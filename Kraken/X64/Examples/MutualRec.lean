module

/-
Modular Concatenation, Forward Labels, Split-Label Layout, Dynamic `.p2align`,
Mutual Recursion, and `bedrock2`-Style `SpecOf` on X64.

Demonstrates:
1. Sequential composition (`Layout.eventually_seq`) and closed subprogram
   embedding (`Eventually.append`, `Eventually.prepend`) on `step1`.
2. `bedrock2`-style function specifications as standalone definitions (`SpecOf "even"`,
   `SpecOf "odd"`, `SpecOf "main"`) built on `CallX64At` / `RetSlot` / `StackBelow`,
   written purely over `e : Executable` **before** any implementation snippet is defined.
3. In-place modular verification (`Embedded`, `step_at_sub`) directly inside `Eventually (step1 e)`
   with label-free body indexing (`Program.stripLabels` / `Program.extractLabels`) and positive-size `Executable.program`.
4. Linking (`even_odd_ok`, `whole_prog_ok`, `whole_prog_correct`) with zero instruction re-stepping.
5. Dynamic `.p2align 4` fall-through stepping with zero user-visible `0` vs `> 0` case splitting,
   plus an unconditional 16-byte alignment guarantee for the target label even after concatenation.
-/

import Kraken.Eval
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics
import Kraken.X64.Sep
import Kraken.X64.Spec

namespace MutualRecX64

open Kraken.X64.Parser
open Std Std.ExtHashMap

set_option maxHeartbeats 1000000

attribute [ksimp]
  BitVec.add_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq
  Int.add_zero
  Int64.toInt_neg
  Nat.shiftRight_zero
  Nat.sub_zero
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

/-! ## 1. Sequential Composition & Subprogram Embedding -/

def inc_rax : Program := ⸨prog|
  addq $1, %rax
⸩

def double_rax : Program := ⸨prog|
  addq %rax, %rax
⸩

theorem inc_rax_spec [layout : Layout] (labels : Labels)
    (hfit : layout.totalSize inc_rax < 2 ^ 64) (s : MachineData) :
    Eventually (step1 (layout inc_rax) labels)
      (fun s' => s'.1.regs.rax = s.regs.rax + 1 ∧
        s'.pc = @Kraken.Layout.start _ _ (layout.after inc_rax))
      ⟨s, layout.start⟩ := by
  kprologue inc_rax with s
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨?_, layout.addrOf_length inc_rax⟩
  simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl]
  bv_decide

theorem double_rax_spec [layout : Layout] (labels : Labels)
    (hfit : layout.totalSize double_rax < 2 ^ 64) (s : MachineData) :
    Eventually (step1 (layout double_rax) labels)
      (fun s' => s'.1.regs.rax = s.regs.rax + s.regs.rax ∧
        s'.pc = @Kraken.Layout.start _ _ (layout.after double_rax))
      ⟨s, layout.start⟩ := by
  kprologue double_rax with s
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨?_, layout.addrOf_length double_rax⟩
  simp (config := { zetaDelta := true })

/-- Composing `inc_rax` and `double_rax` via `Layout.eventually_seq` without re-stepping. -/
theorem inc_then_double_spec [layout : Layout] (labels : Labels)
    (hfit : layout.totalSize (inc_rax ++ double_rax) < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout (inc_rax ++ double_rax)) labels)
      (fun s' => s'.1.regs.rax = (s.regs.rax + 1) + (s.regs.rax + 1))
      ⟨s, layout.start⟩ := by
  refine layout.eventually_seq hfit
    (inc_rax_spec labels (layout.size_left_lt hfit) s) ?_
  rintro ⟨s₁, pc₁⟩ ⟨hrax₁, rfl⟩
  exact eventually_weaken _ _ _ _
    (fun s₂ h => hrax₁ ▸ h.1)
    (double_rax_spec (layout := layout.after inc_rax) labels (layout.size_after_lt hfit) s₁)

/-- Closed subprogram `Eventually.append`: suffix code does not disturb `inc_rax`. -/
theorem inc_rax_append_any [layout : Layout] (suffix : Program)
    (hfit : layout.totalSize (inc_rax ++ suffix) < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout (inc_rax ++ suffix)))
      (fun s' => s'.1.regs.rax = s.regs.rax + 1 ∧
        s'.pc = @Kraken.Layout.start _ _ (layout.after inc_rax))
      ⟨s, layout.start⟩ :=
  Eventually.append inc_rax suffix hfit
    (inc_rax_spec (layout inc_rax).labels (layout.size_left_lt hfit) s)

/-- Closed subprogram `Eventually.prepend`: prefix code with disjoint labels does not disturb `double_rax`. -/
theorem any_prepend_double_rax [layout : Layout] (pref : Program)
    (hfit : layout.totalSize (pref ++ double_rax) < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout (pref ++ double_rax)))
      (fun s' => s'.1.regs.rax = s.regs.rax + s.regs.rax ∧
        s'.pc = @Kraken.Layout.start _ _ ((layout.after pref).after double_rax))
      ⟨s, @Kraken.Layout.start _ _ (layout.after pref)⟩ :=
  Eventually.prepend pref double_rax hfit (by simp [Kraken.Program.definedLabels, double_rax])
    (double_rax_spec (layout := layout.after pref)
      ((layout.after pref) double_rax).labels (layout.size_after_lt hfit) s)

/-! ## 2. `bedrock2`-Style Function Specifications as Definitions (`SpecOf`)

Defined purely over `e : Executable` before any implementation snippet is introduced. -/

/-- Common stack-framed X64 `call`/`ret` contract using `depth` 8-byte scratch stack slots
below `%rsp` and returning `%rax = res`, `%rcx = rcxOut`. -/
def StackCallContract (depth : Nat) (res rcxOut : UInt64)
    (e : Executable) (entry : Int64) (s : MachineData) : Prop :=
  ∀ frames : List (List UInt8),
    frames.length = depth →
    (∀ b ∈ frames, b.length = 8) →
    CallX64At e entry s
      (fun frame dmem => dmem =⋆ StackBelow frames s.regs.rsp.toBitVec frame)
      (fun s' frame =>
        s'.regs.rax = res ∧
        s'.regs.rcx = rcxOut ∧
        ∃ frames' : List (List UInt8),
          frames'.length = depth ∧
          (∀ b ∈ frames', b.length = 8) ∧
          (s'.dmem =⋆ StackBelow frames' s.regs.rsp.toBitVec frame))

def EvenContract (e : Executable) (entry : Int64) (n : Nat) : Prop :=
  ∀ s : MachineData,
    s.regs.rdi.toNat = n →
    StackCallContract n (if decide (n % 2 = 0) then 1 else 0) (UInt64.ofNat n) e entry s

def OddContract (e : Executable) (entry : Int64) (n : Nat) : Prop :=
  ∀ s : MachineData,
    s.regs.rdi.toNat = n →
    StackCallContract n (if decide (n % 2 = 1) then 1 else 0) (UInt64.ofNat n) e entry s

def spec_of_even_at (n : Nat) (e : Executable) : Prop :=
  FnSpec e "even" fun entry => EvenContract e entry n

def spec_of_odd_at (n : Nat) (e : Executable) : Prop :=
  FnSpec e "odd" fun entry => OddContract e entry n

instance spec_of_even : SpecOf "even" where
  spec e := FnSpec e "even" fun entry => ∀ n, EvenContract e entry n

instance spec_of_odd : SpecOf "odd" where
  spec e := FnSpec e "odd" fun entry => ∀ n, OddContract e entry n

instance spec_of_main : SpecOf "main" where
  spec e := FnSpec e "main" fun entry =>
    ∀ s : MachineData,
      StackCallContract (s.regs.rdi.toNat + 1)
        ((if decide (s.regs.rdi.toNat % 2 = 0) then 1 else 0) + 10)
        (UInt64.ofNat s.regs.rdi.toNat) e entry s

/-! ## 3. Independent In-Place Verification of `even_prog`, `odd_prog`, and `caller_prog` -/

private theorem sub_add_8 (sp : UInt64) : (sp - 8) + 8 = sp := by bv_decide
private theorem odd_pred_eq_even_succ (m : Nat) :
    decide (m % 2 = 1) = decide ((m + 1) % 2 = 0) := by
  simp only [decide_eq_decide]; omega
private theorem even_pred_eq_odd_succ (m : Nat) :
    decide (m % 2 = 0) = decide ((m + 1) % 2 = 1) := by
  simp only [decide_eq_decide]; omega
private theorem uint64_zero_of_toNat {u : UInt64} (h : u.toNat = 0) : u = 0 := by grind
private theorem bv_ne_zero_of_succ {u : UInt64} {m : Nat} (h : u.toNat = m + 1) :
    u.toBitVec ≠ 0#64 := fun h0 => by
  have : u.toNat = 0 := congrArg BitVec.toNat h0
  omega
private theorem uint64_sub_one_toNat {u : UInt64} {m : Nat} (h : u.toNat = m + 1) :
    (u - 1).toNat = m := by grind

/-- `even(n)` in X64:
- Intra-snippet forward jump `jz even_zero`
- Cross-snippet forward call `call odd`
- Non-tail post-call continuation `addq $1, %rcx; ret` at body index `4` (`layout.addrOf even_prog 4`). -/
def even_prog : Program := ⸨prog|
even:
  subq $0, %rdi
  jz even_zero
  subq $1, %rdi
  call odd
  addq $1, %rcx
  ret
even_zero:
  movq $1, %rax
  movq $0, %rcx
  ret
⸩

/-- Modular single-layer verification of `even_prog`, proved **without** `odd_prog` in scope,
stepping directly in `Eventually (step1 e)` via `step_at_sub` with no intermediate `h_pre` cut! -/
theorem even_ok (e : Executable) (hemb : Embedded even_prog e)
    (n : Nat) (h_odd : ∀ m < n, spec_of_odd_at m e) :
    spec_of_even_at n e := by
  refine hemb.fnSpec_of_label (k := 0) rfl ?_
  intro layout hfit hlocal hsub s hrdi frames hlen hbytes retAddr R hmem
  cases n with
  | zero =>
    have hframes : frames = [] := List.eq_nil_of_length_eq_zero hlen
    subst hframes
    dsimp only [StackBelow, RetSlot] at hmem
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := RetSlot.bytes_length retAddr
    kprologue even_prog with s
    sym => kstep; tactic =>
    have hrdi0 : rdi = 0 := uint64_zero_of_toNat hrdi
    subst hrdi0
    simp (config := { zetaDelta := true })
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨RetSlot.addr_roundtrip retAddr, rfl, rfl, rfl, hmem⟩
  | succ n' =>
    obtain ⟨f_odd, hodd, h_odd_call⟩ := h_odd n' (Nat.lt_succ_self n')
    obtain ⟨bs, rest, rfl⟩ : ∃ bs rest, frames = bs :: rest := by
      cases frames with | nil => simp at hlen | cons bs rest => exact ⟨bs, rest, rfl⟩
    have hbs : bs.length = 8 := hbytes bs List.mem_cons_self
    have hrest_len : rest.length = n' := Nat.succ.inj hlen
    have hrest_bytes : ∀ b ∈ rest, b.length = 8 := fun b hb => hbytes b (List.mem_cons_of_mem _ hb)
    dsimp only [StackBelow, RetSlot] at hmem
    kprologue even_prog with s
    dsimp only at hmem hrdi
    have h_store := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 bs
      (StackBelow rest (rsp.toBitVec - 8#64)
        (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At rsp.toBitVec) ⋆ R))
      mem ⟨hmem, hbs⟩ (layout.addrOf even_prog 4).toBitVec.toInt
    sym => kstep; tactic =>
    have hrdi_ne := bv_ne_zero_of_succ hrdi
    simp (config := { zetaDelta := true }) [hrdi_ne]
    sym => kstep; tactic =>
    refine Eventually.bind
      (h_odd_call _ ?_ rest hrest_len hrest_bytes (layout.addrOf even_prog 4)
        (RetSlot retAddr rsp ⋆ R) ?_) ?_
    · have hsub_rdi := uint64_sub_one_toNat hrdi
      simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl] at hsub_rdi ⊢
      exact hsub_rdi
    · dsimp (config := { zetaDelta := true }) only [RetSlot]
      rw [← StackBelow_push_inner]
      exact h_store
    · rintro ⟨s_ret, pc_ret⟩ ⟨rfl, hrsp_ret, hrax_ret, hrcx_ret, frames_out, hlen_out, hbytes_out, hmem_ret⟩
      dsimp (config := { zetaDelta := true }) only at hrsp_ret hmem_ret
      have hrsp_eq : s_ret.regs.rsp = rsp := by
        have h8 : UInt64.ofBitVec (rsp.toBitVec - 8#64) = rsp - 8 := by bv_decide
        rw [hrsp_ret, h8, sub_add_8]
      let ra4 := Int.toBytes 8 (layout.addrOf even_prog 4).toBitVec.toInt
      have hmem_final : s_ret.dmem =⋆ StackBelow (ra4 :: frames_out) rsp.toBitVec
          (RetSlot retAddr rsp ⋆ R) := by
        dsimp only [StackBelow, RetSlot] at hmem_ret ⊢
        rw [StackBelow_push_inner]
        exact hmem_ret
      have hmem_for_ret : s_ret.dmem =⋆
          Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s_ret.regs.rsp.toBitVec) ⋆
            StackBelow (ra4 :: frames_out) rsp.toBitVec R := by
        dsimp only [RetSlot] at hmem_final
        rw [hrsp_eq, StackBelow_push_inner]
        exact cast (congrFun (by ac_rfl) _) hmem_final
      have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := RetSlot.bytes_length retAddr
      cases s_ret
      cases ‹Reg64s›
      sym => kstep; tactic =>
      apply Eventually.done
      refine ⟨RetSlot.addr_roundtrip retAddr, ?_, ?_, ?_, ra4 :: frames_out, by simp [hlen_out], ?_, hmem_final⟩
      · exact congrArg (· + 8) hrsp_eq
      · simpa [odd_pred_eq_even_succ n'] using hrax_ret
      · dsimp only at hrcx_ret ⊢
        rw [← hrcx_ret]
        simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl]
        bv_decide
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact Int.toBytes_length 8 _
        · exact hbytes_out b hb'

/-- `odd(n)` in X64: calls `even` and jumps forward to `odd_zero`. -/
def odd_prog : Program := ⸨prog|
odd:
  subq $0, %rdi
  jz odd_zero
  subq $1, %rdi
  call even
  addq $1, %rcx
  ret
odd_zero:
  movq $0, %rax
  movq $0, %rcx
  ret
⸩

/-- Modular single-layer verification of `odd_prog`, proved **without** `even_prog` in scope! -/
theorem odd_ok (e : Executable) (hemb : Embedded odd_prog e)
    (n : Nat) (h_even : ∀ m < n, spec_of_even_at m e) :
    spec_of_odd_at n e := by
  refine hemb.fnSpec_of_label (k := 0) rfl ?_
  intro layout hfit hlocal hsub s hrdi frames hlen hbytes retAddr R hmem
  cases n with
  | zero =>
    have hframes : frames = [] := List.eq_nil_of_length_eq_zero hlen
    subst hframes
    dsimp only [StackBelow, RetSlot] at hmem
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := RetSlot.bytes_length retAddr
    kprologue odd_prog with s
    sym => kstep; tactic =>
    have hrdi0 : rdi = 0 := uint64_zero_of_toNat hrdi
    subst hrdi0
    simp (config := { zetaDelta := true })
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨RetSlot.addr_roundtrip retAddr, rfl, rfl, rfl, hmem⟩
  | succ n' =>
    obtain ⟨f_even, heven, h_even_call⟩ := h_even n' (Nat.lt_succ_self n')
    obtain ⟨bs, rest, rfl⟩ : ∃ bs rest, frames = bs :: rest := by
      cases frames with | nil => simp at hlen | cons bs rest => exact ⟨bs, rest, rfl⟩
    have hbs : bs.length = 8 := hbytes bs List.mem_cons_self
    have hrest_len : rest.length = n' := Nat.succ.inj hlen
    have hrest_bytes : ∀ b ∈ rest, b.length = 8 := fun b hb => hbytes b (List.mem_cons_of_mem _ hb)
    dsimp only [StackBelow, RetSlot] at hmem
    kprologue odd_prog with s
    dsimp only at hmem hrdi
    have h_store := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 bs
      (StackBelow rest (rsp.toBitVec - 8#64)
        (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At rsp.toBitVec) ⋆ R))
      mem ⟨hmem, hbs⟩ (layout.addrOf odd_prog 4).toBitVec.toInt
    sym => kstep; tactic =>
    have hrdi_ne := bv_ne_zero_of_succ hrdi
    simp (config := { zetaDelta := true }) [hrdi_ne]
    sym => kstep; tactic =>
    refine Eventually.bind
      (h_even_call _ ?_ rest hrest_len hrest_bytes (layout.addrOf odd_prog 4)
        (RetSlot retAddr rsp ⋆ R) ?_) ?_
    · have hsub_rdi := uint64_sub_one_toNat hrdi
      simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl] at hsub_rdi ⊢
      exact hsub_rdi
    · dsimp (config := { zetaDelta := true }) only [RetSlot]
      rw [← StackBelow_push_inner]
      exact h_store
    · rintro ⟨s_ret, pc_ret⟩ ⟨rfl, hrsp_ret, hrax_ret, hrcx_ret, frames_out, hlen_out, hbytes_out, hmem_ret⟩
      dsimp (config := { zetaDelta := true }) only at hrsp_ret hmem_ret
      have hrsp_eq : s_ret.regs.rsp = rsp := by
        have h8 : UInt64.ofBitVec (rsp.toBitVec - 8#64) = rsp - 8 := by bv_decide
        rw [hrsp_ret, h8, sub_add_8]
      let ra4 := Int.toBytes 8 (layout.addrOf odd_prog 4).toBitVec.toInt
      have hmem_final : s_ret.dmem =⋆ StackBelow (ra4 :: frames_out) rsp.toBitVec
          (RetSlot retAddr rsp ⋆ R) := by
        dsimp only [StackBelow, RetSlot] at hmem_ret ⊢
        rw [StackBelow_push_inner]
        exact hmem_ret
      have hmem_for_ret : s_ret.dmem =⋆
          Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s_ret.regs.rsp.toBitVec) ⋆
            StackBelow (ra4 :: frames_out) rsp.toBitVec R := by
        dsimp only [RetSlot] at hmem_final
        rw [hrsp_eq, StackBelow_push_inner]
        exact cast (congrFun (by ac_rfl) _) hmem_final
      have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := RetSlot.bytes_length retAddr
      cases s_ret
      cases ‹Reg64s›
      sym => kstep; tactic =>
      apply Eventually.done
      refine ⟨RetSlot.addr_roundtrip retAddr, ?_, ?_, ?_, ra4 :: frames_out, by simp [hlen_out], ?_, hmem_final⟩
      · exact congrArg (· + 8) hrsp_eq
      · simpa [even_pred_eq_odd_succ n'] using hrax_ret
      · dsimp only at hrcx_ret ⊢
        rw [← hrcx_ret]
        simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl]
        bv_decide
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact Int.toBytes_length 8 _
        · exact hbytes_out b hb'

/-- Non-recursive caller snippet: calls `even` forward, resumes at body index `1`, adds 10, returns. -/
def caller_prog : Program := ⸨prog|
main:
  call even
  addq $10, %rax
  ret
⸩

/-- Verified solely against `(h_even : spec_of_even e)` — `even_prog` and `odd_prog` are never inspected! -/
theorem caller_ok (e : Executable) (hemb : Embedded caller_prog e)
    (h_even : spec_of_even e) :
    spec_of_main e := by
  obtain ⟨f_even, heven, h_even_call⟩ := h_even
  refine hemb.fnSpec_of_label (k := 0) rfl ?_
  intro layout hfit hlocal hsub s frames hlen hbytes retAddr R hmem
  obtain ⟨bs, rest, rfl⟩ : ∃ bs rest, frames = bs :: rest := by
    cases frames with | nil => simp at hlen | cons bs rest => exact ⟨bs, rest, rfl⟩
  have hbs : bs.length = 8 := hbytes bs List.mem_cons_self
  have hrest_len : rest.length = s.regs.rdi.toNat := Nat.succ.inj hlen
  have hrest_bytes : ∀ b ∈ rest, b.length = 8 := fun b hb => hbytes b (List.mem_cons_of_mem _ hb)
  dsimp only [StackBelow, RetSlot] at hmem
  kprologue caller_prog with s
  dsimp only at hmem hrest_len
  have h_store := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 bs
    (StackBelow rest (rsp.toBitVec - 8#64)
      (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At rsp.toBitVec) ⋆ R))
    mem ⟨hmem, hbs⟩ (layout.addrOf caller_prog 1).toBitVec.toInt
  sym => kstep; tactic =>
  refine Eventually.bind
    (h_even_call rdi.toNat _ rfl rest hrest_len hrest_bytes (layout.addrOf caller_prog 1)
      (RetSlot retAddr rsp ⋆ R) ?_) ?_
  · dsimp (config := { zetaDelta := true }) only [RetSlot]
    rw [← StackBelow_push_inner]
    exact h_store
  · rintro ⟨s_ret, pc_ret⟩ ⟨rfl, hrsp_ret, hrax_ret, hrcx_ret, frames_out, hlen_out, hbytes_out, hmem_ret⟩
    dsimp (config := { zetaDelta := true }) only at hrsp_ret hmem_ret
    have hrsp_eq : s_ret.regs.rsp = rsp := by
      have h8 : UInt64.ofBitVec (rsp.toBitVec - 8#64) = rsp - 8 := by bv_decide
      rw [hrsp_ret, h8, sub_add_8]
    let ra1 := Int.toBytes 8 (layout.addrOf caller_prog 1).toBitVec.toInt
    have hmem_final : s_ret.dmem =⋆ StackBelow (ra1 :: frames_out) rsp.toBitVec
        (RetSlot retAddr rsp ⋆ R) := by
      dsimp only [StackBelow, RetSlot] at hmem_ret ⊢
      rw [StackBelow_push_inner]
      exact hmem_ret
    have hmem_for_ret : s_ret.dmem =⋆
        Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s_ret.regs.rsp.toBitVec) ⋆
          StackBelow (ra1 :: frames_out) rsp.toBitVec R := by
      dsimp only [RetSlot] at hmem_final
      rw [hrsp_eq, StackBelow_push_inner]
      exact cast (congrFun (by ac_rfl) _) hmem_final
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := RetSlot.bytes_length retAddr
    cases s_ret
    cases ‹Reg64s›
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨RetSlot.addr_roundtrip retAddr, ?_, ?_, hrcx_ret, ra1 :: frames_out, by simp [hlen_out], ?_, hmem_final⟩
    · exact congrArg (· + 8) hrsp_eq
    · simp (config := { zetaDelta := true }) at hrax_ret ⊢
      rw [← hrax_ret]
      exact UInt64.eq_of_toBitVec_eq (by simp; bv_decide)
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Int.toBytes_length 8 _
      · exact hbytes_out b hb'

/-! ## 4. Linking via `Embedded` & `FnSpec.forall_nat` (Zero Re-Stepping) -/

/-- Link `even` and `odd` in any executable `e` containing both snippets. -/
theorem even_odd_ok (e : Executable)
    (hemb_even : Embedded even_prog e)
    (hemb_odd : Embedded odd_prog e) :
    spec_of_even e ∧ spec_of_odd e := by
  have h_at : ∀ n, spec_of_even_at n e ∧ spec_of_odd_at n e := fun n =>
    Nat.strongRecOn n fun n ih =>
      ⟨even_ok e hemb_even n fun m hm => (ih m hm).2,
       odd_ok e hemb_odd n fun m hm => (ih m hm).1⟩
  exact ⟨Kraken.FnSpec.forall_nat fun n => (h_at n).1,
         Kraken.FnSpec.forall_nat fun n => (h_at n).2⟩

def even_odd_prog : Program := even_prog ++ odd_prog

/-- Closed `spec_of_even` & `spec_of_odd` on `even_odd_prog`. -/
theorem even_odd_prog_ok [layout : Layout]
    (hfit : layout.totalSize even_odd_prog < 2 ^ 64) :
    spec_of_even (layout even_odd_prog) ∧ spec_of_odd (layout even_odd_prog) :=
  even_odd_ok (layout even_odd_prog)
    (Embedded.of_append_right layout even_prog odd_prog hfit)
    (Embedded.of_append_left layout even_prog odd_prog (by decide) hfit)

def whole_prog : Program := caller_prog ++ even_odd_prog

/-- 3-module closed `spec_of_main` on `whole_prog := caller_prog ++ (even_prog ++ odd_prog)`. -/
theorem whole_prog_ok [layout : Layout]
    (hfit : layout.totalSize whole_prog < 2 ^ 64) :
    spec_of_main (layout whole_prog) := by
  have hfit_eo := layout.size_after_lt hfit
  have hemb_caller : Embedded caller_prog (layout whole_prog) :=
    Embedded.of_append_right layout caller_prog even_odd_prog hfit
  have hemb_even : Embedded even_prog (layout whole_prog) :=
    Embedded.append_left layout caller_prog even_odd_prog (by decide) hfit
      (Embedded.of_append_right (layout.after caller_prog) even_prog odd_prog hfit_eo)
  have hemb_odd : Embedded odd_prog (layout whole_prog) :=
    Embedded.append_left layout caller_prog even_odd_prog (by decide) hfit
      (Embedded.of_append_left (layout.after caller_prog) even_prog odd_prog (by decide) hfit_eo)
  exact caller_ok (layout whole_prog) hemb_caller
    (even_odd_ok (layout whole_prog) hemb_even hemb_odd).1

/-- Execution from `layout.start` obtained immediately via `FnSpec.at_label`. -/
theorem whole_prog_correct [layout : Layout]
    (hfit : layout.totalSize whole_prog < 2 ^ 64)
    (s : MachineData) :
    StackCallContract (s.regs.rdi.toNat + 1)
      ((if decide (s.regs.rdi.toNat % 2 = 0) then 1 else 0) + 10)
      (UInt64.ofNat s.regs.rdi.toNat) (layout whole_prog) layout.start s := by
  have h0 : layout.addrOf whole_prog 0 = layout.start := layout.addrOf_zero whole_prog
  rw [← h0]
  exact (whole_prog_ok hfit).at_label (k := 0) rfl s

/-! ## 5. Dynamic `.p2align 4` Fall-Through & Alignment Guarantee -/

def aligned_prog : Program := ⸨prog|
aligned_entry:
  addq $1, %rax
  .p2align 4
aligned_target:
  addq %rax, %rax
  ret
⸩

instance spec_of_aligned : SpecOf "aligned_entry" where
  spec e := FnSpec e "aligned_entry" fun entry =>
    ∀ s : MachineData,
      CallX64At e entry s
        (fun frame dmem => dmem =⋆ frame)
        (fun s' frame =>
          s'.regs.rax = (s.regs.rax + 1) + (s.regs.rax + 1) ∧
          s'.dmem =⋆ frame)

/-- `kstep` steps straight through dynamic `.p2align 4` with zero `0` vs `> 0` case splitting! -/
theorem aligned_ok (e : Executable) (hemb : Embedded aligned_prog e) :
    spec_of_aligned e := by
  refine hemb.fnSpec_of_label (k := 0) rfl ?_
  intro layout hfit hlocal hsub s retAddr R hmem
  dsimp only [RetSlot] at hmem
  have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := RetSlot.bytes_length retAddr
  kprologue aligned_prog with s
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨RetSlot.addr_roundtrip retAddr, rfl, ?_, hmem⟩
  simp (config := { zetaDelta := true }) only [Nat.shiftRight_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide

/-- `"aligned_target"` is unconditionally 16-byte aligned in any executable embedding `aligned_prog`
(including after prepending an arbitrary prefix snippet with arbitrary instruction sizes). -/
theorem aligned_target_aligned (e : Executable) (hemb : Embedded aligned_prog e) :
    ∃ addr, e.labels.label? "aligned_target" = some addr ∧ addr.toUInt64.toNat % 16 = 0 := by
  rcases hemb with ⟨layout, _, hlocal, _⟩
  refine ⟨layout.addrOf aligned_prog 2,
    hlocal "aligned_target" _ (Kraken.Layout.label?_eq_some_addrOf aligned_prog "aligned_target" rfl),
    layout.addrOf_align aligned_prog (k := 1) (log2Align := 4) (ex := true) rfl (by omega)⟩

-- Concrete `#eval` sanity check for `whole_prog` (`main(0..5)` returning `(rax = is_even + 10, rcx = depth)`).
/-- info: [Except.ok (11, 0), Except.ok (10, 1), Except.ok (11, 2), Except.ok (10, 3), Except.ok (11, 4), Except.ok (10, 5)] -/
#guard_msgs in
#eval
  let exe := whole_prog.fakeLayout
  let entry := exe.labels.label! "main"
  [0, 1, 2, 3, 4, 5].map fun (n : UInt64) =>
    let dmem0 := [1, 2, 3, 4, 5, 6, 7, 8].foldl
      (fun m (i : Nat) => Mem.storeInt m (0x1000#64 - BitVec.ofNat 64 (8 * i)) 8 0)
      (Mem.storeInt {} 0x1000 8 0x1337)
    let data : MachineData := { dmem := dmem0, regs := { rdi := n, rsp := 0x1000 } }
    (Executable.eval exe { data, pc := entry } (fun st => st.pc = 0x1337)).bind
      (fun st => .ok (st.1.regs.rax, st.1.regs.rcx))

-- Concrete `#eval` sanity check for `inc_rax ++ aligned_prog`: returns `(5 + 1) * 2 = 12` and 16-byte aligned target.
/-- info: (Except.ok 12, true) -/
#guard_msgs in
#eval
  let exe := (inc_rax ++ aligned_prog).fakeLayout
  let entry := exe.labels.label! "aligned_entry"
  let target := exe.labels.label! "aligned_target"
  let data : MachineData := { dmem := Mem.storeInt {} 0x1000 8 0x1337, regs := { rax := 5, rsp := 0x1000 } }
  let res := (Executable.eval exe { data, pc := entry } (fun st => st.pc = 0x1337)).bind
    (fun st => .ok st.1.regs.rax)
  (res, target.toUInt64.toNat % 16 == 0)

end MutualRecX64
