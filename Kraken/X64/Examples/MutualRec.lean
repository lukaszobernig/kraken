module

/-
Modular Concatenation, Forward Labels, and Mutual Recursion on X64.

Demonstrates:
1. Sequential composition (`Layout.eventually_seq`) and closed subprogram
   embedding (`Eventually.append`, `Eventually.prepend`) on `step1`.
2. Open-snippet verification with intra-snippet forward labels (`hlocal : (layout p).labels ⊆ L`)
   and external forward/backward labels (`L.label? "odd" = some f_odd`).
3. Non-tail-recursive mutual recursion (`even` / `odd` using `call` / `addq $1, %rcx` / `ret`),
   where `even_prog` and `odd_prog` are verified completely independently via `SubStep`
   before `even_odd_prog := even_prog ++ odd_prog` is defined, and linked by induction
   without re-stepping a single instruction.
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
    (hfit : Kraken.Directives.size (layout inc_rax).program < 2 ^ 64) (s : MachineData) :
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
    (hfit : Kraken.Directives.size (layout double_rax).program < 2 ^ 64) (s : MachineData) :
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
    (hfit : Kraken.Directives.size (layout (inc_rax ++ double_rax)).program < 2 ^ 64)
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
    (hfit : Kraken.Directives.size (layout (inc_rax ++ suffix)).program < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout (inc_rax ++ suffix)))
      (fun s' => s'.1.regs.rax = s.regs.rax + 1 ∧
        s'.pc = @Kraken.Layout.start _ _ (layout.after inc_rax))
      ⟨s, layout.start⟩ :=
  Eventually.append inc_rax suffix hfit
    (inc_rax_spec (layout inc_rax).labels (layout.size_left_lt hfit) s)

/-- Closed subprogram `Eventually.prepend`: prefix code with disjoint labels does not disturb `double_rax`. -/
theorem any_prepend_double_rax [layout : Layout] (pref : Program)
    (hfit : Kraken.Directives.size (layout (pref ++ double_rax)).program < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout (pref ++ double_rax)))
      (fun s' => s'.1.regs.rax = s.regs.rax + s.regs.rax ∧
        s'.pc = @Kraken.Layout.start _ _ ((layout.after pref).after double_rax))
      ⟨s, @Kraken.Layout.start _ _ (layout.after pref)⟩ :=
  Eventually.prepend pref double_rax hfit (by simp [Kraken.Program.definedLabels, double_rax])
    (double_rax_spec (layout := layout.after pref)
      ((layout.after pref) double_rax).labels (layout.size_after_lt hfit) s)

/-! ## 2. Modular Non-Tail Mutual Recursion (`even` / `odd`) -/

/-- `frames.length` 8-byte stack slots immediately below `sp`, framed around `R`. -/
def StackBelow : List (List UInt8) → BitVec 64 → (DataMem → Prop) → DataMem → Prop
  | [], _, R => R
  | bs :: rest, sp, R => Eq (bs.At (sp - 8#64)) ⋆ StackBelow rest (sp - 8#64) R

theorem StackBelow_push_inner (P : DataMem → Prop) :
    ∀ (frames : List (List UInt8)) (sp : BitVec 64) (R : DataMem → Prop),
      (P ⋆ StackBelow frames sp R) = StackBelow frames sp (P ⋆ R)
  | [], _, _ => rfl
  | bs :: rest, sp, R => by
    dsimp only [StackBelow]
    rw [← StackBelow_push_inner P rest (sp - 8#64) R]
    ac_rfl

/-- `even(n)` in X64:
- Intra-snippet forward jump `jz even_zero`
- Cross-snippet forward call `call odd`
- Non-tail post-call continuation `addq $1, %rcx; ret` at `(layout even_prog).addrOf 5`,
  accumulating recursion depth in `%rcx` while `%rax` returns `1` iff `n` is even. -/
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

/-- Postcondition for calling `even` or `odd`:
- returns to `retAddr`
- `%rax = res` (`1` or `0`)
- `%rcx = UInt64.ofNat n` (accumulated after each non-tail `call` returns)
- `%rsp = sp + 8` and all stack slots preserved as 8-byte frames. -/
def CallPost (n : Nat) (sp : UInt64) (retAddr : Int64) (res : UInt64)
    (R : DataMem → Prop) (st : MachineState) : Prop :=
  st.pc = retAddr ∧
  st.1.regs.rax = res ∧
  st.1.regs.rcx = UInt64.ofNat n ∧
  st.1.regs.rsp = sp + 8 ∧
  ∃ frames' : List (List UInt8),
    frames'.length = n ∧
    (∀ b ∈ frames', b.length = 8) ∧
    (st.1.dmem =⋆ StackBelow frames' sp.toBitVec
      (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp.toBitVec) ⋆ R))

private theorem ret_addr_roundtrip (a : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 a.toBitVec.toInt))) = a := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

private theorem sub_add_8 (sp : UInt64) : (sp - 8) + 8 = sp := by bv_decide
private theorem bv_sub_8_eq (sp : UInt64) : (sp - 8).toBitVec = sp.toBitVec - 8#64 := by bv_decide
private theorem uint64_ofNat_succ (m : Nat) : UInt64.ofNat m + 1 = UInt64.ofNat (m + 1) := by
  simp [UInt64.ofNat_add]
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

/-- Modular single-layer verification of `even_prog`, proved **without** `odd_prog` in scope!
Works in any ambient transition `trans` satisfying `SubStep (step1 (layout even_prog) labels) trans`. -/
theorem even_step [layout : Layout] {labels : Labels}
    {trans : MachineState → @Post MachineState → Prop}
    (hfit : Kraken.Directives.size (layout even_prog).program < 2 ^ 64)
    (hemb : SubStep (step1 (layout even_prog) labels) trans)
    (hlocal : (layout even_prog).labels ⊆ labels)
    {f_odd : Int64} (hodd : labels.label? "odd" = some f_odd)
    (n : Nat) (s : MachineData) (retAddr : Int64)
    (frames : List (List UInt8)) (R : DataMem → Prop)
    (hrdi : s.regs.rdi.toNat = n)
    (hlen : frames.length = n)
    (hbytes : ∀ b ∈ frames, b.length = 8)
    (hmem : s.dmem =⋆ StackBelow frames s.regs.rsp.toBitVec
      (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R))
    (hcallee : ∀ n', n = n' + 1 → ∀ (s_call : MachineData) (frames' : List (List UInt8)) (R' : DataMem → Prop),
      s_call.regs.rdi.toNat = n' →
      frames'.length = n' →
      (∀ b ∈ frames', b.length = 8) →
      (s_call.dmem =⋆ StackBelow frames' s_call.regs.rsp.toBitVec
        (Eq ((Int.toBytes 8 ((layout even_prog).addrOf 5).toBitVec.toInt).At s_call.regs.rsp.toBitVec) ⋆ R')) →
      Eventually trans
        (CallPost n' s_call.regs.rsp ((layout even_prog).addrOf 5) (if decide (n' % 2 = 1) then 1 else 0) R')
        ⟨s_call, f_odd⟩) :
    Eventually trans
      (CallPost n s.regs.rsp retAddr (if decide (n % 2 = 0) then 1 else 0) R)
      ⟨s, (layout even_prog).addrOf 0⟩ := by
  cases n with
  | zero =>
    have hframes : frames = [] := List.eq_nil_of_length_eq_zero hlen
    subst hframes
    apply hemb.eventually
    dsimp only [StackBelow] at hmem
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := Int.toBytes_length 8 _
    kprologue even_prog with s
    sym => kstep; tactic =>
    have hrdi0 : rdi = 0 := uint64_zero_of_toNat hrdi
    subst hrdi0
    simp (config := { zetaDelta := true })
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨ret_addr_roundtrip retAddr, rfl, rfl, rfl, [], rfl, nofun, hmem⟩
  | succ n' =>
    obtain ⟨bs, rest, rfl⟩ : ∃ bs rest, frames = bs :: rest := by
      cases frames with | nil => simp at hlen | cons bs rest => exact ⟨bs, rest, rfl⟩
    have hbs : bs.length = 8 := hbytes bs List.mem_cons_self
    have hrest_len : rest.length = n' := Nat.succ.inj hlen
    have hrest_bytes : ∀ b ∈ rest, b.length = 8 := fun b hb => hbytes b (List.mem_cons_of_mem _ hb)
    let sp0 := s.regs.rsp
    -- Phase 1: step inside `even_prog` from entry up to `call odd`, jumping to `f_odd`.
    have h_pre : Eventually (step1 (layout even_prog) labels)
        (fun st => st.pc = f_odd ∧
          st.1.regs.rdi.toNat = n' ∧
          st.1.regs.rsp = sp0 - 8 ∧
          (st.1.dmem =⋆ StackBelow rest (sp0 - 8).toBitVec
            (Eq ((Int.toBytes 8 ((layout even_prog).addrOf 5).toBitVec.toInt).At (sp0 - 8).toBitVec) ⋆
              (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp0.toBitVec) ⋆ R))))
        ⟨s, (layout even_prog).addrOf 0⟩ := by
      dsimp only [StackBelow] at hmem
      kprologue even_prog with s
      dsimp only at hmem sp0
      have h_store := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 bs
        (StackBelow rest (rsp.toBitVec - 8#64)
          (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At rsp.toBitVec) ⋆ R))
        mem ⟨hmem, hbs⟩ ((layout even_prog).addrOf 5).toBitVec.toInt
      sym => kstep; tactic =>
      have hrdi_ne := bv_ne_zero_of_succ hrdi
      simp (config := { zetaDelta := true }) [hrdi_ne]
      sym => kstep; tactic =>
      apply Eventually.done
      refine ⟨rfl, ?_, rfl, ?_⟩
      · have hsub := uint64_sub_one_toNat hrdi
        simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl] at hsub ⊢
        exact hsub
      · dsimp (config := { zetaDelta := true }) only
        rw [← StackBelow_push_inner]
        exact h_store
    -- Phase 2: lift Phase 1 via `SubStep`, bind with `hcallee` at `f_odd`, then resume at `addrOf 5`!
    refine Eventually.bind (hemb.eventually h_pre) ?_
    rintro ⟨s_call, pc_call⟩ ⟨rfl, hrdi_call, hrsp_call, hmem_call⟩
    refine Eventually.bind
      (hcallee n' rfl s_call rest (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp0.toBitVec) ⋆ R)
        hrdi_call hrest_len hrest_bytes (hrsp_call ▸ hmem_call)) ?_
    rintro ⟨s_ret, pc_ret⟩ ⟨rfl, hrax_ret, hrcx_ret, hrsp_ret, frames_out, hlen_out, hbytes_out, hmem_ret⟩
    -- Phase 3: resume inside `even_prog` at `addrOf 5` (`addq $1, %rcx; ret`) and lift via `SubStep`!
    apply hemb.eventually
    have hrsp_eq : s_ret.regs.rsp = sp0 := by
      rw [hrsp_ret, hrsp_call, sub_add_8]
    let ra5 := Int.toBytes 8 ((layout even_prog).addrOf 5).toBitVec.toInt
    have hmem_final : s_ret.dmem =⋆ StackBelow (ra5 :: frames_out) sp0.toBitVec
        (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp0.toBitVec) ⋆ R) := by
      dsimp only [StackBelow]
      rw [← bv_sub_8_eq sp0, StackBelow_push_inner]
      rw [hrsp_call] at hmem_ret
      exact hmem_ret
    have hmem_for_ret : s_ret.dmem =⋆
        Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s_ret.regs.rsp.toBitVec) ⋆
          StackBelow (ra5 :: frames_out) sp0.toBitVec R := by
      rw [hrsp_eq, StackBelow_push_inner]
      exact cast (congrFun (by ac_rfl) _) hmem_final
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := Int.toBytes_length 8 _
    kprologue even_prog with s_ret
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨ret_addr_roundtrip retAddr, ?_, ?_, ?_, ra5 :: frames_out, by simp [hlen_out], ?_, hmem_final⟩
    · simpa [odd_pred_eq_even_succ n'] using hrax_ret
    · rw [← uint64_ofNat_succ n', ← hrcx_ret]
      simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl]
      bv_decide
    · exact congrArg (· + 8) hrsp_eq
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Int.toBytes_length 8 _
      · exact hbytes_out b hb'

/-- `odd(n)` in X64: defined after `even_prog`, calling backward to `even` and jumping forward to `odd_zero`. -/
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
theorem odd_step [layout : Layout] {labels : Labels}
    {trans : MachineState → @Post MachineState → Prop}
    (hfit : Kraken.Directives.size (layout odd_prog).program < 2 ^ 64)
    (hemb : SubStep (step1 (layout odd_prog) labels) trans)
    (hlocal : (layout odd_prog).labels ⊆ labels)
    {f_even : Int64} (heven : labels.label? "even" = some f_even)
    (n : Nat) (s : MachineData) (retAddr : Int64)
    (frames : List (List UInt8)) (R : DataMem → Prop)
    (hrdi : s.regs.rdi.toNat = n)
    (hlen : frames.length = n)
    (hbytes : ∀ b ∈ frames, b.length = 8)
    (hmem : s.dmem =⋆ StackBelow frames s.regs.rsp.toBitVec
      (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R))
    (hcallee : ∀ n', n = n' + 1 → ∀ (s_call : MachineData) (frames' : List (List UInt8)) (R' : DataMem → Prop),
      s_call.regs.rdi.toNat = n' →
      frames'.length = n' →
      (∀ b ∈ frames', b.length = 8) →
      (s_call.dmem =⋆ StackBelow frames' s_call.regs.rsp.toBitVec
        (Eq ((Int.toBytes 8 ((layout odd_prog).addrOf 5).toBitVec.toInt).At s_call.regs.rsp.toBitVec) ⋆ R')) →
      Eventually trans
        (CallPost n' s_call.regs.rsp ((layout odd_prog).addrOf 5) (if decide (n' % 2 = 0) then 1 else 0) R')
        ⟨s_call, f_even⟩) :
    Eventually trans
      (CallPost n s.regs.rsp retAddr (if decide (n % 2 = 1) then 1 else 0) R)
      ⟨s, (layout odd_prog).addrOf 0⟩ := by
  cases n with
  | zero =>
    have hframes : frames = [] := List.eq_nil_of_length_eq_zero hlen
    subst hframes
    apply hemb.eventually
    dsimp only [StackBelow] at hmem
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := Int.toBytes_length 8 _
    kprologue odd_prog with s
    sym => kstep; tactic =>
    have hrdi0 : rdi = 0 := uint64_zero_of_toNat hrdi
    subst hrdi0
    simp (config := { zetaDelta := true })
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨ret_addr_roundtrip retAddr, rfl, rfl, rfl, [], rfl, nofun, hmem⟩
  | succ n' =>
    obtain ⟨bs, rest, rfl⟩ : ∃ bs rest, frames = bs :: rest := by
      cases frames with | nil => simp at hlen | cons bs rest => exact ⟨bs, rest, rfl⟩
    have hbs : bs.length = 8 := hbytes bs List.mem_cons_self
    have hrest_len : rest.length = n' := Nat.succ.inj hlen
    have hrest_bytes : ∀ b ∈ rest, b.length = 8 := fun b hb => hbytes b (List.mem_cons_of_mem _ hb)
    let sp0 := s.regs.rsp
    have h_pre : Eventually (step1 (layout odd_prog) labels)
        (fun st => st.pc = f_even ∧
          st.1.regs.rdi.toNat = n' ∧
          st.1.regs.rsp = sp0 - 8 ∧
          (st.1.dmem =⋆ StackBelow rest (sp0 - 8).toBitVec
            (Eq ((Int.toBytes 8 ((layout odd_prog).addrOf 5).toBitVec.toInt).At (sp0 - 8).toBitVec) ⋆
              (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp0.toBitVec) ⋆ R))))
        ⟨s, (layout odd_prog).addrOf 0⟩ := by
      dsimp only [StackBelow] at hmem
      kprologue odd_prog with s
      dsimp only at hmem sp0
      have h_store := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 bs
        (StackBelow rest (rsp.toBitVec - 8#64)
          (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At rsp.toBitVec) ⋆ R))
        mem ⟨hmem, hbs⟩ ((layout odd_prog).addrOf 5).toBitVec.toInt
      sym => kstep; tactic =>
      have hrdi_ne := bv_ne_zero_of_succ hrdi
      simp (config := { zetaDelta := true }) [hrdi_ne]
      sym => kstep; tactic =>
      apply Eventually.done
      refine ⟨rfl, ?_, rfl, ?_⟩
      · have hsub := uint64_sub_one_toNat hrdi
        simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl] at hsub ⊢
        exact hsub
      · dsimp (config := { zetaDelta := true }) only
        rw [← StackBelow_push_inner]
        exact h_store
    refine Eventually.bind (hemb.eventually h_pre) ?_
    rintro ⟨s_call, pc_call⟩ ⟨rfl, hrdi_call, hrsp_call, hmem_call⟩
    refine Eventually.bind
      (hcallee n' rfl s_call rest (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp0.toBitVec) ⋆ R)
        hrdi_call hrest_len hrest_bytes (hrsp_call ▸ hmem_call)) ?_
    rintro ⟨s_ret, pc_ret⟩ ⟨rfl, hrax_ret, hrcx_ret, hrsp_ret, frames_out, hlen_out, hbytes_out, hmem_ret⟩
    apply hemb.eventually
    have hrsp_eq : s_ret.regs.rsp = sp0 := by
      rw [hrsp_ret, hrsp_call, sub_add_8]
    let ra5 := Int.toBytes 8 ((layout odd_prog).addrOf 5).toBitVec.toInt
    have hmem_final : s_ret.dmem =⋆ StackBelow (ra5 :: frames_out) sp0.toBitVec
        (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At sp0.toBitVec) ⋆ R) := by
      dsimp only [StackBelow]
      rw [← bv_sub_8_eq sp0, StackBelow_push_inner]
      rw [hrsp_call] at hmem_ret
      exact hmem_ret
    have hmem_for_ret : s_ret.dmem =⋆
        Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s_ret.regs.rsp.toBitVec) ⋆
          StackBelow (ra5 :: frames_out) sp0.toBitVec R := by
      rw [hrsp_eq, StackBelow_push_inner]
      exact cast (congrFun (by ac_rfl) _) hmem_final
    have h_ret_len : (Int.toBytes 8 retAddr.toBitVec.toInt).length = 8 := Int.toBytes_length 8 _
    kprologue odd_prog with s_ret
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨ret_addr_roundtrip retAddr, ?_, ?_, ?_, ra5 :: frames_out, by simp [hlen_out], ?_, hmem_final⟩
    · simpa [even_pred_eq_odd_succ n'] using hrax_ret
    · rw [← uint64_ofNat_succ n', ← hrcx_ret]
      simp (config := { zetaDelta := true }) [show (OfNat.ofNat 1 : UInt64) = 1 from rfl]
      bv_decide
    · exact congrArg (· + 8) hrsp_eq
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact Int.toBytes_length 8 _
      · exact hbytes_out b hb'

/-! ## 3. Linking `even_prog ++ odd_prog` with Zero Re-Stepping -/

def even_odd_prog : Program := even_prog ++ odd_prog

/-- Simultaneous linking theorem for `even_odd_prog := even_prog ++ odd_prog`:
proved purely from `even_step`, `odd_step`, `Layout.subStep_append_right`,
`Layout.subStep_append_left`, and `Layout.labels_sub_append_*` — no instruction stepping! -/
theorem even_odd_linked [layout : Layout]
    (hfit : Kraken.Directives.size (layout even_odd_prog).program < 2 ^ 64) :
    ∀ n : Nat,
      (∀ (s : MachineData) (retAddr : Int64) (frames : List (List UInt8)) (R : DataMem → Prop),
        s.regs.rdi.toNat = n →
        frames.length = n →
        (∀ b ∈ frames, b.length = 8) →
        (s.dmem =⋆ StackBelow frames s.regs.rsp.toBitVec
          (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R)) →
        Eventually (step1 (layout even_odd_prog))
          (CallPost n s.regs.rsp retAddr (if decide (n % 2 = 0) then 1 else 0) R)
          ⟨s, (layout even_prog).addrOf 0⟩) ∧
      (∀ (s : MachineData) (retAddr : Int64) (frames : List (List UInt8)) (R : DataMem → Prop),
        s.regs.rdi.toNat = n →
        frames.length = n →
        (∀ b ∈ frames, b.length = 8) →
        (s.dmem =⋆ StackBelow frames s.regs.rsp.toBitVec
          (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R)) →
        Eventually (step1 (layout even_odd_prog))
          (CallPost n s.regs.rsp retAddr (if decide (n % 2 = 1) then 1 else 0) R)
          ⟨s, ((layout.after even_prog) odd_prog).addrOf 0⟩) := by
  have hdisj : ∀ l ∈ even_prog.definedLabels, l ∉ odd_prog.definedLabels := by
    decide
  have hL_even : (layout even_prog).labels ⊆ (layout even_odd_prog).labels :=
    layout.labels_sub_append_right even_prog odd_prog
  have hL_odd : ((layout.after even_prog) odd_prog).labels ⊆ (layout even_odd_prog).labels :=
    layout.labels_sub_append_left even_prog odd_prog hdisj
  have hemb_even : SubStep (step1 (layout even_prog) (layout even_odd_prog).labels)
      (step1 (layout even_odd_prog)) :=
    layout.subStep_append_right (Kraken.Labels.subset_refl _) hfit
  have hemb_odd : SubStep (step1 ((layout.after even_prog) odd_prog) (layout even_odd_prog).labels)
      (step1 (layout even_odd_prog)) :=
    layout.subStep_append_left (Kraken.Labels.subset_refl _) hfit
  have h_even_lbl : (layout even_odd_prog).labels.label? "even" = some ((layout even_prog).addrOf 0) :=
    hL_even "even" _ (Kraken.Layout.label?_eq_some_addrOf even_prog "even" rfl)
  have h_odd_lbl : (layout even_odd_prog).labels.label? "odd" =
      some (((layout.after even_prog) odd_prog).addrOf 0) :=
    hL_odd "odd" _ (Kraken.Layout.label?_eq_some_addrOf (l := layout.after even_prog) odd_prog "odd" rfl)
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro s retAddr frames R hrdi hlen hbytes hmem
      exact even_step (layout.size_left_lt hfit) hemb_even hL_even h_odd_lbl
        0 s retAddr frames R hrdi hlen hbytes hmem (by omega)
    · intro s retAddr frames R hrdi hlen hbytes hmem
      exact odd_step (layout := layout.after even_prog) (layout.size_after_lt hfit) hemb_odd hL_odd h_even_lbl
        0 s retAddr frames R hrdi hlen hbytes hmem (by omega)
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · intro s retAddr frames R hrdi hlen hbytes hmem
      refine even_step (layout.size_left_lt hfit) hemb_even hL_even h_odd_lbl
        (m + 1) s retAddr frames R hrdi hlen hbytes hmem ?_
      rintro n' hn' s_call frames' R' hrdi' hlen' hbytes' hmem'
      obtain rfl : n' = m := Nat.succ.inj hn'.symm
      exact ih.2 s_call ((layout even_prog).addrOf 5) frames' R' hrdi' hlen' hbytes' hmem'
    · intro s retAddr frames R hrdi hlen hbytes hmem
      refine odd_step (layout := layout.after even_prog) (layout.size_after_lt hfit) hemb_odd hL_odd h_even_lbl
        (m + 1) s retAddr frames R hrdi hlen hbytes hmem ?_
      rintro n' hn' s_call frames' R' hrdi' hlen' hbytes' hmem'
      obtain rfl : n' = m := Nat.succ.inj hn'.symm
      exact ih.1 s_call (((layout.after even_prog) odd_prog).addrOf 5) frames' R' hrdi' hlen' hbytes' hmem'

/-- Top-level closed specification for `even` on `even_odd_prog` starting from `layout.start`. -/
theorem even_correct [layout : Layout]
    (hfit : Kraken.Directives.size (layout even_odd_prog).program < 2 ^ 64)
    (s : MachineData) (retAddr : Int64) (frames : List (List UInt8)) (R : DataMem → Prop)
    (hlen : frames.length = s.regs.rdi.toNat)
    (hbytes : ∀ b ∈ frames, b.length = 8)
    (hmem : s.dmem =⋆ StackBelow frames s.regs.rsp.toBitVec
      (Eq ((Int.toBytes 8 retAddr.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R)) :
    Eventually (step1 (layout even_odd_prog))
      (CallPost s.regs.rdi.toNat s.regs.rsp retAddr
        (if decide (s.regs.rdi.toNat % 2 = 0) then 1 else 0) R)
      ⟨s, layout.start⟩ := by
  have h0 : (layout even_prog).addrOf 0 = layout.start := Kraken.Executable.addrOf_zero _
  rw [← h0]
  exact (even_odd_linked hfit s.regs.rdi.toNat).1 s retAddr frames R rfl hlen hbytes hmem

-- Concrete `#eval` sanity check for `even(0..5)` returning `(rax = is_even, rcx = depth)`.
/-- info: [Except.ok (1, 0), Except.ok (0, 1), Except.ok (1, 2), Except.ok (0, 3), Except.ok (1, 4), Except.ok (0, 5)] -/
#guard_msgs in
#eval
  let exe := even_odd_prog.fakeLayout
  let entry := exe.labels.label! "even"
  [0, 1, 2, 3, 4, 5].map fun (n : UInt64) =>
    let dmem0 := [1, 2, 3, 4, 5, 6, 7, 8].foldl
      (fun m (i : Nat) => Mem.storeInt m (0x1000#64 - BitVec.ofNat 64 (8 * i)) 8 0)
      (Mem.storeInt {} 0x1000 8 0x1337)
    let data : MachineData := { dmem := dmem0, regs := { rdi := n, rsp := 0x1000 } }
    (Executable.eval exe { data, pc := entry } (fun st => st.pc = 0x1337)).bind
      (fun st => .ok (st.1.regs.rax, st.1.regs.rcx))

end MutualRecX64
