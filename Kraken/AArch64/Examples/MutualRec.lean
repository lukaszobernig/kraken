module

/-
Modular Concatenation, Forward Labels, Infix Embedding, and `bedrock2`-Style `SpecOf` on AArch64.

Demonstrates:
1. Sequential composition (`Layout.eventually_seq`) and closed subprogram
   embedding (`Eventually.append`, `Eventually.prepend`) on AArch64 `step1`.
2. `bedrock2`-style function specifications as standalone definitions (`SpecOf "even"`,
   `SpecOf "odd"`, `SpecOf "main"`), written over `e : Executable` **before** any
   function implementation (`even_prog`, `odd_prog`, `caller_prog`) is defined.
3. In-place modular verification (`Embedded`, `step_at_sub`) directly in `Eventually (step1 e)`
   without intermediate pre-call state predicates:
   - `even_ok` (intra-snippet forward `cbz x0, even_zero` + cross-snippet forward `b odd`)
   - `odd_ok` (intra-snippet forward `cbz x0, odd_zero` + cross-snippet backward `b even`)
   - `caller_ok` (non-tail forward `bl even`, resuming at return address for `add x0, x0, #10; ret x29`)
4. 3-way linking (`whole_prog := caller_prog ++ even_prog ++ odd_prog`) via `Embedded.of_infix`
   and `FnSpec.forall_nat` with zero instruction re-stepping.
-/

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
meta import Kraken.AArch64.Semantics
import Kraken.AArch64.Sep
import Kraken.AArch64.Spec
import Kraken.Eval
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide

namespace MutualRecAArch64

open Kraken.AArch64
open Kraken.AArch64.Parser

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

def inc_x0 : Program := ⸨prog|
  add x0, x0, #1
⸩

def double_x0 : Program := ⸨prog|
  add x0, x0, x0
⸩

theorem inc_x0_spec [layout : Layout] (labels : Labels)
    (hfit : Kraken.Directives.size (layout inc_x0).program < 2 ^ 64) (s : MachineData) :
    Eventually (step1 (layout inc_x0) labels)
      (fun s' => s'.1.regs.X0 = s.regs.X0 + 1 ∧
        s'.pc = @Kraken.Layout.start _ _ (layout.after inc_x0))
      ⟨s, layout.start⟩ := by
  kprologue inc_x0 with s
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨?_, layout.addrOf_length inc_x0⟩
  simp (config := { zetaDelta := true }) only [
    show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
  bv_decide

theorem double_x0_spec [layout : Layout] (labels : Labels)
    (hfit : Kraken.Directives.size (layout double_x0).program < 2 ^ 64) (s : MachineData) :
    Eventually (step1 (layout double_x0) labels)
      (fun s' => s'.1.regs.X0 = s.regs.X0 + s.regs.X0 ∧
        s'.pc = @Kraken.Layout.start _ _ (layout.after double_x0))
      ⟨s, layout.start⟩ := by
  kprologue double_x0 with s
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨?_, layout.addrOf_length double_x0⟩
  simp (config := { zetaDelta := true }) only [
    show (Int64.toInt 0).toNat = 0 from rfl]
  bv_decide

theorem inc_then_double_x0_spec [layout : Layout] (labels : Labels)
    (hfit : Kraken.Directives.size (layout (inc_x0 ++ double_x0)).program < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout (inc_x0 ++ double_x0)) labels)
      (fun s' => s'.1.regs.X0 = (s.regs.X0 + 1) + (s.regs.X0 + 1))
      ⟨s, layout.start⟩ := by
  refine layout.eventually_seq hfit
    (inc_x0_spec labels (layout.size_left_lt hfit) s) ?_
  rintro ⟨s₁, pc₁⟩ ⟨hx0, rfl⟩
  exact eventually_weaken _ _ _ _
    (fun s₂ h => hx0 ▸ h.1)
    (double_x0_spec (layout := layout.after inc_x0) labels (layout.size_after_lt hfit) s₁)

/-! ## 2. `bedrock2`-Style Function Specifications as Definitions (`SpecOf`)

Defined purely over `e : Executable` before any implementation snippet is introduced. -/

def EvenContract (e : Executable) (entry : Int64) (n : Nat) : Prop :=
  ∀ s : MachineData,
    s.regs.X0.toNat = n →
    CallBLAt e entry s fun s' =>
      s'.regs.X0 = (if decide (n % 2 = 0) then 1 else 0) ∧
      s'.regs.X29 = s.regs.X29

def OddContract (e : Executable) (entry : Int64) (n : Nat) : Prop :=
  ∀ s : MachineData,
    s.regs.X0.toNat = n →
    CallBLAt e entry s fun s' =>
      s'.regs.X0 = (if decide (n % 2 = 1) then 1 else 0) ∧
      s'.regs.X29 = s.regs.X29

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
      WPCallAt e entry s fun st =>
        st.pc = Int64.ofBitVec s.regs.X29.toBitVec ∧
        st.1.regs.X0 = (if decide (s.regs.X0.toNat % 2 = 0) then 1 else 0) + 10

/-! ## 3. Independent Verification of `even_prog`, `odd_prog`, and `caller_prog` -/

private theorem uint64_zero_of_toNat {u : UInt64} (h : u.toNat = 0) : u = 0 := by grind
private theorem bv_ne_zero_of_succ {u : UInt64} {m : Nat} (h : u.toNat = m + 1) :
    u.toBitVec ≠ 0#64 := fun h0 => by
  have : u.toNat = 0 := congrArg BitVec.toNat h0
  omega
private theorem uint64_sub_one_toNat {u : UInt64} {m : Nat} (h : u.toNat = m + 1) :
    (u - 1).toNat = m := by grind
private theorem odd_pred_eq_even_succ (m : Nat) :
    decide (m % 2 = 1) = decide ((m + 1) % 2 = 0) := by
  simp only [decide_eq_decide]; omega
private theorem even_pred_eq_odd_succ (m : Nat) :
    decide (m % 2 = 0) = decide ((m + 1) % 2 = 1) := by
  simp only [decide_eq_decide]; omega

def even_prog : Program := ⸨prog|
even:
  cbz x0, even_zero
  sub x0, x0, #1
  b odd
even_zero:
  mov x0, #1
  ret
⸩

theorem even_ok (e : Executable) (hemb : Embedded even_prog e)
    (n : Nat) (h_odd : ∀ m < n, spec_of_odd_at m e) :
    spec_of_even_at n e := by
  refine hemb.fnSpec_of_label (k := 0) rfl fun hfit hlocal hsub => fun s hx0 => ?_
  cases n with
  | zero =>
    kprologue even_prog with s
    sym => kstep; tactic =>
    have hx0_zero : X0 = 0 := uint64_zero_of_toNat hx0
    subst hx0_zero
    simp (config := { zetaDelta := true })
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨by simp (config := { zetaDelta := true }), ?_, rfl⟩
    simp (config := { zetaDelta := true }) only [
      show BitVec.ofInt 64 (Int64.toInt 1) = 1#64 from rfl]
    decide
  | succ n' =>
    obtain ⟨f_odd, hodd, h_odd_call⟩ := h_odd n' (Nat.lt_succ_self n')
    kprologue even_prog with s
    sym => kstep; tactic =>
    have hx0_ne := bv_ne_zero_of_succ hx0
    simp (config := { zetaDelta := true }) [hx0_ne]
    sym => kstep; tactic =>
    refine eventually_weaken _ _ _ _ ?_ (h_odd_call _ ?_)
    · rintro st ⟨hpc, hx0_out, hx29_out⟩
      exact ⟨hpc, by simpa [odd_pred_eq_even_succ n'] using hx0_out, hx29_out⟩
    · have hsub_x0 := uint64_sub_one_toNat hx0
      simp (config := { zetaDelta := true }) at hsub_x0 ⊢
      exact hsub_x0

def odd_prog : Program := ⸨prog|
odd:
  cbz x0, odd_zero
  sub x0, x0, #1
  b even
odd_zero:
  mov x0, #0
  ret
⸩

theorem odd_ok (e : Executable) (hemb : Embedded odd_prog e)
    (n : Nat) (h_even : ∀ m < n, spec_of_even_at m e) :
    spec_of_odd_at n e := by
  refine hemb.fnSpec_of_label (k := 0) rfl fun hfit hlocal hsub => fun s hx0 => ?_
  cases n with
  | zero =>
    kprologue odd_prog with s
    sym => kstep; tactic =>
    have hx0_zero : X0 = 0 := uint64_zero_of_toNat hx0
    subst hx0_zero
    simp (config := { zetaDelta := true })
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨by simp (config := { zetaDelta := true }), ?_, rfl⟩
    simp (config := { zetaDelta := true }) only [
      show BitVec.ofInt 64 (Int64.toInt 0) = 0#64 from rfl]
    decide
  | succ n' =>
    obtain ⟨f_even, heven, h_even_call⟩ := h_even n' (Nat.lt_succ_self n')
    kprologue odd_prog with s
    sym => kstep; tactic =>
    have hx0_ne := bv_ne_zero_of_succ hx0
    simp (config := { zetaDelta := true }) [hx0_ne]
    sym => kstep; tactic =>
    refine eventually_weaken _ _ _ _ ?_ (h_even_call _ ?_)
    · rintro st ⟨hpc, hx0_out, hx29_out⟩
      exact ⟨hpc, by simpa [even_pred_eq_odd_succ n'] using hx0_out, hx29_out⟩
    · have hsub_x0 := uint64_sub_one_toNat hx0
      simp (config := { zetaDelta := true }) at hsub_x0 ⊢
      exact hsub_x0

/-- Non-tail caller snippet: calls `bl even` forward, resumes at `addrOf 2`, adds 10, returns via `x29`. -/
def caller_prog : Program := ⸨prog|
main:
  bl even
  add x0, x0, #10
  ret x29
⸩

theorem caller_ok (e : Executable) (hemb : Embedded caller_prog e)
    (h_even : spec_of_even e) :
    spec_of_main e := by
  obtain ⟨f_even, heven, h_even_call⟩ := h_even
  refine hemb.fnSpec_of_label (k := 0) rfl fun hfit hlocal hsub => fun s => ?_
  cases s with | mk regs status dmem =>
  cases regs
  sym => kstep; tactic =>
  refine Eventually.bind (h_even_call _ _ rfl) ?_
  rintro ⟨⟨regs_ret, status_ret, dmem_ret⟩, pc_ret⟩ ⟨h_pc, hx0_ret, hx29_ret⟩
  dsimp only at h_pc hx0_ret hx29_ret
  simp (config := { zetaDelta := true }) at h_pc
  subst h_pc
  cases regs_ret
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨?_, ?_⟩
  · dsimp only at hx29_ret ⊢
    simp (config := { zetaDelta := true }) [← hx29_ret]
  · dsimp only at hx0_ret ⊢
    subst hx0_ret
    simp (config := { zetaDelta := true }) only [
      show BitVec.ofInt 64 (Int64.toInt 10) = 10#64 from rfl]
    bv_decide

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

def whole_prog : Program := caller_prog ++ even_prog ++ odd_prog

/-- Closed specification of `whole_prog` expressed directly as `spec_of_main (layout whole_prog)`. -/
theorem whole_prog_ok [layout : Layout]
    (hfit : Kraken.Directives.size (layout whole_prog).program < 2 ^ 64) :
    spec_of_main (layout whole_prog) := by
  have hemb_caller : Embedded caller_prog (layout whole_prog) :=
    Embedded.append_right layout (caller_prog ++ even_prog) odd_prog hfit
      (Embedded.of_append_right layout caller_prog even_prog (layout.size_left_lt hfit))
  have hemb_even : Embedded even_prog (layout whole_prog) :=
    Embedded.of_infix layout caller_prog even_prog odd_prog (by decide) hfit
  have hemb_odd : Embedded odd_prog (layout whole_prog) :=
    Embedded.of_append_left layout (caller_prog ++ even_prog) odd_prog (by decide) hfit
  exact caller_ok (layout whole_prog) hemb_caller
    (even_odd_ok (layout whole_prog) hemb_even hemb_odd).1

/-- Execution from `layout.start` obtained immediately via `FnSpec.at_label`. -/
theorem whole_prog_correct [layout : Layout]
    (hfit : Kraken.Directives.size (layout whole_prog).program < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout whole_prog))
      (fun st => st.pc = Int64.ofBitVec s.regs.X29.toBitVec ∧
        st.1.regs.X0 = (if decide (s.regs.X0.toNat % 2 = 0) then 1 else 0) + 10)
      ⟨s, layout.start⟩ := by
  have h0 : (layout whole_prog).addrOf 0 = layout.start := (layout whole_prog).addrOf_zero
  rw [← h0]
  exact (whole_prog_ok hfit).at_label (k := 0) rfl s

-- Concrete `#eval` sanity check for `whole_prog` (`11` for even, `10` for odd).
/-- info: [Except.ok 11, Except.ok 10, Except.ok 11, Except.ok 10, Except.ok 11, Except.ok 10] -/
#guard_msgs in
#eval
  let exe := whole_prog.fakeLayout
  let entry := exe.labels.label! "main"
  [0, 1, 2, 3, 4, 5].map fun (n : UInt64) =>
    let data : MachineData := { regs := { X0 := n, X29 := 0x1337 } }
    (Executable.eval exe { data, pc := entry } (fun st => st.pc = 0x1337)).bind
      (fun st => .ok st.1.regs.X0)

end MutualRecAArch64
