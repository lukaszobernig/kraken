module

/-
Modular Concatenation, Forward Labels, Infix Embedding, and Mutual Recursion on AArch64.

Demonstrates:
1. Sequential composition (`Layout.eventually_seq`) and closed subprogram
   embedding (`Eventually.append`, `Eventually.prepend`) on AArch64 `step1`.
2. 3-way concatenation `whole_prog := caller_prog ++ even_prog ++ odd_prog`
   exercising `Layout.subStep_infix` and `Layout.labels_sub_infix`:
   - `caller_prog` performs a non-tail forward `bl even`, resumes at its return
     address to compute `add x0, x0, #10`, and returns via `ret x29`.
   - `even_prog` (an infix snippet!) has an intra-snippet forward `cbz x0, even_zero`
     and a cross-snippet forward `b odd`.
   - `odd_prog` has an intra-snippet forward `cbz x0, odd_zero` and a cross-snippet
     backward `b even`.
   All three snippets are verified completely independently via `SubStep` before
   `whole_prog` is defined, then linked with zero instruction re-stepping.
-/

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
meta import Kraken.AArch64.Semantics
import Kraken.AArch64.Sep
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

/-! ## 2. Independent Verification of `even_prog`, `odd_prog`, and `caller_prog` -/

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

theorem even_step [layout : Layout] {labels : Labels}
    {trans : MachineState → @Post MachineState → Prop}
    (hfit : Kraken.Directives.size (layout even_prog).program < 2 ^ 64)
    (hemb : SubStep (step1 (layout even_prog) labels) trans)
    (hlocal : (layout even_prog).labels ⊆ labels)
    {f_odd : Int64} (hodd : labels.label? "odd" = some f_odd)
    (n : Nat) (s : MachineData) (hx0 : s.regs.X0.toNat = n)
    (hcallee : ∀ n', n = n' + 1 → ∀ s_call : MachineData,
      s_call.regs.X0.toNat = n' →
      s_call.regs.X30 = s.regs.X30 →
      s_call.regs.X29 = s.regs.X29 →
      Eventually trans
        (fun st => st.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
          st.1.regs.X0 = (if decide (n' % 2 = 1) then 1 else 0) ∧
          st.1.regs.X29 = s.regs.X29)
        ⟨s_call, f_odd⟩) :
    Eventually trans
      (fun st => st.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
        st.1.regs.X0 = (if decide (n % 2 = 0) then 1 else 0) ∧
        st.1.regs.X29 = s.regs.X29)
      ⟨s, (layout even_prog).addrOf 0⟩ := by
  cases n with
  | zero =>
    apply hemb.eventually
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
    have h_pre : Eventually (step1 (layout even_prog) labels)
        (fun st => st.pc = f_odd ∧
          st.1.regs.X0.toNat = n' ∧
          st.1.regs.X30 = s.regs.X30 ∧
          st.1.regs.X29 = s.regs.X29)
        ⟨s, (layout even_prog).addrOf 0⟩ := by
      kprologue even_prog with s
      sym => kstep; tactic =>
      have hx0_ne := bv_ne_zero_of_succ hx0
      simp (config := { zetaDelta := true }) [hx0_ne]
      sym => kstep; tactic =>
      apply Eventually.done
      refine ⟨rfl, ?_, rfl, rfl⟩
      have hsub := uint64_sub_one_toNat hx0
      simp (config := { zetaDelta := true }) at hsub ⊢
      exact hsub
    refine Eventually.bind (hemb.eventually h_pre) ?_
    rintro ⟨s_call, pc_call⟩ ⟨rfl, hx0_call, hx30_call, hx29_call⟩
    exact odd_pred_eq_even_succ n' ▸ hcallee n' rfl s_call hx0_call hx30_call hx29_call

def odd_prog : Program := ⸨prog|
odd:
  cbz x0, odd_zero
  sub x0, x0, #1
  b even
odd_zero:
  mov x0, #0
  ret
⸩

theorem odd_step [layout : Layout] {labels : Labels}
    {trans : MachineState → @Post MachineState → Prop}
    (hfit : Kraken.Directives.size (layout odd_prog).program < 2 ^ 64)
    (hemb : SubStep (step1 (layout odd_prog) labels) trans)
    (hlocal : (layout odd_prog).labels ⊆ labels)
    {f_even : Int64} (heven : labels.label? "even" = some f_even)
    (n : Nat) (s : MachineData) (hx0 : s.regs.X0.toNat = n)
    (hcallee : ∀ n', n = n' + 1 → ∀ s_call : MachineData,
      s_call.regs.X0.toNat = n' →
      s_call.regs.X30 = s.regs.X30 →
      s_call.regs.X29 = s.regs.X29 →
      Eventually trans
        (fun st => st.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
          st.1.regs.X0 = (if decide (n' % 2 = 0) then 1 else 0) ∧
          st.1.regs.X29 = s.regs.X29)
        ⟨s_call, f_even⟩) :
    Eventually trans
      (fun st => st.pc = Int64.ofBitVec s.regs.X30.toBitVec ∧
        st.1.regs.X0 = (if decide (n % 2 = 1) then 1 else 0) ∧
        st.1.regs.X29 = s.regs.X29)
      ⟨s, (layout odd_prog).addrOf 0⟩ := by
  cases n with
  | zero =>
    apply hemb.eventually
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
    have h_pre : Eventually (step1 (layout odd_prog) labels)
        (fun st => st.pc = f_even ∧
          st.1.regs.X0.toNat = n' ∧
          st.1.regs.X30 = s.regs.X30 ∧
          st.1.regs.X29 = s.regs.X29)
        ⟨s, (layout odd_prog).addrOf 0⟩ := by
      kprologue odd_prog with s
      sym => kstep; tactic =>
      have hx0_ne := bv_ne_zero_of_succ hx0
      simp (config := { zetaDelta := true }) [hx0_ne]
      sym => kstep; tactic =>
      apply Eventually.done
      refine ⟨rfl, ?_, rfl, rfl⟩
      have hsub := uint64_sub_one_toNat hx0
      simp (config := { zetaDelta := true }) at hsub ⊢
      exact hsub
    refine Eventually.bind (hemb.eventually h_pre) ?_
    rintro ⟨s_call, pc_call⟩ ⟨rfl, hx0_call, hx30_call, hx29_call⟩
    exact even_pred_eq_odd_succ n' ▸ hcallee n' rfl s_call hx0_call hx30_call hx29_call

/-- Non-tail caller snippet: calls `bl even` forward, resumes at `addrOf 2`, adds 10, returns via `x29`. -/
def caller_prog : Program := ⸨prog|
main:
  bl even
  add x0, x0, #10
  ret x29
⸩

theorem caller_step [layout : Layout] {labels : Labels}
    {trans : MachineState → @Post MachineState → Prop}
    (hfit : Kraken.Directives.size (layout caller_prog).program < 2 ^ 64)
    (hemb : SubStep (step1 (layout caller_prog) labels) trans)
    {f_even : Int64} (heven : labels.label? "even" = some f_even)
    (s : MachineData) (res : UInt64)
    (h_even_spec : ∀ s_call : MachineData,
      s_call.regs.X0 = s.regs.X0 →
      s_call.regs.X29 = s.regs.X29 →
      Int64.ofBitVec s_call.regs.X30.toBitVec = (layout caller_prog).addrOf 2 →
      Eventually trans
        (fun st => st.pc = (layout caller_prog).addrOf 2 ∧
          st.1.regs.X0 = res ∧
          st.1.regs.X29 = s.regs.X29)
        ⟨s_call, f_even⟩) :
    Eventually trans
      (fun st => st.pc = Int64.ofBitVec s.regs.X29.toBitVec ∧
        st.1.regs.X0 = res + 10)
      ⟨s, (layout caller_prog).addrOf 0⟩ := by
  have h_call : Eventually (step1 (layout caller_prog) labels)
      (fun st => st.pc = f_even ∧
        st.1.regs.X0 = s.regs.X0 ∧
        st.1.regs.X29 = s.regs.X29 ∧
        Int64.ofBitVec st.1.regs.X30.toBitVec = (layout caller_prog).addrOf 2)
      ⟨s, (layout caller_prog).addrOf 0⟩ := by
    kprologue caller_prog with s
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨rfl, rfl, rfl, ?_⟩
    simp (config := { zetaDelta := true })
  refine Eventually.bind (hemb.eventually h_call) ?_
  rintro ⟨s_mid, pc_mid⟩ ⟨rfl, hx0_mid, hx29_mid, hx30_mid⟩
  refine Eventually.bind (h_even_spec s_mid hx0_mid hx29_mid hx30_mid) ?_
  rintro ⟨s_ret, pc_ret⟩ ⟨rfl, hx0_ret, hx29_ret⟩
  apply hemb.eventually
  kprologue caller_prog with s_ret
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨?_, ?_⟩
  · simp (config := { zetaDelta := true }) [← hx29_ret]
  · subst hx0_ret
    simp (config := { zetaDelta := true }) only [
      show BitVec.ofInt 64 (Int64.toInt 10) = 10#64 from rfl]
    bv_decide

/-! ## 3. 3-Way Linking (`caller_prog ++ even_prog ++ odd_prog`) via `Layout.subStep_infix` -/

def whole_prog : Program := caller_prog ++ even_prog ++ odd_prog

theorem whole_prog_correct [layout : Layout]
    (hfit : Kraken.Directives.size (layout whole_prog).program < 2 ^ 64)
    (s : MachineData) :
    Eventually (step1 (layout whole_prog))
      (fun st => st.pc = Int64.ofBitVec s.regs.X29.toBitVec ∧
        st.1.regs.X0 = (if decide (s.regs.X0.toNat % 2 = 0) then 1 else 0) + 10)
      ⟨s, layout.start⟩ := by
  let L := (layout whole_prog).labels
  have hfit_ce : Kraken.Directives.size (layout (caller_prog ++ even_prog)).program < 2 ^ 64 :=
    layout.size_left_lt hfit
  have hfit_c : Kraken.Directives.size (layout caller_prog).program < 2 ^ 64 :=
    layout.size_left_lt hfit_ce
  have hfit_e : Kraken.Directives.size ((layout.after caller_prog) even_prog).program < 2 ^ 64 :=
    layout.size_after_lt hfit_ce
  have hfit_o : Kraken.Directives.size ((layout.after (caller_prog ++ even_prog)) odd_prog).program < 2 ^ 64 :=
    layout.size_after_lt hfit
  have hL_even : ((layout.after caller_prog) even_prog).labels ⊆ L :=
    layout.labels_sub_infix caller_prog even_prog odd_prog (by decide)
  have hL_odd : ((layout.after (caller_prog ++ even_prog)) odd_prog).labels ⊆ L :=
    layout.labels_sub_append_left (caller_prog ++ even_prog) odd_prog (by decide)
  have hemb_caller : SubStep (step1 (layout caller_prog) L) (step1 (layout whole_prog)) := by
    have hassoc : caller_prog ++ (even_prog ++ odd_prog) = whole_prog :=
      (List.append_assoc caller_prog even_prog odd_prog).symm
    have hfit' : Kraken.Directives.size (layout (caller_prog ++ (even_prog ++ odd_prog))).program < 2 ^ 64 :=
      hassoc ▸ hfit
    have hsub := layout.subStep_append_right (p := caller_prog) (q := even_prog ++ odd_prog)
      (L₁ := L) (L₂ := L) (Kraken.Labels.subset_refl L) hfit'
    exact hassoc ▸ hsub
  have hemb_even : SubStep (step1 ((layout.after caller_prog) even_prog) L)
      (step1 (layout whole_prog)) :=
    layout.subStep_infix (q₁ := caller_prog) (p := even_prog) (q₂ := odd_prog)
      (Kraken.Labels.subset_refl L) hfit
  have hemb_odd : SubStep (step1 ((layout.after (caller_prog ++ even_prog)) odd_prog) L)
      (step1 (layout whole_prog)) :=
    layout.subStep_append_left (q := caller_prog ++ even_prog) (p := odd_prog)
      (Kraken.Labels.subset_refl L) hfit
  have h_even_lbl : L.label? "even" = some (((layout.after caller_prog) even_prog).addrOf 0) :=
    hL_even "even" _ (Kraken.Layout.label?_eq_some_addrOf
      (l := layout.after caller_prog) even_prog "even" rfl)
  have h_odd_lbl : L.label? "odd" =
      some (((layout.after (caller_prog ++ even_prog)) odd_prog).addrOf 0) :=
    hL_odd "odd" _ (Kraken.Layout.label?_eq_some_addrOf
      (l := layout.after (caller_prog ++ even_prog)) odd_prog "odd" rfl)
  -- Link `even` and `odd` by induction on `n`:
  have h_eo : ∀ n : Nat,
      (∀ d : MachineData, d.regs.X0.toNat = n →
        Eventually (step1 (layout whole_prog))
          (fun st => st.pc = Int64.ofBitVec d.regs.X30.toBitVec ∧
            st.1.regs.X0 = (if decide (n % 2 = 0) then 1 else 0) ∧
            st.1.regs.X29 = d.regs.X29)
          ⟨d, ((layout.after caller_prog) even_prog).addrOf 0⟩) ∧
      (∀ d : MachineData, d.regs.X0.toNat = n →
        Eventually (step1 (layout whole_prog))
          (fun st => st.pc = Int64.ofBitVec d.regs.X30.toBitVec ∧
            st.1.regs.X0 = (if decide (n % 2 = 1) then 1 else 0) ∧
            st.1.regs.X29 = d.regs.X29)
          ⟨d, ((layout.after (caller_prog ++ even_prog)) odd_prog).addrOf 0⟩) := by
    intro n
    induction n with
    | zero =>
      exact ⟨fun d hd => even_step (layout := layout.after caller_prog) hfit_e hemb_even hL_even
          h_odd_lbl 0 d hd (by omega),
        fun d hd => odd_step (layout := layout.after (caller_prog ++ even_prog)) hfit_o hemb_odd
          hL_odd h_even_lbl 0 d hd (by omega)⟩
    | succ m ih =>
      refine ⟨fun d hd => even_step (layout := layout.after caller_prog) hfit_e hemb_even hL_even
          h_odd_lbl (m + 1) d hd ?_,
        fun d hd => odd_step (layout := layout.after (caller_prog ++ even_prog)) hfit_o hemb_odd
          hL_odd h_even_lbl (m + 1) d hd ?_⟩
      · rintro n' hn' s_call hx0' hx30' hx29'
        obtain rfl : n' = m := Nat.succ.inj hn'.symm
        simpa [hx30', hx29'] using ih.2 s_call hx0'
      · rintro n' hn' s_call hx0' hx30' hx29'
        obtain rfl : n' = m := Nat.succ.inj hn'.symm
        simpa [hx30', hx29'] using ih.1 s_call hx0'
  -- Link `caller_prog` with `even`:
  have h0 : (layout caller_prog).addrOf 0 = layout.start := Kraken.Executable.addrOf_zero _
  rw [← h0]
  refine caller_step hfit_c hemb_caller h_even_lbl s
    (if decide (s.regs.X0.toNat % 2 = 0) then 1 else 0) ?_
  intro s_call hx0_call hx29_call hx30_call
  have hev := (h_eo s.regs.X0.toNat).1 s_call (by rw [hx0_call])
  simpa [hx30_call, hx29_call] using hev

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
