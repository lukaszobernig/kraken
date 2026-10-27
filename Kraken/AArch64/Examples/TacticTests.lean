module

/-
Regression tests for the composition and frame tactics (`kcall`, `kloop`, `kloop_exit`,
`kloop_next`, `kframe`, `kframe_eqs`, `≡ … except`) on AArch64 examples.
-/

import all Kraken.AArch64.Examples.P256Beeu
import Kraken.Tactics

open Kraken Kraken.AArch64
open Kraken.AArch64.Parser


-- (`kloop`/`kloop_exit`/`kloop_next` on a plain loop: see `memcpy_correct` in Memcpy.lean; on a
-- constant-time loop: `memcmp_ct_correct` in Memcmp.lean.)

-- A block lemma with a frame ("modifies") clause instead of per-register equalities.
theorem loop_exit_frame [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre := s₀.regs.beeuB = 0)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        st.data.regs ≡ s₀.regs except [X14, X15] ∧
        st.data.dmem = s₀.dmem) := by
  intro h_B_zero
  have ⟨h25, h26, h27, h28⟩ := val256_eq_zero_limbs
    s₀.regs.X25 s₀.regs.X26 s₀.regs.X27 s₀.regs.X28 h_B_zero
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_A_Y" with s₀
  sym => kstep; tactic =>
  kfinish beeu_mod_inverse_vartime

-- Consumer: composing two frames and using frame equations for derived facts.
example [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime] (s : MachineData)
    (hB : s.regs.beeuB = 0) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        st.data.regs ≡ s.regs except [X14, X15, X13] ∧
        st.data.regs.beeuA = s.regs.beeuA) := by
  intro _
  kcall loop_exit_frame s hB with st1 ⟨h1_fr, h1_mem⟩
  kframe_eqs h1_fr [Reg64s.beeuA]   -- field equations `h1_fr_X21 …` and `h1_fr_beeuA`
  apply Eventually.done
  refine ⟨rfl, ?_, ?_⟩
  · kframe
  · exact h1_fr_beeuA


/-! ### `kstep` normal form of instruction residues

`extr`/`ubfm`(`lsr #k`) leave `if`s over ground conditions, unfolded shift amounts (`64 - 1`) and
`setWidth`/`extractLsb'` wrappers in their results. `kstep` now decides the conditions, folds the
arithmetic and applies the `lsr #k` rule when the value is introduced, so the register values are
`X1.toBitVec <<< 63 ||| X2.toBitVec >>> 1` and `X3.toBitVec >>> 5` and the post can be stated
against them directly, with no bridging lemmas. -/

def extr_lsr : Program := parseAArch64("
  extr x0, x1, x2, #1
  lsr  x4, x3, #5
  ubfx x5, x3, #8, #16
")

theorem extr_lsr_correct [layout : Layout] [Layout.Valid extr_lsr] (s₀ : MachineData) :
    (layout extr_lsr).Spec s₀
      (post := fun st =>
        st.data.regs.X0.toBitVec = s₀.regs.X1.toBitVec <<< 63 ||| s₀.regs.X2.toBitVec >>> 1 ∧
        st.data.regs.X4.toBitVec = s₀.regs.X3.toBitVec >>> 5 ∧
        st.data.regs.X5.toBitVec =
          BitVec.setWidth 64 (BitVec.extractLsb' 0 16 (s₀.regs.X3.toBitVec >>> 8)) ∧
        st.data.regs ≡ s₀.regs except [X0, X4, X5]) := by
  kprologue extr_lsr with s₀
  sym => kstep; tactic =>
  kfinish extr_lsr

/-! ### Flags as an abstraction boundary

`subs`/`cmp` leave `status := StatusFlags.subs a b` in the state; the branch condition `b.lo` is
decided from a value-level hypothesis (`X0.toNat < X1.toNat`) through the `@[kcond]` projection
`(subs a b).c = decide (b.toNat ≤ a.toNat)`, and the post can talk about the flags by name. -/

def cmp_branch : Program := parseAArch64("
  subs x2, x0, x1
  b.lo less
  mov x3, #1
  b done
less:
  mov x3, #0
done:
  nop
")

theorem cmp_branch_correct [layout : Layout] [Layout.Valid cmp_branch] (s₀ : MachineData) :
    (layout cmp_branch).Spec s₀
      (post := fun st =>
        st.data.regs.X3.toNat = (if s₀.regs.X0.toNat < s₀.regs.X1.toNat then 0 else 1) ∧
        st.data.status = StatusFlags.subs s₀.regs.X0.toBitVec s₀.regs.X1.toBitVec ∧
        st.data.regs ≡ s₀.regs except [X2, X3]) := by
  kprologue cmp_branch with s₀
  by_cases h : X0.toNat < X1.toNat
  · sym => kstep; tactic =>          -- `b.lo` taken: decided from `h` through `subs_c`
    kprologue cmp_branch at "less"
    sym => kstep; tactic =>
    kfinish cmp_branch
  · sym => kstep; tactic =>          -- not taken
    kprologue cmp_branch at "done"
    sym => kstep; tactic =>
    kfinish cmp_branch

/-! ### `block_spec`: the same statements without the boilerplate -/

-- `loop_exit_frame` restated: entry label, exit label, written registers, extra post.
block_spec loop_exit_frame' beeu_mod_inverse_vartime s₀
  from ".Lbeeu_loop" to ".Lbeeu_loop_end"
  (writes := [X14, X15])
  (pre := s₀.regs.beeuB = 0)
  (post := fun st => st.data.dmem = s₀.dmem) := by
  intro h_B_zero
  have ⟨h25, h26, h27, h28⟩ := val256_eq_zero_limbs
    s₀.regs.X25 s₀.regs.X26 s₀.regs.X27 s₀.regs.X28 h_B_zero
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_A_Y" with s₀
  sym => kstep; tactic =>
  kfinish beeu_mod_inverse_vartime

-- The generated statement is the hand-written one.
example : @loop_exit_frame' = @loop_exit_frame := rfl

-- A whole-program block (no `from`), with extra binders and no pc conjunct.
block_spec extr_lsr_correct' extr_lsr s₀ (n : Nat) (hn : n = 5)
  (writes := [X0, X4, X5])
  (post := fun st =>
    st.data.regs.X0.toBitVec = s₀.regs.X1.toBitVec <<< 63 ||| s₀.regs.X2.toBitVec >>> 1 ∧
    st.data.regs.X4.toBitVec = s₀.regs.X3.toBitVec >>> n) := by
  subst hn
  kprologue extr_lsr with s₀
  sym => kstep; tactic =>
  kfinish extr_lsr

-- A consumer composes a `block_spec` lemma with `kcall` as usual.
example [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime] (s : MachineData)
    (hB : s.regs.beeuB = 0) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        st.data.regs.X21 = s.regs.X21) := by
  intro _
  kcall loop_exit_frame' s hB with st1 ⟨h1_fr, h1_mem⟩
  kframe_eqs h1_fr
  apply Eventually.done
  exact ⟨rfl, h1_fr_X21⟩

