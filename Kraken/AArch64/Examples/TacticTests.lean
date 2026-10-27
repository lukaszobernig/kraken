module

/-
Regression tests for the composition and frame tactics (`kcall`, `kloop`, `kloop_exit`,
`kloop_next`, `kframe`, `kframe_eqs`, `≡ … except`) on AArch64 examples.
-/

import all Kraken.AArch64.Examples.Memcpy
import all Kraken.AArch64.Examples.P256Beeu
import Kraken.Tactics

open Kraken Kraken.AArch64
open Kraken.AArch64.Parser


theorem memcpy_correct' [layout : Layout] [Layout.Valid memcpy] (s₀ : MachineData)
    (n : Nat) (dst src : List UInt8) (R : DataMem → Prop) :
    (layout memcpy).Spec s₀
      (pre :=
        s₀.regs.X2.toNat = n ∧
        dst.length = n ∧
        src.length = n ∧
        (s₀.dmem =⋆ dst @ s₀.regs.X0 ⋆ src @ s₀.regs.X1 ⋆ R))
      (post := fun st =>
        st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
        st.data.regs.X0 = s₀.regs.X0 ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        (st.data.dmem =⋆ src @ s₀.regs.X0 ⋆ src @ s₀.regs.X1 ⋆ R)) := by
  rintro ⟨h_x2, h_dst_len, h_src_len, h_mem⟩
  kloop
    (inv := fun v (dst_ptr, src_ptr, dst_bs, src_bs, frame) st =>
      st.pc = (layout memcpy).label "loop" ∧
      0 < v ∧
      st.data.regs.X2.toNat = v ∧
      st.data.regs.X3.toBitVec = dst_ptr ∧
      st.data.regs.X1.toBitVec = src_ptr ∧
      st.data.regs.X0 = s₀.regs.X0 ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      dst_bs.length = v ∧
      src_bs.length = v ∧
      (st.data.dmem =⋆ dst_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (exit := fun _ (dst_ptr, src_ptr, _, src_bs, frame) st =>
      st.pc = (layout memcpy).label "done" ∧
      st.data.regs.X0 = s₀.regs.X0 ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      (st.data.dmem =⋆ src_bs @ dst_ptr ⋆ src_bs @ src_ptr ⋆ frame))
    (measure := n)
    (ghost := (s₀.regs.X0.toBitVec, s₀.regs.X1.toBitVec, dst, src, R))
    with v ⟨dst_ptr, src_ptr, dst_bs, src_bs, frame⟩ ⟨hv, h_x2_v, rfl, rfl, h_x0, h_x30, h_sp, h_cs, h_dst_v, h_src_v, h_mem_v⟩
  · kprologue memcpy to "loop"
    by_cases hn : n = 0
    · sym => kstep; tactic =>
      subst hn
      obtain rfl := List.eq_nil_of_length_eq_zero h_dst_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_src_len
      kloop_exit
      exact ⟨by kaddr memcpy, rfl, rfl, rfl, Reg64s.CalleeSavedEq_refl _, by ecancel⟩
    · sym => kstep; tactic =>
      kloop_next
      exact ⟨by kaddr memcpy, by omega, by grind, by grind, rfl, rfl, rfl, rfl,
        Reg64s.CalleeSavedEq_refl _, h_dst_len, h_src_len, by ecancel⟩
  · by_cases hv1 : v = 1
    · subst hv1
      kprologue memcpy at "loop" to "done" with st
      sym => kstep; tactic =>
      kloop_exit
      exact ⟨by kaddr memcpy, h_x0, h_x30, h_sp, h_cs, by ecancel⟩
    · kprologue memcpy at "loop" to "done" with st
      sym => kstep; tactic =>
      kloop_next (v - 1) (X3.toBitVec + 1#64, X1.toBitVec + 1#64, dst_bs.drop 1, src_bs.drop 1,
        (src_bs.take 1) @ X3 ⋆ (src_bs.take 1) @ X1 ⋆ frame)
      · exact ⟨by kaddr memcpy, by grind, by grind, by grind, by grind, h_x0, h_x30, h_sp, h_cs,
          by simp [h_dst_v], by simp [h_src_v], by ecancel⟩
      · rintro t_s ⟨hQ_pc, hQ_x0, hQ_x30, hQ_sp, hQ_cs, hQ_mem⟩
        exact ⟨hQ_pc, hQ_x0, hQ_x30, hQ_sp, hQ_cs, by ecancel⟩
  · obtain ⟨h_x0, h_x30, h_sp, h_cs, h_mem_q⟩ := hst
    kprologue memcpy at "done" with st
    sym => kstep; tactic =>
    apply Eventually.done
    exact ⟨by grind, h_x0, h_sp, h_cs, by ecancel⟩


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
  kframe_eqs h1_fr
  apply Eventually.done
  refine ⟨rfl, ?_, ?_⟩
  · kframe
  · simp only [Reg64s.beeuA, h1_fr_X21, h1_fr_X22, h1_fr_X23, h1_fr_X24]


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
