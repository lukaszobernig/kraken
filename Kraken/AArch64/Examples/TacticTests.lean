module

/-
Regression tests for the composition and frame tactics (`kcall`, `kloop`, `kloop_exit`,
`kloop_next`, `kframe`, `kframe_eqs`, `≡ … except`) on AArch64 examples.
-/

import all Kraken.AArch64.Examples.Memcmp
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

/-! ### Constant-time loops through `kloop`

`memcmp_ct_correct` (see Memcmp.lean) with the loop rule applied by `kloop (pub := …)`: the
goals are `init`, `body` (with `v pub hv` introduced) and `post`; `kloop_exit` / `kloop_next v' pub'`
pick the disjunct and discharge the measure/invariant side conditions, `kintro` peels the trace
witness. -/

theorem memcmp_ct_correct' [layout : Layout] [Layout.Valid memcmp]
    (p_a p_b : BitVec 64) (n : Nat) :
    ∃ tr : List Kraken.LeakageEvent,
      ∀ (s₀ : MachineData) (a b : List UInt8) (R : DataMem → Prop),
        (layout memcmp).Spec s₀ (trace := some tr)
          (pre :=
            s₀.regs.X0.toBitVec = p_a ∧
            s₀.regs.X1.toBitVec = p_b ∧
            s₀.regs.X2.toNat = n ∧
            a.length = n ∧
            b.length = n ∧
            (s₀.dmem =⋆ a @ p_a ⋆ b @ p_b ⋆ R))
          (post := fun st =>
            st.pc = Int64.ofBitVec s₀.regs.X30.toBitVec ∧
            st.data.regs.X0.toBitVec = diffAcc a b ∧
            (st.data.regs.X0 = 0 ↔ a = b) ∧
            st.data.regs.SP = s₀.regs.SP ∧
            st.data.regs.CalleeSavedEq s₀.regs ∧
            (st.data.dmem =⋆ a @ p_a ⋆ b @ p_b ⋆ R)) := by
  kloop
    (pubinv := fun v _ => 0 < v)
    (inv := fun v (a_ptr, b_ptr) s₀ _ (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "loop" ∧
      st.data.regs.X2.toNat = v ∧
      st.data.regs.X0.toBitVec = a_ptr ∧
      st.data.regs.X1.toBitVec = b_ptr ∧
      st.data.regs.X3.toBitVec = acc ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = v ∧
      b_bs.length = v ∧
      (st.data.dmem =⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (exit := fun _ (a_ptr, b_ptr) s₀ _ (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "done" ∧
      st.data.regs.X3.toBitVec = acc ||| diffAcc a_bs b_bs ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = b_bs.length ∧
      (st.data.dmem =⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (measure := n)
    (pub := (p_a, p_b))
    (ghost := fun _ (a, b, R) => (a, b, 0#64, R))
    with v ⟨a_ptr, b_ptr⟩ hv
  · by_cases hn : n = 0
    · subst hn
      kloop_exit
      kintro s ⟨a, b, R⟩ ⟨h_x0, h_x1, h_x2, h_a_len, h_b_len, h_mem⟩
      kprologue memcmp to "loop" with s
      kstep
      kdone
      obtain rfl := List.eq_nil_of_length_eq_zero h_a_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_b_len
      exact ⟨by kaddr memcmp, rfl, rfl, rfl, by grind, rfl, by ecancel⟩
    · kloop_next
      refine ⟨by omega, ?_⟩
      kintro s ⟨a, b, R⟩ ⟨h_x0, h_x1, h_x2, h_a_len, h_b_len, h_mem⟩
      kprologue memcmp to "loop" with s
      kstep
      kdone
      exact ⟨by kaddr memcmp, by grind, h_x0, h_x1, rfl, rfl, rfl,
        by grind, h_a_len, h_b_len, by ecancel⟩
  · by_cases hv1 : v = 1
    · subst hv1
      kloop_exit
      kintro s₀ ⟨a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_x2_v, h_x0_v, h_x1_v, h_x3_v, h_x30, h_sp, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨by kaddr memcmp, ?_, h_x30, h_sp, h_cs, by omega, by ecancel⟩
      have := diffAcc_one a_bs b_bs h_a_v h_b_v acc
      grind
    · kloop_next (v - 1) (a_ptr + 1#64, b_ptr + 1#64)
      kintro s₀ ⟨a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_x2_v, h_x0_v, h_x1_v, h_x3_v, h_x30, h_sp, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨(a_bs.drop 1, b_bs.drop 1,
        acc ||| (((BitVec.ofInt 8 (Int.ofBytes (a_bs.take 1))).setWidth 32 ^^^
                  (BitVec.ofInt 8 (Int.ofBytes (b_bs.take 1))).setWidth 32).setWidth 64),
        (a_bs.take 1) @ a_ptr ⋆ (b_bs.take 1) @ b_ptr ⋆ frame),
        ⟨by kaddr memcmp, by grind, by grind, by grind, by grind,
         h_x30, h_sp, h_cs, by simp [h_a_v], by simp [h_b_v], by ecancel⟩,
        ?_⟩
      rintro t_s ⟨hQ_pc, hQ_x3, hQ_x30, hQ_sp, hQ_cs, _, hQ_mem⟩
      refine ⟨hQ_pc, ?_, hQ_x30, hQ_sp, hQ_cs, by omega, by ecancel⟩
      rw [hQ_x3]
      exact diffAcc_step a_bs b_bs (by omega) (by omega) acc
  · kintro s₀ ⟨a, b, R⟩ ⟨st, pc⟩ ⟨rfl, h_x3, h_x30, h_sp, h_cs, h_ab_len, h_mem_q⟩
    kprologue memcmp at "done" with st
    kstep
    kdone
    have h_diff := diffAcc_eq_zero_iff a b h_ab_len
    exact ⟨by grind, by grind, by grind, h_sp, h_cs, by ecancel⟩
