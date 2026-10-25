module

/-
Constant-time byte-slice comparison `memcmp(a, b, n)` on AArch64:
functional correctness and constant-time execution (leakage trace independence from buffer contents).
-/

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std
open Std.ExtHashMap

/-- Bitwise OR of byte-wise XOR differences across two byte lists. -/
def diffAcc : List UInt8 → List UInt8 → BitVec 64
  | x :: xs, y :: ys => (x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) ||| diffAcc xs ys
  | _, _ => 0#64

@[simp]
theorem diffAcc_nil_left (b : List UInt8) : diffAcc [] b = 0#64 := rfl

@[simp]
theorem diffAcc_nil_right (a : List UInt8) : diffAcc a [] = 0#64 := by
  cases a <;> rfl

theorem diffAcc_eq_zero_iff (a b : List UInt8) (h : a.length = b.length) :
    diffAcc a b = 0#64 ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [diffAcc]
    | cons _ _ => simp at h
  | cons x xs ih =>
    cases b with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [diffAcc, List.cons.injEq]
      have h_or :
          ((x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) ||| diffAcc xs ys) = 0#64 ↔
            (x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) = 0#64 ∧ diffAcc xs ys = 0#64 := by
        grind
      have h_xy : (x.toBitVec.setWidth 64 ^^^ y.toBitVec.setWidth 64) = 0#64 ↔ x = y := by
        cases x; cases y; simp; grind
      rw [h_or, h_xy, ih ys h]

private theorem ofInt_ofBytes_singleton (x : UInt8) :
    BitVec.ofInt 8 (Int.ofBytes [x]) = x.toBitVec := by
  simp [Int.ofBytes]

theorem diffAcc_one (a b : List UInt8) (ha : a.length = 1) (hb : b.length = 1) (acc : BitVec 64) :
    acc |||
      (((BitVec.ofInt 8 (Int.ofBytes a)).setWidth 32 ^^^
        (BitVec.ofInt 8 (Int.ofBytes b)).setWidth 32).setWidth 64) =
      acc ||| diffAcc a b := by
  rcases List.length_eq_one_iff.mp ha with ⟨x, rfl⟩
  rcases List.length_eq_one_iff.mp hb with ⟨y, rfl⟩
  rw [ofInt_ofBytes_singleton, ofInt_ofBytes_singleton]
  simp only [diffAcc]
  grind

theorem diffAcc_step (a b : List UInt8) (ha : 0 < a.length) (hb : 0 < b.length) (acc : BitVec 64) :
    (acc |||
      (((BitVec.ofInt 8 (Int.ofBytes (a.take 1))).setWidth 32 ^^^
        (BitVec.ofInt 8 (Int.ofBytes (b.take 1))).setWidth 32).setWidth 64)) |||
      diffAcc (a.drop 1) (b.drop 1) =
      acc ||| diffAcc a b := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
    cases b with
    | nil => simp at hb
    | cons y ys =>
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, diffAcc]
      rw [ofInt_ofBytes_singleton, ofInt_ofBytes_singleton]
      grind

-- Constant-time AAPCS64 byte-slice comparison `memcmp(a, b, n)`
-- Arguments: x0 = a, x1 = b, x2 = n, x30 (lr) = return address
-- Returns: x0 = diffAcc a b (0 iff a = b), sp = sp₀, pc = x30₀,
--          callee-saved registers and memory preserved,
--          and execution leakage trace depends only on public `(p_a, p_b, n)`.
def memcmp : Program := parseAArch64("
memcmp:
  mov x3, #0
  cbz x2, done
loop:
  ldrb w4, [x0]
  ldrb w5, [x1]
  eor w4, w4, w5
  orr x3, x3, x4
  add x0, x0, #1
  add x1, x1, #1
  sub x2, x2, #1
  cbnz x2, loop
done:
  mov x0, x3
  ret
")

theorem memcmp_ct_correct [layout : Layout] [Layout.Valid memcmp]
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
  kpack_secrets
  apply tailrec_loop_cps_traced (layout memcmp)
    (Inv := fun v _ => 0 < v)
    (P := fun v (a_ptr, b_ptr) s₀ _ (a_bs, b_bs, acc, frame) st =>
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
    (Q := fun _ (a_ptr, b_ptr) s₀ _ (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "done" ∧
      st.data.regs.X3.toBitVec = acc ||| diffAcc a_bs b_bs ∧
      st.data.regs.X30 = s₀.regs.X30 ∧
      st.data.regs.SP = s₀.regs.SP ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = b_bs.length ∧
      (st.data.dmem =⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (v0 := n)
    (pub0 := (p_a, p_b))
    (g0 := fun _ (a, b, R) => (a, b, 0#64, R))
  · by_cases hn : n = 0
    · subst hn
      left
      kintro s ⟨a, b, R⟩ ⟨h_x0, h_x1, h_x2, h_a_len, h_b_len, h_mem⟩
      kprologue memcmp to "loop" with s
      kstep
      kdone
      obtain rfl := List.eq_nil_of_length_eq_zero h_a_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_b_len
      exact ⟨by kaddr memcmp, rfl, rfl, rfl, by grind, rfl, by ecancel⟩
    · right
      refine ⟨by omega, ?_⟩
      kintro s ⟨a, b, R⟩ ⟨h_x0, h_x1, h_x2, h_a_len, h_b_len, h_mem⟩
      kprologue memcmp to "loop" with s
      kstep
      kdone
      exact ⟨by kaddr memcmp, by grind, h_x0, h_x1, rfl, rfl, rfl,
        by grind, h_a_len, h_b_len, by ecancel⟩
  · rintro v ⟨a_ptr, b_ptr⟩ hv
    by_cases hv1 : v = 1
    · subst hv1
      left
      kintro s₀ ⟨a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_x2_v, h_x0_v, h_x1_v, h_x3_v, h_x30, h_sp, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨by kaddr memcmp, ?_, h_x30, h_sp, h_cs, by omega, by ecancel⟩
      have := diffAcc_one a_bs b_bs h_a_v h_b_v acc
      grind
    · right
      refine ⟨v - 1, (a_ptr + 1#64, b_ptr + 1#64), by omega, by omega, ?_⟩
      kintro s₀ ⟨a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_x2_v, h_x0_v, h_x1_v, h_x3_v, h_x30, h_sp, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      rw [Mem.At_take_drop_sep a_bs 1 a_ptr (by omega) (by grind),
          Mem.At_take_drop_sep b_bs 1 b_ptr (by omega) (by grind)] at h_mem_v
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
      refine ⟨hQ_pc, ?_, hQ_x30, hQ_sp, hQ_cs, by omega, ?_⟩
      · rw [hQ_x3]
        exact diffAcc_step a_bs b_bs (by omega) (by omega) acc
      · rw [Mem.At_take_drop_sep a_bs 1 a_ptr (by omega) (by grind),
            Mem.At_take_drop_sep b_bs 1 b_ptr (by omega) (by grind)]
        ecancel
  · kintro s₀ ⟨a, b, R⟩ ⟨st, pc⟩ ⟨rfl, h_x3, h_x30, h_sp, h_cs, h_ab_len, h_mem_q⟩
    kprologue memcmp at "done" with st
    kstep
    kdone
    have h_diff := diffAcc_eq_zero_iff a b h_ab_len
    exact ⟨by grind, by grind, by grind, h_sp, h_cs, by ecancel⟩
