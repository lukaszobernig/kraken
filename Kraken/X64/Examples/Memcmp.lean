module

/-
Constant-time byte-by-byte memory comparison `memcmp(a, b, n)` in x86_64 assembly,
following the System V AMD64 ABI (`%rdi = a`, `%rsi = b`, `%rdx = n`, `(%rsp) = ra`,
return value in `%rax`).

This file proves both:
1. Functional correctness: `%rax` holds the bitwise OR of `(a[i] ^^^ b[i])`, which is `0` iff `a = b`.
2. Constant-time security: for fixed public pointers `p_a`, `p_b`, stack pointer `p_sp`, and length `n`,
   there exists a single leakage trace `tr` (covering all instruction addresses and memory read
   addresses) that is produced for *all* secret byte contents `a` and `b`.
-/

import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.ToBytes
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics

open Kraken.X64.Parser
open Std
open Std.ExtHashMap

/-- Bitwise OR of all byte-wise XOR differences between `a` and `b`, zero-extended to 64 bits. -/
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
    acc ||| ((BitVec.ofInt 8 (Int.ofBytes a)).setWidth 64 ^^^
             (BitVec.ofInt 8 (Int.ofBytes b)).setWidth 64) =
      acc ||| diffAcc a b := by
  rcases List.length_eq_one_iff.mp ha with ⟨x, rfl⟩
  rcases List.length_eq_one_iff.mp hb with ⟨y, rfl⟩
  rw [ofInt_ofBytes_singleton, ofInt_ofBytes_singleton]
  simp only [diffAcc]
  grind

theorem diffAcc_step (a b : List UInt8) (ha : 0 < a.length) (hb : 0 < b.length) (acc : BitVec 64) :
    (acc ||| ((BitVec.ofInt 8 (Int.ofBytes (a.take 1))).setWidth 64 ^^^
              (BitVec.ofInt 8 (Int.ofBytes (b.take 1))).setWidth 64)) |||
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

-- Constant-time `memcmp(a, b, n)` in x86_64 assembly
-- Arguments: %rdi = a, %rsi = b, %rdx = n, (%rsp) = return address `ra`
-- Returns: %rax = bitwise OR of all `(a[i] ^ b[i])`, which is 0 iff the buffers are equal.
-- Notice there is no early exit on mismatch: the loop always runs `n` times.
def memcmp : Program := parse("
memcmp:
  movq $0, %rax
  subq $0, %rdx
  jz done
loop:
  movzbq (%rdi), %rcx
  movzbq (%rsi), %r8
  xorq %r8, %rcx
  orq %rcx, %rax
  addq $1, %rdi
  addq $1, %rsi
  subq $1, %rdx
  jnz loop
done:
  ret
")

theorem memcmp_ct_correct [layout : Layout] [Layout.Valid memcmp]
    (p_a p_b p_sp : BitVec 64) (n : Nat) :
    ∃ tr : List Kraken.LeakageEvent,
      ∀ (s₀ : MachineData) (ra : UInt64) (a b : List UInt8) (R : DataMem → Prop),
        (layout memcmp).Spec s₀ (trace := some tr)
          (pre :=
            s₀.regs.rdi.toBitVec = p_a ∧
            s₀.regs.rsi.toBitVec = p_b ∧
            s₀.regs.rsp.toBitVec = p_sp ∧
            s₀.regs.rdx.toNat = n ∧
            a.length = n ∧
            b.length = n ∧
            (s₀.dmem =⋆ ra @ s₀.regs.rsp ⋆ a @ p_a ⋆ b @ p_b ⋆ R))
          (post := fun st =>
            st.pc = Int64.ofBitVec ra.toBitVec ∧
            st.data.regs.rax.toBitVec = diffAcc a b ∧
            (st.data.regs.rax = 0 ↔ a = b) ∧
            st.data.regs.rsp = s₀.regs.rsp + 8 ∧
            st.data.regs.CalleeSavedEq s₀.regs ∧
            (st.data.dmem =⋆ ra @ s₀.regs.rsp ⋆ a @ p_a ⋆ b @ p_b ⋆ R)) := by
  kloop
    (pubinv := fun v _ => 0 < v)
    (inv := fun v (a_ptr, b_ptr) s₀ (ra, _, _, _) (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "loop" ∧
      st.data.regs.rdx.toNat = v ∧
      st.data.regs.rdi.toBitVec = a_ptr ∧
      st.data.regs.rsi.toBitVec = b_ptr ∧
      st.data.regs.rax.toBitVec = acc ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.rsp.toBitVec = p_sp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = v ∧
      b_bs.length = v ∧
      (st.data.dmem =⋆ ra @ p_sp ⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (exit := fun _ (a_ptr, b_ptr) s₀ (ra, _, _, _) (a_bs, b_bs, acc, frame) st =>
      st.pc = (layout memcmp).label "done" ∧
      st.data.regs.rax.toBitVec = acc ||| diffAcc a_bs b_bs ∧
      st.data.regs.rsp = s₀.regs.rsp ∧
      st.data.regs.rsp.toBitVec = p_sp ∧
      st.data.regs.CalleeSavedEq s₀.regs ∧
      a_bs.length = b_bs.length ∧
      (st.data.dmem =⋆ ra @ p_sp ⋆ a_bs @ a_ptr ⋆ b_bs @ b_ptr ⋆ frame))
    (measure := n)
    (pub := (p_a, p_b))
    (ghost := fun _ (_, a, b, R) => (a, b, 0#64, R))
    with v ⟨a_ptr, b_ptr⟩ hv
  · by_cases hn : n = 0
    · subst hn
      kloop_exit
      kintro s ⟨ra, a, b, R⟩ ⟨h_rdi, h_rsi, h_rsp, h_rdx, h_a_len, h_b_len, h_mem⟩
      rw [h_rsp] at h_mem
      kprologue memcmp to "loop" with s
      kstep
      kdone
      obtain rfl := List.eq_nil_of_length_eq_zero h_a_len
      obtain rfl := List.eq_nil_of_length_eq_zero h_b_len
      exact ⟨by kaddr memcmp, rfl, rfl, h_rsp, by grind, rfl, by ecancel⟩
    · kloop_next
      refine ⟨by omega, ?_⟩
      kintro s ⟨ra, a, b, R⟩ ⟨h_rdi, h_rsi, h_rsp, h_rdx, h_a_len, h_b_len, h_mem⟩
      rw [h_rsp] at h_mem
      kprologue memcmp to "loop" with s
      kstep
      kdone
      exact ⟨by kaddr memcmp, by grind, h_rdi, h_rsi, rfl, rfl, h_rsp,
        by grind, h_a_len, h_b_len, by ecancel⟩
  · by_cases hv1 : v = 1
    · subst hv1
      kloop_exit
      kintro s₀ ⟨ra, a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_rdx_v, h_rdi_v, h_rsi_v, h_rax_v, h_rsp, h_rsp_p, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨by kaddr memcmp, ?_, h_rsp, h_rsp_p, h_cs, by omega, by ecancel⟩
      have := diffAcc_one a_bs b_bs h_a_v h_b_v acc
      grind
    · kloop_next (v - 1) (a_ptr + 1#64, b_ptr + 1#64)
      kintro s₀ ⟨ra, a, b, R⟩ ⟨a_bs, b_bs, acc, frame⟩ ⟨s, pc⟩
        ⟨rfl, h_rdx_v, h_rdi_v, h_rsi_v, h_rax_v, h_rsp, h_rsp_p, h_cs, h_a_v, h_b_v, h_mem_v⟩
      kprologue memcmp at "loop" to "done" with s
      kstep
      kdone
      refine ⟨(a_bs.drop 1, b_bs.drop 1,
        acc ||| ((BitVec.ofInt 8 (Int.ofBytes (a_bs.take 1))).setWidth 64 ^^^
                 (BitVec.ofInt 8 (Int.ofBytes (b_bs.take 1))).setWidth 64),
        (a_bs.take 1) @ a_ptr ⋆ (b_bs.take 1) @ b_ptr ⋆ frame),
        ⟨by kaddr memcmp, by grind, by grind, by grind, by grind,
         h_rsp, h_rsp_p, h_cs, by simp [h_a_v], by simp [h_b_v], by ecancel⟩,
        ?_⟩
      rintro t_s ⟨hQ_pc, hQ_rax, hQ_rsp, hQ_rsp_p, hQ_cs, _, hQ_mem⟩
      refine ⟨hQ_pc, ?_, hQ_rsp, hQ_rsp_p, hQ_cs, by omega, by ecancel⟩
      rw [hQ_rax]
      exact diffAcc_step a_bs b_bs (by omega) (by omega) acc
  · kintro s₀ ⟨ra, a, b, R⟩ ⟨st, pc⟩ ⟨rfl, h_rax, h_rsp, h_rsp_p, h_cs, h_ab_len, h_mem_q⟩
    have h_rsp0 : s₀.regs.rsp.toBitVec = p_sp := by rw [← h_rsp, h_rsp_p]
    kprologue memcmp at "done" with st
    kstep
    kdone
    rw [← h_rsp0] at h_mem_q
    have h_diff := diffAcc_eq_zero_iff a b h_ab_len
    exact ⟨rfl, by grind, by grind, by grind, h_cs, by ecancel⟩
