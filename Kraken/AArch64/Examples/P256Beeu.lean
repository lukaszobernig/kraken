module

/-
Verification of BoringSSL's `beeu_mod_inverse_vartime`
from `third_party/openssl/boringssl/src/gen/bcm/p256_beeu-armv8-asm-linux.S`.
-/

import Kraken.AArch64.OmniSemantics
import Kraken.AArch64.Parser
import Kraken.AArch64.Semantics
import Kraken.SeparationMem
import Kraken.SeparationTactics
import Kraken.Tactics
import Std.Tactic.BVDecide
public import Lean.Elab.Tactic

open Kraken.AArch64
open Kraken.AArch64.Parser
open Std
open Std.ExtHashMap

-- Stripped of assembler directives and `AARCH64_SIGN_LINK_REGISTER` /
-- `AARCH64_VALIDATE_LINK_REGISTER` PAC macro annotations.
def beeu_mod_inverse_vartime : Program := parseAArch64("
beeu_mod_inverse_vartime:
    // Reserve enough space for 14 8-byte registers on the stack
    // in the first stp call for x29, x30.
    // Then store the remaining callee-saved registers.
    //
    //    | x29 | x30 | x19 | x20 | ... | x27 | x28 |  x0 |  x2 |
    //    ^                                                     ^
    //    sp  <------------------- 112 bytes ----------------> old sp
    //   x29 (FP)
    //
	stp	x29,x30,[sp,#-112]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	stp	x23,x24,[sp,#48]
	stp	x25,x26,[sp,#64]
	stp	x27,x28,[sp,#80]
	stp	x0,x2,[sp,#96]

    // B = b3..b0 := a
	ldp	x25,x26,[x1]
	ldp	x27,x28,[x1,#16]

    // n3..n0 := n
    // Note: the value of input params are changed in the following.
	ldp	x0,x1,[x2]
	ldp	x2,x30,[x2,#16]

    // A = a3..a0 := n
	mov	x21, x0
	mov	x22, x1
	mov	x23, x2
	mov	x24, x30

    // X = x4..x0 := 1
	mov	x3, #1
	eor	x4, x4, x4
	eor	x5, x5, x5
	eor	x6, x6, x6
	eor	x7, x7, x7

    // Y = y4..y0 := 0
	eor	x8, x8, x8
	eor	x9, x9, x9
	eor	x10, x10, x10
	eor	x11, x11, x11
	eor	x12, x12, x12

.Lbeeu_loop:
    // if B == 0, jump to .Lbeeu_loop_end
	orr	x14, x25, x26
	orr	x14, x14, x27

    // reverse the bit order of x25. This is needed for clz after this macro
	rbit	x15, x25

	orr	x14, x14, x28
	cbz	x14,.Lbeeu_loop_end

    // shift := number of trailing 0s in x25
	orr	x15, x15, #1
	clz	x13, x15

    // If there is no shift, goto shift_A_Y
	cbz	x13, .Lbeeu_shift_A_Y

    // Shift B right by x13 bits
	neg	x14, x13
	lsr	x25, x25, x13
	lsl	x15, x26, x14

	lsr	x26, x26, x13
	lsl	x19, x27, x14

	orr	x25, x25, x15

	lsr	x27, x27, x13
	lsl	x20, x28, x14

	orr	x26, x26, x19

	lsr	x28, x28, x13

	orr	x27, x27, x20

    // Shift X right by x13 bits, adding n whenever X becomes odd.
	eor	x14, x14, x14
.Lbeeu_shift_loop_X:
	tbz	x3, #0, .Lshift1_0
	adds	x3, x3, x0
	adcs	x4, x4, x1
	adcs	x5, x5, x2
	adcs	x6, x6, x30
	adc	x7, x7, x14
.Lshift1_0:
	extr	x3, x4, x3, #1
	extr	x4, x5, x4, #1
	extr	x5, x6, x5, #1
	extr	x6, x7, x6, #1
	lsr	x7, x7, #1

	subs	x13, x13, #1
	bne	.Lbeeu_shift_loop_X

.Lbeeu_shift_A_Y:
	rbit	x15, x21
	orr	x15, x15, #1
	clz	x13, x15

	cbz	x13, .Lbeeu_update_B_X_or_A_Y

	neg	x14, x13
	lsr	x21, x21, x13
	lsl	x15, x22, x14

	lsr	x22, x22, x13
	lsl	x19, x23, x14

	orr	x21, x21, x15

	lsr	x23, x23, x13
	lsl	x20, x24, x14

	orr	x22, x22, x19

	lsr	x24, x24, x13

	orr	x23, x23, x20

	eor	x14, x14, x14
.Lbeeu_shift_loop_Y:
	tbz	x8, #0, .Lshift1_1
	adds	x8, x8, x0
	adcs	x9, x9, x1
	adcs	x10, x10, x2
	adcs	x11, x11, x30
	adc	x12, x12, x14
.Lshift1_1:
	extr	x8, x9, x8, #1
	extr	x9, x10, x9, #1
	extr	x10, x11, x10, #1
	extr	x11, x12, x11, #1
	lsr	x12, x12, #1

	subs	x13, x13, #1
	bne	.Lbeeu_shift_loop_Y

.Lbeeu_update_B_X_or_A_Y:
	subs	x14, x25, x21
	sbcs	x15, x26, x22
	sbcs	x19, x27, x23
	sbcs	x20, x28, x24
	bcs	.Lbeeu_B_greater_than_A

	subs	x21, x21, x25
	sbcs	x22, x22, x26
	sbcs	x23, x23, x27
	sbcs	x24, x24, x28

	adds	x8, x8, x3
	adcs	x9, x9, x4
	adcs	x10, x10, x5
	adcs	x11, x11, x6
	adc	x12, x12, x7
	b	.Lbeeu_loop

.Lbeeu_B_greater_than_A:
	mov	x25, x14
	mov	x26, x15
	mov	x27, x19
	mov	x28, x20

	adds	x3, x3, x8
	adcs	x4, x4, x9
	adcs	x5, x5, x10
	adcs	x6, x6, x11
	adc	x7, x7, x12
	b	.Lbeeu_loop

.Lbeeu_loop_end:
	sub	x14, x21, #1
	orr	x14, x14, x22
	orr	x14, x14, x23
	orr	x14, x14, x24
	cbnz	x14, .Lbeeu_err

.Lbeeu_reduction_loop:
	subs	x3, x8, x0
	sbcs	x4, x9, x1
	sbcs	x5, x10, x2
	sbcs	x6, x11, x30
	sbcs	x7, x12, x14

	csel	x8, x3, x8, cs
	csel	x9, x4, x9, cs
	csel	x10, x5, x10, cs
	csel	x11, x6, x11, cs
	csel	x12, x7, x12, cs
	bcs	.Lbeeu_reduction_loop

	subs	x8, x0, x8
	sbcs	x9, x1, x9
	sbcs	x10, x2, x10
	sbcs	x11, x30, x11

	ldr	x3, [sp,#96]
	stp	x8, x9, [x3]
	stp	x10, x11, [x3,#16]
	mov	x0, #1
	b	.Lbeeu_finish

.Lbeeu_err:
	eor	x0, x0, x0

.Lbeeu_finish:
	add	sp,x29,#0
	ldp	x19,x20,[sp,#16]
	ldp	x21,x22,[sp,#32]
	ldp	x23,x24,[sp,#48]
	ldp	x25,x26,[sp,#64]
	ldp	x27,x28,[sp,#80]
	ldp	x29,x30,[sp],#112

	ret
")

/-! ## Multi-Limb Integer Representations & Arithmetic Helpers -/

/-- 256-bit unsigned integer represented across four 64-bit registers (little-endian limbs). -/
def val256 (w0 w1 w2 w3 : UInt64) : Int :=
  (w0.toNat : Int) +
  256 ^ 8 * (w1.toNat : Int) +
  256 ^ 16 * (w2.toNat : Int) +
  256 ^ 24 * (w3.toNat : Int)

/-- 320-bit unsigned integer represented across five 64-bit registers (little-endian limbs). -/
def val320 (w0 w1 w2 w3 w4 : UInt64) : Int :=
  (w0.toNat : Int) +
  256 ^ 8 * (w1.toNat : Int) +
  256 ^ 16 * (w2.toNat : Int) +
  256 ^ 24 * (w3.toNat : Int) +
  256 ^ 32 * (w4.toNat : Int)

/-- Register-tuple projections for the live 256/320-bit BEEU state in `Reg64s`. -/
abbrev Reg64s.beeuB (r : Reg64s) : Int := val256 r.X25 r.X26 r.X27 r.X28
abbrev Reg64s.beeuA (r : Reg64s) : Int := val256 r.X21 r.X22 r.X23 r.X24
abbrev Reg64s.beeuN (r : Reg64s) : Int := val256 r.X0 r.X1 r.X2 r.X30
abbrev Reg64s.beeuX (r : Reg64s) : Int := val320 r.X3 r.X4 r.X5 r.X6 r.X7
abbrev Reg64s.beeuY (r : Reg64s) : Int := val320 r.X8 r.X9 r.X10 r.X11 r.X12
abbrev Reg64s.beeuY256 (r : Reg64s) : Int := val256 r.X8 r.X9 r.X10 r.X11

/-- The 12 saved callee-saved/frame registers in the `beeu_mod_inverse_vartime` stack frame. -/
def BeeuSavedRegs (r₀ : Reg64s) (sp' : BitVec 64) : DataMem → Prop :=
  (Int.toBytes 8 r₀.X29.toBitVec.toInt) @ sp' ⋆
  (Int.toBytes 8 r₀.X30.toBitVec.toInt) @ (sp' + 8#64) ⋆
  (Int.toBytes 8 r₀.X19.toBitVec.toInt) @ (sp' + 16#64) ⋆
  (Int.toBytes 8 r₀.X20.toBitVec.toInt) @ (sp' + 24#64) ⋆
  (Int.toBytes 8 r₀.X21.toBitVec.toInt) @ (sp' + 32#64) ⋆
  (Int.toBytes 8 r₀.X22.toBitVec.toInt) @ (sp' + 40#64) ⋆
  (Int.toBytes 8 r₀.X23.toBitVec.toInt) @ (sp' + 48#64) ⋆
  (Int.toBytes 8 r₀.X24.toBitVec.toInt) @ (sp' + 56#64) ⋆
  (Int.toBytes 8 r₀.X25.toBitVec.toInt) @ (sp' + 64#64) ⋆
  (Int.toBytes 8 r₀.X26.toBitVec.toInt) @ (sp' + 72#64) ⋆
  (Int.toBytes 8 r₀.X27.toBitVec.toInt) @ (sp' + 80#64) ⋆
  (Int.toBytes 8 r₀.X28.toBitVec.toInt) @ (sp' + 88#64)

/-- The 112-byte stack frame saved by the `beeu_mod_inverse_vartime` prologue. -/
def BeeuStackFrame (r₀ : Reg64s) (sp' : BitVec 64) : DataMem → Prop :=
  BeeuSavedRegs r₀ sp' ⋆
  (Int.toBytes 8 r₀.X0.toBitVec.toInt) @ (sp' + 96#64) ⋆
  (Int.toBytes 8 r₀.X2.toBitVec.toInt) @ (sp' + 104#64)

/-- Four 64-bit limbs stored contiguously in memory at address `p`. -/
def Words256At (w0 w1 w2 w3 : UInt64) (p : BitVec 64) : DataMem → Prop :=
  (Int.toBytes 8 w0.toBitVec.toInt) @ p ⋆
  (Int.toBytes 8 w1.toBitVec.toInt) @ (p + 8#64) ⋆
  (Int.toBytes 8 w2.toBitVec.toInt) @ (p + 16#64) ⋆
  (Int.toBytes 8 w3.toBitVec.toInt) @ (p + 24#64)

@[simp, ksimp, grind =]
theorem sp_sub_112_mod_16 (sp : BitVec 64) :
    (sp + 18446744073709551504#64) % 16#64 = sp % 16#64 := by
  bv_decide

@[simp, ksimp, grind =]
theorem sp_sub_112_add_zero (sp : BitVec 64) :
    sp + 18446744073709551504#64 + 0#64 = sp + 18446744073709551504#64 := by
  bv_decide

@[simp, ksimp, grind =]
theorem sp_add_112_cancel (sp : BitVec 64) :
    sp + 18446744073709551504#64 + 112#64 = sp := by
  bv_decide

theorem Int.ofBytes_32_split (bs : List UInt8) (h : bs.length = 32) :
    Int.ofBytes bs =
      Int.ofBytes (bs.take 8) +
      256 ^ 8 * Int.ofBytes ((bs.drop 8).take 8) +
      256 ^ 16 * Int.ofBytes ((bs.drop 16).take 8) +
      256 ^ 24 * Int.ofBytes ((bs.drop 24).take 8) := by
  have h1 : bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ (bs.drop 24).take 8)) := by
    have h24 : (bs.drop 24).take 8 = bs.drop 24 := List.take_of_length_le (by simp [h])
    rw [h24]
    have h16 : (bs.drop 16).take 8 ++ bs.drop 24 = bs.drop 16 := by
      conv => rhs; rw [← List.take_append_drop 8 (bs.drop 16), List.drop_drop]
    rw [h16]
    have h8 : (bs.drop 8).take 8 ++ bs.drop 16 = bs.drop 8 := by
      conv => rhs; rw [← List.take_append_drop 8 (bs.drop 8), List.drop_drop]
    rw [h8, List.take_append_drop]
  conv => lhs; rw [h1]
  rw [Int.ofBytes_append, Int.ofBytes_append, Int.ofBytes_append]
  have h_len1 : (bs.take 8).length = 8 := by simp [h]
  have h_len2 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h_len3 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  rw [h_len1, h_len2, h_len3]
  omega

theorem val256_of_limbs (bs : List UInt8) (h : bs.length = 32) :
    val256
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (bs.take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 8).take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 16).take 8))))
      (UInt64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes ((bs.drop 24).take 8)))) =
      Int.ofBytes bs := by
  dsimp only [val256]
  rw [UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_toNat_ofInt_64 _ (by simp [h]),
      Int.ofBytes_32_split bs h]

/-! ## 1. Prologue Verification (`beeu_mod_inverse_vartime` to `.Lbeeu_loop`) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_prologue_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) (stack a_bs n_bs : List UInt8) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pre :=
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        s₀.regs.SP.toBitVec % 16#64 = 0#64 ∧
        stack.length = 112 ∧
        a_bs.length = 32 ∧
        n_bs.length = 32 ∧
        (s₀.dmem =⋆ stack @ sp' ⋆ a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R))
      (post := fun st =>
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
        st.data.regs.SP.toBitVec = sp' ∧
        st.data.regs.X29.toBitVec = sp' ∧
        st.data.regs.beeuB = Int.ofBytes a_bs ∧
        st.data.regs.beeuA = Int.ofBytes n_bs ∧
        st.data.regs.beeuN = Int.ofBytes n_bs ∧
        st.data.regs.beeuX = 1 ∧
        st.data.regs.beeuY = 0 ∧
        (st.data.dmem =⋆
          BeeuStackFrame s₀.regs sp' ⋆
          a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)) := by
  rintro ⟨h_sp_align, h_stack_len, h_a_len, h_n_len, h_mem⟩
  dsimp only [BeeuStackFrame, BeeuSavedRegs]
  kprologue beeu_mod_inverse_vartime to ".Lbeeu_loop" with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨by kaddr beeu_mod_inverse_vartime, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by ecancel⟩
  · dsimp +zetaDelta only; simp
  · dsimp +zetaDelta only; simp
  · dsimp +zetaDelta only [Reg64s.beeuB]
    exact val256_of_limbs a_bs h_a_len
  · dsimp +zetaDelta only [Reg64s.beeuA]
    simp only [BitVec.shiftLeft_zero, BitVec.zero_or]
    exact val256_of_limbs n_bs h_n_len
  · dsimp +zetaDelta only [Reg64s.beeuN]
    exact val256_of_limbs n_bs h_n_len
  · dsimp +zetaDelta only [Reg64s.beeuX, val320]; simp; decide
  · dsimp +zetaDelta only [Reg64s.beeuY, val320]; simp

/-! ## Multi-Limb Arithmetic Lemmas for Loop Steps -/

theorem val256_nonneg (w0 w1 w2 w3 : UInt64) : 0 ≤ val256 w0 w1 w2 w3 := by
  dsimp [val256]; omega

theorem val256_lt (w0 w1 w2 w3 : UInt64) : val256 w0 w1 w2 w3 < 256 ^ 32 := by
  have h0 : w0.toNat < 2 ^ 64 := w0.toBitVec.isLt
  have h1 : w1.toNat < 2 ^ 64 := w1.toBitVec.isLt
  have h2 : w2.toNat < 2 ^ 64 := w2.toBitVec.isLt
  have h3 : w3.toNat < 2 ^ 64 := w3.toBitVec.isLt
  dsimp [val256]; omega

theorem val320_nonneg (w0 w1 w2 w3 w4 : UInt64) : 0 ≤ val320 w0 w1 w2 w3 w4 := by
  dsimp [val320]; omega

theorem val320_lt (w0 w1 w2 w3 w4 : UInt64) : val320 w0 w1 w2 w3 w4 < 256 ^ 40 := by
  have h0 : w0.toNat < 2 ^ 64 := w0.toBitVec.isLt
  have h1 : w1.toNat < 2 ^ 64 := w1.toBitVec.isLt
  have h2 : w2.toNat < 2 ^ 64 := w2.toBitVec.isLt
  have h3 : w3.toNat < 2 ^ 64 := w3.toBitVec.isLt
  have h4 : w4.toNat < 2 ^ 64 := w4.toBitVec.isLt
  dsimp [val320]; omega

theorem val256_eq_zero_limbs (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 = 0) :
    w0.toBitVec = 0#64 ∧ w1.toBitVec = 0#64 ∧ w2.toBitVec = 0#64 ∧ w3.toBitVec = 0#64 := by
  dsimp [val256] at h
  have hw0 : w0.toNat = 0 := by omega
  have hw1 : w1.toNat = 0 := by omega
  have hw2 : w2.toNat = 0 := by omega
  have hw3 : w3.toNat = 0 := by omega
  refine ⟨BitVec.eq_of_toNat_eq hw0, BitVec.eq_of_toNat_eq hw1,
          BitVec.eq_of_toNat_eq hw2, BitVec.eq_of_toNat_eq hw3⟩

theorem val256_eq_one_limbs (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 = 1) :
    w0.toBitVec = 1#64 ∧ w1.toBitVec = 0#64 ∧ w2.toBitVec = 0#64 ∧ w3.toBitVec = 0#64 := by
  dsimp [val256] at h
  have hw0 : w0.toNat = 1 := by omega
  have hw1 : w1.toNat = 0 := by omega
  have hw2 : w2.toNat = 0 := by omega
  have hw3 : w3.toNat = 0 := by omega
  refine ⟨BitVec.eq_of_toNat_eq hw0, BitVec.eq_of_toNat_eq hw1,
          BitVec.eq_of_toNat_eq hw2, BitVec.eq_of_toNat_eq hw3⟩

theorem or4_sub_one_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    ((x0 - 1#64 ||| x1 ||| x2 ||| x3) = 0#64) ↔
      (x0 = 1#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) := by
  bv_decide

theorem val256_ne_one_or_ne_zero (w0 w1 w2 w3 : UInt64) (h : val256 w0 w1 w2 w3 ≠ 1) :
    ((w0.toBitVec - 1#64 ||| w1.toBitVec ||| w2.toBitVec ||| w3.toBitVec) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_zero
  have ⟨h0, h1, h2, h3⟩ := (or4_sub_one_eq_zero_iff w0.toBitVec w1.toBitVec w2.toBitVec w3.toBitVec).mp h_zero
  apply h
  dsimp [val256]
  have hw0 : w0.toNat = 1 := congrArg BitVec.toNat h0
  have hw1 : w1.toNat = 0 := congrArg BitVec.toNat h1
  have hw2 : w2.toNat = 0 := congrArg BitVec.toNat h2
  have hw3 : w3.toNat = 0 := congrArg BitVec.toNat h3
  omega

theorem val320_lt_256_pow_32 (w0 w1 w2 w3 w4 : UInt64) (h : val320 w0 w1 w2 w3 w4 < 256 ^ 32) :
    w4 = 0 ∧ val256 w0 w1 w2 w3 = val320 w0 w1 w2 w3 w4 := by
  dsimp only [val320, val256] at h ⊢
  have hw4 : w4.toNat = 0 := by omega
  refine ⟨UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw4), by omega⟩

theorem or4_eq_zero_iff (x0 x1 x2 x3 : BitVec 64) :
    ((x0 ||| x1 ||| x2 ||| x3) = 0#64) ↔
      (x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) := by
  bv_decide

theorem val256_pos_or_ne_zero (w0 w1 w2 w3 : UInt64) (h : 0 < val256 w0 w1 w2 w3) :
    ((w0.toBitVec ||| w1.toBitVec ||| w2.toBitVec ||| w3.toBitVec) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_zero
  have ⟨h0, h1, h2, h3⟩ := (or4_eq_zero_iff w0.toBitVec w1.toBitVec w2.toBitVec w3.toBitVec).mp h_zero
  have hw0 : w0.toNat = 0 := congrArg BitVec.toNat h0
  have hw1 : w1.toNat = 0 := congrArg BitVec.toNat h1
  have hw2 : w2.toNat = 0 := congrArg BitVec.toNat h2
  have hw3 : w3.toNat = 0 := congrArg BitVec.toNat h3
  dsimp [val256] at h
  omega

/-- Single 64-bit limb produced by `extr dst, hi, lo, #1`. -/
def extr1Word (hi lo : UInt64) : BitVec 64 :=
  (hi.toBitVec <<< 63) ||| (lo.toBitVec >>> 1)

theorem extr_sem_eq (hi lo : UInt64) :
    (if (1 == 0) = true then lo.toBitVec else hi.toBitVec <<< (64 - 1) ||| lo.toBitVec >>> 1) =
      extr1Word hi lo := rfl

theorem ubfm_lsr1_sem_eq (x : UInt64) :
    (if (1 : Nat) ≤ 63 then BitVec.setWidth 64 (BitVec.extractLsb' 0 63 (x.toBitVec >>> 1))
     else BitVec.setWidth 64 (BitVec.extractLsb' 0 64 x.toBitVec) <<< 63) =
      x.toBitVec >>> 1 := by
  bv_decide

theorem extr1_eq_add_bv (hi lo : BitVec 64) :
    (hi <<< 63) ||| (lo >>> 1) = (lo >>> 1) + 0x8000000000000000#64 * (hi &&& 1#64) := by
  bv_decide

theorem extr1Word_toNat (hi lo : UInt64) :
    (UInt64.ofBitVec (extr1Word hi lo)).toNat =
      lo.toNat / 2 + 2 ^ 63 * (hi.toNat % 2) := by
  dsimp only [extr1Word]
  rw [UInt64.toNat_ofBitVec, extr1_eq_add_bv, BitVec.toNat_add, BitVec.toNat_mul]
  have h_shr : (lo.toBitVec >>> 1).toNat = lo.toNat / 2 :=
    UInt64.toNat_ofBitVec_ushiftRight_one lo
  have h_and : (hi.toBitVec &&& 1#64).toNat = hi.toNat % 2 :=
    UInt64.toNat_ofBitVec_and_one hi
  have h_lt : lo.toNat < 2 ^ 64 := lo.toBitVec.isLt
  have h_pow : (0x8000000000000000#64).toNat = 2 ^ 63 := rfl
  rw [h_shr, h_and, h_pow]
  omega

theorem shift1_val320 (x0 x1 x2 x3 x4 : UInt64) :
    let w0 := UInt64.ofBitVec (extr1Word x1 x0)
    let w1 := UInt64.ofBitVec (extr1Word x2 x1)
    let w2 := UInt64.ofBitVec (extr1Word x3 x2)
    let w3 := UInt64.ofBitVec (extr1Word x4 x3)
    let w4 := UInt64.ofBitVec (x4.toBitVec >>> 1)
    2 * val320 w0 w1 w2 w3 w4 + (x0.toNat % 2 : Int) = val320 x0 x1 x2 x3 x4 := by
  have h0 := extr1Word_toNat x1 x0
  have h1 := extr1Word_toNat x2 x1
  have h2 := extr1Word_toNat x3 x2
  have h3 := extr1Word_toNat x4 x3
  have h4 := UInt64.toNat_ofBitVec_ushiftRight_one x4
  dsimp only [val320]
  omega

theorem getLsbD_zero_eq_false_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = false) :
    x.toNat % 2 = 0 := by
  have h_bv : (x.toBitVec &&& 1#64) = 0#64 := by revert h; bv_decide
  have h_and := UInt64.toNat_ofBitVec_and_one x
  rw [UInt64.toNat_ofBitVec, h_bv] at h_and
  exact h_and.symm

theorem getLsbD_zero_eq_true_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = true) :
    x.toNat % 2 = 1 := by
  have h_bv : (x.toBitVec &&& 1#64) = 1#64 := by revert h; bv_decide
  have h_and := UInt64.toNat_ofBitVec_and_one x
  rw [UInt64.toNat_ofBitVec, h_bv] at h_and
  exact h_and.symm

theorem val320_emod_two (x0 x1 x2 x3 x4 : UInt64) :
    val320 x0 x1 x2 x3 x4 % 2 = (x0.toNat % 2 : Int) := by
  dsimp only [val320]; omega

theorem val256_emod_two (x0 x1 x2 x3 : UInt64) :
    val256 x0 x1 x2 x3 % 2 = (x0.toNat % 2 : Int) := by
  dsimp only [val256]; omega

/-- Clamped trailing-zero count `(w.reverse ||| 1).clz` in `[0, 63]`. -/
def ctzClamped (w : UInt64) : BitVec 64 :=
  (w.toBitVec.reverse ||| 1#64).clz

/-- Single 64-bit limb produced by `SHIFT256` (`(lo >> k) | (hi << (-k))`). -/
def shift256Word (lo hi : UInt64) (k : BitVec 64) : BitVec 64 :=
  lo.toBitVec.ushiftRight (k.toNat % 64) ||| (hi.toBitVec <<< ((0#64 - k).toNat % 64))

/-- Top 64-bit limb produced by `SHIFT256` (`hi >> k`). -/
def shift256TopWord (hi : UInt64) (k : BitVec 64) : BitVec 64 :=
  hi.toBitVec.ushiftRight (k.toNat % 64)

theorem clz_reverse_or_one_le_63 (b0 : BitVec 64) :
    (b0.reverse ||| 1#64).clz ≤ 63#64 := by
  bv_decide

theorem clz_reverse_or_one_mask_zero (b0 : BitVec 64) :
    b0 &&& ((1#64 <<< (((b0.reverse ||| 1#64).clz) % 64#64)) - 1#64) = 0#64 := by
  bv_decide

theorem shift256_limb_bv128 (lo hi k : BitVec 64) (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((1#64 <<< (k % 64#64)).setWidth 128) *
      (((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).setWidth 128) +
      (lo &&& ((1#64 <<< (k % 64#64)) - 1#64)).setWidth 128 =
      lo.setWidth 128 +
      0x10000000000000000#128 * ((hi &&& ((1#64 <<< (k % 64#64)) - 1#64)).setWidth 128) := by
  bv_decide

theorem shift256_top_bv128 (hi k : BitVec 64) (hk63 : k ≤ 63#64) :
    ((1#64 <<< (k % 64#64)).setWidth 128) * ((hi >>> (k % 64#64)).setWidth 128) +
      (hi &&& ((1#64 <<< (k % 64#64)) - 1#64)).setWidth 128 =
      hi.setWidth 128 := by
  bv_decide

theorem one_shiftLeft_toNat (k : BitVec 64) (hk63 : k ≤ 63#64) :
    (1#64 <<< (k % 64#64)).toNat = 2 ^ k.toNat := by
  have hk_lt : k.toNat < 64 := by
    have h63 : (63#64).toNat = 63 := rfl
    have hle : k.toNat ≤ (63#64).toNat := BitVec.le_def.mp hk63
    omega
  have hmod : (k % 64#64).toNat = k.toNat := by
    rw [BitVec.toNat_umod]
    change k.toNat % 64 = k.toNat
    omega
  change (1#64 <<< (k % 64#64).toNat).toNat = 2 ^ k.toNat
  rw [BitVec.toNat_shiftLeft, hmod, Nat.shiftLeft_eq]
  have hpow : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk_lt
  change (1 * 2 ^ k.toNat) % 2 ^ 64 = 2 ^ k.toNat
  rw [Nat.one_mul, Nat.mod_eq_of_lt hpow]

theorem shift256Word_eq_aux (lo hi : UInt64) (k d : BitVec 64) :
    (lo.toBitVec.ushiftRight (k.toNat % 64) ||| (hi.toBitVec <<< (d.toNat % 64))) =
      (lo.toBitVec >>> (k % 64#64)) ||| (hi.toBitVec <<< (d % 64#64)) := by
  have h1 : (k % 64#64).toNat = k.toNat % 64 := BitVec.toNat_umod
  have h2 : (d % 64#64).toNat = d.toNat % 64 := BitVec.toNat_umod
  rw [← h1, ← h2]
  rfl

theorem shift256Word_eq (lo hi : UInt64) (k : BitVec 64) :
    shift256Word lo hi k =
      (lo.toBitVec >>> (k % 64#64)) ||| (hi.toBitVec <<< ((0#64 - k) % 64#64)) :=
  shift256Word_eq_aux lo hi k (0#64 - k)

theorem shift256TopWord_eq (hi : UInt64) (k : BitVec 64) :
    shift256TopWord hi k = hi.toBitVec >>> (k % 64#64) := by
  dsimp only [shift256TopWord]
  have h1 : (k % 64#64).toNat = k.toNat % 64 := BitVec.toNat_umod
  rw [← h1]
  rfl

theorem bv128_c64_toNat : (0x10000000000000000#128).toNat = 2 ^ 64 := rfl

theorem bv128_mod_mul (x y : Nat) (hy : y < 2 ^ 64) (hm : x * y ≤ 2 ^ 63 * y) :
    (x * y) % 2 ^ 128 = x * y :=
  Nat.mod_eq_of_lt (by omega)

theorem bv128_mod_mul_add (x y z : Nat) (hy : y < 2 ^ 64) (hz : z < 2 ^ 64)
    (hm : x * y ≤ 2 ^ 63 * y) :
    (x * y + z) % 2 ^ 128 = x * y + z :=
  Nat.mod_eq_of_lt (by omega)

theorem bv128_mod_c64_mul (z : Nat) (hz : z < 2 ^ 64) :
    (2 ^ 64 * z) % 2 ^ 128 = 2 ^ 64 * z :=
  Nat.mod_eq_of_lt (by omega)

theorem bv128_mod_add_c64_mul (l z : Nat) (hl : l < 2 ^ 64) (hz : z < 2 ^ 64) :
    (l + 2 ^ 64 * z) % 2 ^ 128 = l + 2 ^ 64 * z :=
  Nat.mod_eq_of_lt (by omega)

theorem bv64_setWidth128_toNat (w : BitVec 64) : (w.setWidth 128).toNat = w.toNat :=
  BitVec.toNat_setWidth_of_le (by decide : 64 ≤ 128)

theorem bv128_linear_toNat (p w1 w2 mlo mhi : BitVec 64) (lo : UInt64) (k : Nat)
    (hk : k ≤ 63) (hp : p.toNat = 2 ^ k) (hw : w1 = w2)
    (h_eq : (p.setWidth 128) * (w2.setWidth 128) + mlo.setWidth 128 =
      lo.toBitVec.setWidth 128 + 0x10000000000000000#128 * (mhi.setWidth 128)) :
    2 ^ k * (UInt64.ofBitVec w1).toNat + mlo.toNat = lo.toNat + 2 ^ 64 * mhi.toNat := by
  subst hw
  have h_bv := congrArg BitVec.toNat h_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, bv64_setWidth128_toNat,
    UInt64.toNat_toBitVec, bv128_c64_toNat] at h_bv
  have h_pow_le : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hk
  have h_mul_le : 2 ^ k * w1.toNat ≤ 2 ^ 63 * w1.toNat := Nat.mul_le_mul_right _ h_pow_le
  rw [hp, bv128_mod_mul (2 ^ k) w1.toNat w1.isLt h_mul_le,
      bv128_mod_mul_add (2 ^ k) w1.toNat mlo.toNat w1.isLt mlo.isLt h_mul_le,
      bv128_mod_c64_mul mhi.toNat mhi.isLt,
      bv128_mod_add_c64_mul lo.toNat mhi.toNat lo.toBitVec.isLt mhi.isLt] at h_bv
  rw [UInt64.toNat_ofBitVec]
  exact h_bv

theorem bv128_top_toNat (p w1 w2 mhi : BitVec 64) (hi : UInt64) (k : Nat)
    (hk : k ≤ 63) (hp : p.toNat = 2 ^ k) (hw : w1 = w2)
    (h_eq : (p.setWidth 128) * (w2.setWidth 128) + mhi.setWidth 128 =
      hi.toBitVec.setWidth 128) :
    2 ^ k * (UInt64.ofBitVec w1).toNat + mhi.toNat = hi.toNat := by
  subst hw
  have h_bv := congrArg BitVec.toNat h_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, bv64_setWidth128_toNat,
    UInt64.toNat_toBitVec] at h_bv
  have h_pow_le : 2 ^ k ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hk
  have h_mul_le : 2 ^ k * w1.toNat ≤ 2 ^ 63 * w1.toNat := Nat.mul_le_mul_right _ h_pow_le
  rw [hp, bv128_mod_mul (2 ^ k) w1.toNat w1.isLt h_mul_le,
      bv128_mod_mul_add (2 ^ k) w1.toNat mhi.toNat w1.isLt mhi.isLt h_mul_le] at h_bv
  rw [UInt64.toNat_ofBitVec]
  exact h_bv

theorem shift256_limb_toNat (lo hi : UInt64) (k : BitVec 64)
    (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (UInt64.ofBitVec (shift256Word lo hi k)).toNat +
      (lo.toBitVec &&& mask).toNat =
      lo.toNat + 2 ^ 64 * (hi.toBitVec &&& mask).toNat :=
  bv128_linear_toNat
    (1#64 <<< (k % 64#64))
    (shift256Word lo hi k)
    ((lo.toBitVec >>> (k % 64#64)) ||| (hi.toBitVec <<< ((0#64 - k) % 64#64)))
    (lo.toBitVec &&& ((1#64 <<< (k % 64#64)) - 1#64))
    (hi.toBitVec &&& ((1#64 <<< (k % 64#64)) - 1#64))
    lo k.toNat hk63
    (one_shiftLeft_toNat k hk63)
    (shift256Word_eq lo hi k)
    (shift256_limb_bv128 lo.toBitVec hi.toBitVec k hk1 hk63)

theorem shift256_top_toNat (hi : UInt64) (k : BitVec 64) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (UInt64.ofBitVec (shift256TopWord hi k)).toNat +
      (hi.toBitVec &&& mask).toNat = hi.toNat :=
  bv128_top_toNat
    (1#64 <<< (k % 64#64))
    (shift256TopWord hi k)
    (hi.toBitVec >>> (k % 64#64))
    (hi.toBitVec &&& ((1#64 <<< (k % 64#64)) - 1#64))
    hi k.toNat hk63
    (one_shiftLeft_toNat k hk63)
    (shift256TopWord_eq hi k)
    (shift256_top_bv128 hi.toBitVec k hk63)

theorem shift256_val256 (b0 b1 b2 b3 : UInt64) (h_nz : ctzClamped b0 ≠ 0#64) :
    let k := ctzClamped b0
    let w0 := UInt64.ofBitVec (shift256Word b0 b1 k)
    let w1 := UInt64.ofBitVec (shift256Word b1 b2 k)
    let w2 := UInt64.ofBitVec (shift256Word b2 b3 k)
    let w3 := UInt64.ofBitVec (shift256TopWord b3 k)
    ((2 ^ k.toNat : Nat) : Int) * val256 w0 w1 w2 w3 = val256 b0 b1 b2 b3 := by
  let k := ctzClamped b0
  have hk63 : k ≤ 63#64 := clz_reverse_or_one_le_63 b0.toBitVec
  have hk1 : 1#64 ≤ k := by
    rw [BitVec.le_def]
    have : k.toNat ≠ 0 := fun h0 => h_nz (BitVec.eq_of_toNat_eq h0)
    change 1 ≤ k.toNat
    omega
  have h0 := shift256_limb_toNat b0 b1 k hk1 hk63
  have h1 := shift256_limb_toNat b1 b2 k hk1 hk63
  have h2 := shift256_limb_toNat b2 b3 k hk1 hk63
  have h3 := shift256_top_toNat b3 k hk63
  have hm0 : (b0.toBitVec &&& ((1#64 <<< (k % 64#64)) - 1#64)).toNat = 0 := by
    dsimp +zetaDelta only [ctzClamped]
    rw [clz_reverse_or_one_mask_zero]
    rfl
  dsimp +zetaDelta only [val256] at h0 h1 h2 h3 ⊢
  rw [hm0] at h0
  grind

theorem sub256_step (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    val256
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2)) -
      (if c3 then 0 else 1) * 256 ^ 32 =
      val256 b0 b1 b2 b3 - val256 a0 a1 a2 a3 := by
  have h0 := sub0_step b0 a0
  have h1 := sbc_step b1 a1 (sub0Carry b0 a0)
  have h2 := sbc_step b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))
  have h3 := sbc_step b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))
  dsimp only [val256]
  omega

theorem sub256_carry_of_ge (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 ≥ val256 a0 a1 a2 a3) :
    sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))) = true := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  have h_lt := val256_lt
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
  dsimp +zetaDelta only at h_step h_lt
  revert h_step
  cases sbcCarry b3 a3 c2
  · intro h_step; simp only [Bool.false_eq_true, ↓reduceIte] at h_step; omega
  · intro _; rfl

theorem sub256_val_of_ge (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 ≥ val256 a0 a1 a2 a3) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    val256
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2)) =
      val256 b0 b1 b2 b3 - val256 a0 a1 a2 a3 := by
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  dsimp +zetaDelta only at h_step ⊢
  have h_c := sub256_carry_of_ge b0 b1 b2 b3 a0 a1 a2 a3 h
  simp only [h_c, ↓reduceIte] at h_step
  omega

theorem sub256_carry_of_lt (b0 b1 b2 b3 a0 a1 a2 a3 : UInt64)
    (h : val256 b0 b1 b2 b3 < val256 a0 a1 a2 a3) :
    sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0))) = false := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  have h_step := sub256_step b0 b1 b2 b3 a0 a1 a2 a3
  have h_nonneg := val256_nonneg
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
  dsimp +zetaDelta only at h_step h_nonneg
  revert h_step
  cases sbcCarry b3 a3 c2
  · intro _; rfl
  · intro h_step
    simp only [↓reduceIte] at h_step
    omega

theorem add320_val_of_lt (x0 x1 x2 x3 x4 y0 y1 y2 y3 y4 : UInt64)
    (h : val320 x0 x1 x2 x3 x4 + val320 y0 y1 y2 y3 y4 < 256 ^ 40) :
    let c0 := add0Carry x0 y0
    let c1 := adcCarry x1 y1 c0
    let c2 := adcCarry x2 y2 c1
    let c3 := adcCarry x3 y3 c2
    val320
      (UInt64.ofBitVec (add0Word x0 y0))
      (UInt64.ofBitVec (adcWord x1 y1 c0))
      (UInt64.ofBitVec (adcWord x2 y2 c1))
      (UInt64.ofBitVec (adcWord x3 y3 c2))
      (UInt64.ofBitVec (adcWord x4 y4 c3)) =
      val320 x0 x1 x2 x3 x4 + val320 y0 y1 y2 y3 y4 := by
  let c0 := add0Carry x0 y0
  let c1 := adcCarry x1 y1 c0
  let c2 := adcCarry x2 y2 c1
  let c3 := adcCarry x3 y3 c2
  have h0 := add0_step x0 y0
  have h1 := adc_step x1 y1 c0
  have h2 := adc_step x2 y2 c1
  have h3 := adc_step x3 y3 c2
  have h4 := adc_step x4 y4 c3
  have h_nonneg := val320_nonneg
    (UInt64.ofBitVec (add0Word x0 y0))
    (UInt64.ofBitVec (adcWord x1 y1 c0))
    (UInt64.ofBitVec (adcWord x2 y2 c1))
    (UInt64.ofBitVec (adcWord x3 y3 c2))
    (UInt64.ofBitVec (adcWord x4 y4 c3))
  dsimp +zetaDelta only [val320] at h0 h1 h2 h3 h4 h h_nonneg ⊢
  omega

theorem sub320_step (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    let c4 := sbcCarry b4 a4 c3
    val320
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2))
      (UInt64.ofBitVec (sbcWord b4 a4 c3)) -
      (if c4 then 0 else 1) * 256 ^ 40 =
      val320 b0 b1 b2 b3 b4 - val320 a0 a1 a2 a3 a4 := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h0 := sub0_step b0 a0
  have h1 := sbc_step b1 a1 c0
  have h2 := sbc_step b2 a2 c1
  have h3 := sbc_step b3 a3 c2
  have h4 := sbc_step b4 a4 c3
  dsimp +zetaDelta only [val320] at h0 h1 h2 h3 h4 ⊢
  omega

theorem sub320_carry_of_ge (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 ≥ val320 a0 a1 a2 a3 a4) :
    sbcCarry b4 a4 (sbcCarry b3 a3 (sbcCarry b2 a2 (sbcCarry b1 a1 (sub0Carry b0 a0)))) = true := by
  let c0 := sub0Carry b0 a0
  let c1 := sbcCarry b1 a1 c0
  let c2 := sbcCarry b2 a2 c1
  let c3 := sbcCarry b3 a3 c2
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  have h_lt := val320_lt
    (UInt64.ofBitVec (sub0Word b0 a0))
    (UInt64.ofBitVec (sbcWord b1 a1 c0))
    (UInt64.ofBitVec (sbcWord b2 a2 c1))
    (UInt64.ofBitVec (sbcWord b3 a3 c2))
    (UInt64.ofBitVec (sbcWord b4 a4 c3))
  dsimp +zetaDelta only at h_step h_lt
  revert h_step
  cases sbcCarry b4 a4 c3
  · intro h_step; simp only [Bool.false_eq_true, ↓reduceIte] at h_step; omega
  · intro _; rfl

theorem sub320_val_of_ge (b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 : UInt64)
    (h : val320 b0 b1 b2 b3 b4 ≥ val320 a0 a1 a2 a3 a4) :
    let c0 := sub0Carry b0 a0
    let c1 := sbcCarry b1 a1 c0
    let c2 := sbcCarry b2 a2 c1
    let c3 := sbcCarry b3 a3 c2
    val320
      (UInt64.ofBitVec (sub0Word b0 a0))
      (UInt64.ofBitVec (sbcWord b1 a1 c0))
      (UInt64.ofBitVec (sbcWord b2 a2 c1))
      (UInt64.ofBitVec (sbcWord b3 a3 c2))
      (UInt64.ofBitVec (sbcWord b4 a4 c3)) =
      val320 b0 b1 b2 b3 b4 - val320 a0 a1 a2 a3 a4 := by
  have h_step := sub320_step b0 b1 b2 b3 b4 a0 a1 a2 a3 a4
  dsimp +zetaDelta only at h_step ⊢
  have h_c := sub320_carry_of_ge b0 b1 b2 b3 b4 a0 a1 a2 a3 a4 h
  simp only [h_c, ↓reduceIte] at h_step
  omega

/-! ## 2. Loop Exit Verification (`.Lbeeu_loop` to `.Lbeeu_loop_end` when `B = 0`) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_loop_exit_when_B_zero [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre := s₀.regs.beeuB = 0)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.X29 = s₀.regs.X29 ∧
        st.data.regs.beeuA = s₀.regs.beeuA ∧
        st.data.regs.beeuN = s₀.regs.beeuN ∧
        st.data.regs.beeuX = s₀.regs.beeuX ∧
        st.data.regs.beeuY = s₀.regs.beeuY ∧
        st.data.dmem = s₀.dmem) := by
  intro h_B_zero
  have ⟨h25, h26, h27, h28⟩ := val256_eq_zero_limbs
    s₀.regs.X25 s₀.regs.X26 s₀.regs.X27 s₀.regs.X28 h_B_zero
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_A_Y" with s₀
  sym => kstep; tactic =>
  apply Eventually.done
  refine ⟨by kaddr beeu_mod_inverse_vartime, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Loop Update Step Verification (`.Lbeeu_update_B_X_or_A_Y` to `.Lbeeu_loop`) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_update_step_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y")
      (pre := s₀.regs.beeuX + s₀.regs.beeuY < 256 ^ 40)
      (post := fun st =>
        let B := s₀.regs.beeuB
        let A := s₀.regs.beeuA
        let X := s₀.regs.beeuX
        let Y := s₀.regs.beeuY
        let B' := st.data.regs.beeuB
        let A' := st.data.regs.beeuA
        let X' := st.data.regs.beeuX
        let Y' := st.data.regs.beeuY
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.X29 = s₀.regs.X29 ∧
        st.data.regs.beeuN = s₀.regs.beeuN ∧
        st.data.dmem = s₀.dmem ∧
        (if B ≥ A then
          B' = B - A ∧ A' = A ∧ X' = X + Y ∧ Y' = Y
        else
          B' = B ∧ A' = A - B ∧ X' = X ∧ Y' = Y + X) ∧
        B' * Y' + A' * X' = B * Y + A * X) := by
  intro h_xy_bound
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_update_B_X_or_A_Y" to ".Lbeeu_B_greater_than_A" with s₀
  by_cases h_ge : val256 X25 X26 X27 X28 ≥ val256 X21 X22 X23 X24
  · have h_carry := sub256_carry_of_ge X25 X26 X27 X28 X21 X22 X23 X24 h_ge
    have hB' := sub256_val_of_ge X25 X26 X27 X28 X21 X22 X23 X24 h_ge
    have hX' := add320_val_of_lt X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 h_xy_bound
    sym => kstep; tactic =>
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_B_greater_than_A" to ".Lbeeu_loop_end"
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX, Reg64s.beeuY] at hB' hX' ⊢
    simp only [BitVec.shiftLeft_zero, BitVec.zero_or, UInt64.toNat_toBitVec, h_ge, ↓reduceIte]
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, trivial, trivial, ⟨hB', trivial, hX', trivial⟩, ?_⟩
    rw [hB', hX']; grind
  · have h_lt : val256 X25 X26 X27 X28 < val256 X21 X22 X23 X24 := Int.lt_of_not_ge h_ge
    have h_le : val256 X21 X22 X23 X24 ≥ val256 X25 X26 X27 X28 := Int.le_of_lt h_lt
    have h_carry := sub256_carry_of_lt X25 X26 X27 X28 X21 X22 X23 X24 h_lt
    have h_yx_bound : val320 X8 X9 X10 X11 X12 + val320 X3 X4 X5 X6 X7 < 256 ^ 40 := by
      dsimp only [Reg64s.beeuX, Reg64s.beeuY] at h_xy_bound; omega
    have hA' := sub256_val_of_ge X21 X22 X23 X24 X25 X26 X27 X28 h_le
    have hY' := add320_val_of_lt X8 X9 X10 X11 X12 X3 X4 X5 X6 X7 h_yx_bound
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX, Reg64s.beeuY] at hA' hY' ⊢
    simp only [BitVec.shiftLeft_zero, UInt64.toNat_toBitVec, h_ge, ↓reduceIte]
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, trivial, trivial, ⟨trivial, hA', trivial, hY'⟩, ?_⟩
    rw [hA', hY']; grind

/-! ## 4. Epilogue & Modular Negation Verification (`.Lbeeu_err` and `.Lbeeu_reduction_loop` to Return) -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_epilogue_err_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_err")
      (pre :=
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        r₀.SP.toBitVec % 16#64 = 0#64 ∧
        s.regs.X29 = UInt64.ofBitVec sp' ∧
        (s.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R))
      (post := fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.X0 = 0 ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        st.data.regs.CalleeSavedEq r₀ ∧
        (st.data.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R)) := by
  rintro ⟨h_sp_align, h_x29, h_mem⟩
  dsimp only [BeeuStackFrame, BeeuSavedRegs] at h_mem ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_err" with s
  subst h_x29
  sym => kstep; tactic =>
  apply Eventually.done
  dsimp +zetaDelta only
  simp only [BitVec.ofInt_ofBytes_toBytes_64, BitVec.shiftLeft_zero, BitVec.xor_self]
  refine ⟨trivial, rfl, ?_, trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by ecancel⟩
  apply UInt64.eq_of_toBitVec_eq
  change (r₀.SP.toBitVec + 18446744073709551504#64 + 0#64) + 112#64 = r₀.SP.toBitVec
  grind

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_reduction_and_store_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (sp' out_p : BitVec 64) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop")
      (pre :=
        sp' % 16#64 = 0#64 ∧
        s.regs.SP = UInt64.ofBitVec sp' ∧
        s.regs.X12 = 0 ∧
        s.regs.X14 = 0 ∧
        s.regs.beeuY256 < s.regs.beeuN ∧
        (s.dmem =⋆
          (Int.toBytes 8 out_p.toInt) @ (sp' + 96#64) ⋆
          Words256At o0 o1 o2 o3 out_p ⋆
          R))
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_finish" ∧
        st.data.regs.X0 = 1 ∧
        st.data.regs.SP = UInt64.ofBitVec sp' ∧
        st.data.regs.X29 = s.regs.X29 ∧
        ∃ w0 w1 w2 w3 : UInt64,
          val256 w0 w1 w2 w3 = s.regs.beeuN - s.regs.beeuY256 ∧
          (st.data.dmem =⋆
            (Int.toBytes 8 out_p.toInt) @ (sp' + 96#64) ⋆
            Words256At w0 w1 w2 w3 out_p ⋆
            R)) := by
  rintro ⟨h_sp_align, h_sp, h12, h14, h_lt, h_mem⟩
  dsimp only [Words256At, Reg64s.beeuY256, Reg64s.beeuN] at h_lt h_mem ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_reduction_loop" to ".Lbeeu_err" with s
  subst h_sp h12 h14
  have h_carry4 := sub256_carry_of_lt X8 X9 X10 X11 X0 X1 X2 X30 h_lt
  have h_le : val256 X0 X1 X2 X30 ≥ val256 X8 X9 X10 X11 := Int.le_of_lt h_lt
  have h_sub := sub256_val_of_ge X0 X1 X2 X30 X8 X9 X10 X11 h_le
  have h_zero_sbc :
      (((0#64 - 0#64 - BitVec.ofNat 64 (!false).toNat).toNat : Int) ==
        ((0#64).toNat : Int) - ((0#64).toNat : Int) - 1) = false := by
    decide
  sym => kstep; tactic =>
  apply Eventually.done
  dsimp +zetaDelta only [sub0Carry, sbcCarry, sub0Word, sbcWord] at *
  simp only [BitVec.shiftLeft_zero, UInt64.toNat_toBitVec,
    h_carry4, h_zero_sbc, Bool.false_eq_true, ↓reduceIte] at *
  refine ⟨by kaddr beeu_mod_inverse_vartime, rfl, trivial, trivial, _, _, _, _, h_sub, by ecancel⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_finish_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_finish")
      (pre :=
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        r₀.SP.toBitVec % 16#64 = 0#64 ∧
        s.regs.X29 = UInt64.ofBitVec sp' ∧
        (s.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R))
      (post := fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.X0 = s.regs.X0 ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        st.data.regs.CalleeSavedEq r₀ ∧
        (st.data.dmem =⋆ BeeuStackFrame r₀ sp' ⋆ R)) := by
  rintro ⟨h_sp_align, h_x29, h_mem⟩
  dsimp only [BeeuStackFrame, BeeuSavedRegs] at h_mem ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_finish" with s
  subst h_x29
  sym => kstep; tactic =>
  apply Eventually.done
  dsimp +zetaDelta only
  simp only [BitVec.ofInt_ofBytes_toBytes_64]
  refine ⟨trivial, trivial, ?_, trivial, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by ecancel⟩
  apply UInt64.eq_of_toBitVec_eq
  change (r₀.SP.toBitVec + 18446744073709551504#64 + 0#64) + 112#64 = r₀.SP.toBitVec
  grind

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_loop_end_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end")
      (pre := True)
      (post := fun st =>
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        if s.regs.beeuA = 1 then
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
          st.data.regs.X14 = 0 ∧
          st.data.regs.X0 = s.regs.X0 ∧
          st.data.regs.X1 = s.regs.X1 ∧
          st.data.regs.X2 = s.regs.X2 ∧
          st.data.regs.X30 = s.regs.X30 ∧
          st.data.regs.X8 = s.regs.X8 ∧
          st.data.regs.X9 = s.regs.X9 ∧
          st.data.regs.X10 = s.regs.X10 ∧
          st.data.regs.X11 = s.regs.X11 ∧
          st.data.regs.X12 = s.regs.X12
        else
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_err") := by
  intro _
  by_cases hA : s.regs.beeuA = 1
  · simp only [hA, ↓reduceIte]
    dsimp only [Reg64s.beeuA] at hA
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop_end" to ".Lbeeu_reduction_loop" with s
    have ⟨h21, h22, h23, h24⟩ := val256_eq_one_limbs X21 X22 X23 X24 hA
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨rfl, rfl, rfl, rfl, rfl, by kaddr beeu_mod_inverse_vartime,
      by dsimp +zetaDelta only; rw [h21, h22, h23, h24]; decide,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hA, ↓reduceIte]
    dsimp only [Reg64s.beeuA] at hA
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop_end" to ".Lbeeu_reduction_loop" with s
    have h_nz := val256_ne_one_or_ne_zero X21 X22 X23 X24 hA
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨rfl, rfl, rfl, rfl, rfl, by kaddr beeu_mod_inverse_vartime⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_reduction_step_ge_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop")
      (pre :=
        s.regs.X14 = 0 ∧
        s.regs.beeuY ≥ s.regs.beeuN)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.X0 = s.regs.X0 ∧
        st.data.regs.X1 = s.regs.X1 ∧
        st.data.regs.X2 = s.regs.X2 ∧
        st.data.regs.X30 = s.regs.X30 ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY - s.regs.beeuN ∧
        st.data.dmem = s.dmem) := by
  rintro ⟨h14, h_ge⟩
  dsimp only [Reg64s.beeuY, Reg64s.beeuN] at h_ge ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_reduction_loop" to ".Lbeeu_err" with s
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h_ge320 : val320 X8 X9 X10 X11 X12 ≥ val320 X0 X1 X2 X30 X14 := by
    subst h14
    dsimp only [val320, val256] at h_ge ⊢
    omega
  have h_carry := sub320_carry_of_ge X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_ge320
  have h_sub := sub320_val_of_ge X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_ge320
  sym => kstep; tactic =>
  apply Eventually.done
  dsimp +zetaDelta only [sub0Carry, sbcCarry, sub0Word, sbcWord] at h_carry h_sub ⊢
  simp only [BitVec.shiftLeft_zero, UInt64.toNat_toBitVec, h_carry, ↓reduceIte] at h_sub ⊢
  refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, h14, trivial, trivial, trivial, trivial, trivial, ?_, trivial⟩
  rw [h_sub]
  subst h14
  dsimp only [val320, val256]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Full verification of `.Lbeeu_reduction_loop` through `.Lbeeu_finish` to `ret`:
    repeatedly subtracts `N` from `Y` while `Y ≥ N`, then stores `N - (Y % N)` to `out_p`,
    restores callee-saved registers, and returns `1`. -/
theorem beeu_reduction_to_return_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop")
      (pre :=
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        r₀.SP.toBitVec % 16#64 = 0#64 ∧
        s.regs.SP = UInt64.ofBitVec sp' ∧
        s.regs.X29 = UInt64.ofBitVec sp' ∧
        s.regs.X14 = 0 ∧
        0 < s.regs.beeuN ∧
        (s.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
          R))
      (post := fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.X0 = 1 ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        st.data.regs.CalleeSavedEq r₀ ∧
        ∃ w0 w1 w2 w3 : UInt64,
          val256 w0 w1 w2 w3 = s.regs.beeuN - (s.regs.beeuY % s.regs.beeuN) ∧
          (st.data.dmem =⋆
            BeeuStackFrame r₀ sp' ⋆
            Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆
            R)) := by
  rintro ⟨h_sp_align, h_sp, h_x29, h_x14, h_n_pos, h_mem⟩
  let sp' := r₀.SP.toBitVec + 18446744073709551504#64
  apply tailrec_loop (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
      st.data.regs.SP = UInt64.ofBitVec sp' ∧
      st.data.regs.X29 = UInt64.ofBitVec sp' ∧
      st.data.regs.X14 = 0 ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.regs.beeuY % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
      st.data.regs.beeuY.toNat = v ∧
      st.data.dmem = s.dmem)
    (Q := fun (_ : Nat) (_ : Unit) st =>
      st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
      st.data.regs.X0 = 1 ∧
      st.data.regs.SP = r₀.SP ∧
      st.data.regs.X30 = r₀.X30 ∧
      st.data.regs.CalleeSavedEq r₀ ∧
      ∃ w0 w1 w2 w3 : UInt64,
        val256 w0 w1 w2 w3 = s.regs.beeuN - (s.regs.beeuY % s.regs.beeuN) ∧
        (st.data.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆
          R))
    (lt := (· < ·))
    (Hwf := Nat.lt_wfRel.wf)
    (v0 := s.regs.beeuY.toNat)
    (g0 := ())
  · exact ⟨rfl, h_sp, h_x29, h_x14, rfl, rfl, rfl, rfl⟩
  · rintro v _ ⟨st_data, st_pc⟩ ⟨rfl, hst_sp, hst_x29, hst_x14, hst_N, hst_Y_mod, hst_v, hst_dmem⟩
    dsimp only at hst_sp hst_x29 hst_x14 hst_N hst_Y_mod hst_v hst_dmem
    by_cases h_ge : st_data.regs.beeuY ≥ st_data.regs.beeuN
    · apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_reduction_step_ge_correct st_data ⟨hst_x14, h_ge⟩)
      intro mid ⟨h_pc, h_sp', h_x29', h_x14', _, _, _, _, h_N', h_Y', h_dmem'⟩
      right
      refine ⟨mid.data.regs.beeuY.toNat, (), ⟨h_pc, h_sp'.trans hst_sp, h_x29'.trans hst_x29,
        h_x14', h_N'.trans hst_N, ?_, rfl, h_dmem'.trans hst_dmem⟩, ?_, fun _ hQ => hQ⟩
      · rw [h_Y', hst_N, Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod, hst_Y_mod]
      · have hY_nonneg : 0 ≤ st_data.regs.beeuY := val320_nonneg _ _ _ _ _
        rw [h_Y', hst_N, ← hst_v]
        omega
    · have h_lt : st_data.regs.beeuY < st_data.regs.beeuN := Int.lt_of_not_ge h_ge
      have h_N_lt : st_data.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
      have ⟨h_x12, h_y256⟩ := val320_lt_256_pow_32
        st_data.regs.X8 st_data.regs.X9 st_data.regs.X10 st_data.regs.X11 st_data.regs.X12
        (by dsimp only [Reg64s.beeuY] at h_lt; omega)
      have h_y256_lt : st_data.regs.beeuY256 < st_data.regs.beeuN := by
        dsimp only [Reg64s.beeuY256]; rw [h_y256]; exact h_lt
      have h_sp_align' : sp' % 16#64 = 0#64 := by
        dsimp only [sp']; rw [sp_sub_112_mod_16]; exact h_sp_align
      have h_mem_st : (st_data.dmem =⋆
          (Int.toBytes 8 r₀.X0.toBitVec.toInt) @ (sp' + 96#64) ⋆
          Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
          (BeeuSavedRegs r₀ sp' ⋆
           (Int.toBytes 8 r₀.X2.toBitVec.toInt) @ (sp' + 104#64) ⋆ R)) := by
        rw [hst_dmem]
        dsimp only [BeeuStackFrame] at h_mem ⊢
        ecancel
      apply (beeu_reduction_and_store_correct st_data sp' r₀.X0.toBitVec o0 o1 o2 o3 _
        ⟨h_sp_align', hst_sp, h_x12, hst_x14, h_y256_lt, h_mem_st⟩).bind
      rintro ⟨mid_data, mid_pc⟩ ⟨rfl, h_mid_x0, h_mid_sp, h_mid_x29, w0, w1, w2, w3, h_mid_val, h_mid_mem⟩
      dsimp only at h_mid_x0 h_mid_sp h_mid_x29 h_mid_val h_mid_mem
      have h_mid_mem' : (mid_data.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)) := by
        dsimp +zetaDelta only [BeeuStackFrame] at h_mid_mem ⊢
        ecancel
      apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_finish_correct mid_data r₀ (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)
          ⟨h_sp_align, h_mid_x29.trans hst_x29, h_mid_mem'⟩)
      rintro fin ⟨h_fin_pc, h_fin_x0, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_mem⟩
      left
      refine ⟨h_fin_pc, h_fin_x0.trans h_mid_x0, h_fin_sp, h_fin_x30, h_fin_cs,
        w0, w1, w2, w3, ?_, by ecancel⟩
      have hY_nonneg : 0 ≤ st_data.regs.beeuY := val320_nonneg _ _ _ _ _
      have hY_mod_eq : st_data.regs.beeuY % s.regs.beeuN = st_data.regs.beeuY :=
        Int.emod_eq_of_lt hY_nonneg (hst_N ▸ h_lt)
      dsimp only [Reg64s.beeuY256] at h_mid_val
      rw [h_mid_val, h_y256, hst_N, ← hst_Y_mod, hY_mod_eq]
  · intro st hQ
    exact hQ

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Complete verification from `.Lbeeu_loop_end` to function return:
    if `A = 1`, reduces `Y` modulo `N`, writes `N - (Y % N)` to `out`, and returns `1`;
    if `A ≠ 1`, leaves `out` unchanged and returns `0`. -/
theorem beeu_loop_end_to_return_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (r₀ : Reg64s) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end")
      (pre :=
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        r₀.SP.toBitVec % 16#64 = 0#64 ∧
        s.regs.SP = UInt64.ofBitVec sp' ∧
        s.regs.X29 = UInt64.ofBitVec sp' ∧
        0 < s.regs.beeuN ∧
        (s.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
          R))
      (post := fun st =>
        let sp' := r₀.SP.toBitVec + 18446744073709551504#64
        st.pc = Int64.ofInt r₀.X30.toBitVec.toInt ∧
        st.data.regs.SP = r₀.SP ∧
        st.data.regs.X30 = r₀.X30 ∧
        st.data.regs.CalleeSavedEq r₀ ∧
        if s.regs.beeuA = 1 then
          st.data.regs.X0 = 1 ∧
          ∃ w0 w1 w2 w3 : UInt64,
            val256 w0 w1 w2 w3 = s.regs.beeuN - (s.regs.beeuY % s.regs.beeuN) ∧
            (st.data.dmem =⋆
              BeeuStackFrame r₀ sp' ⋆
              Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆
              R)
        else
          st.data.regs.X0 = 0 ∧
          (st.data.dmem =⋆
            BeeuStackFrame r₀ sp' ⋆
            Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆
            R)) := by
  rintro ⟨h_sp_align, h_sp, h_x29, h_n_pos, h_mem⟩
  apply (beeu_loop_end_correct s trivial).bind
  rintro ⟨mid_data, mid_pc⟩ ⟨h_mid_sp, h_mid_x29, h_mid_N, h_mid_Y, h_mid_dmem, h_branch⟩
  dsimp only at h_mid_sp h_mid_x29 h_mid_N h_mid_Y h_mid_dmem h_branch
  by_cases hA : s.regs.beeuA = 1
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    rcases h_branch with ⟨rfl, h_mid_x14, _⟩
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_reduction_to_return_correct mid_data r₀ o0 o1 o2 o3 R
        ⟨h_sp_align, h_mid_sp.trans h_sp, h_mid_x29.trans h_x29, h_mid_x14,
         h_mid_N.symm ▸ h_n_pos, h_mid_dmem ▸ h_mem⟩)
    rintro fin ⟨h_pc, h_x0, h_sp', h_x30', h_cs', w0, w1, w2, w3, h_val, h_mem'⟩
    rw [h_mid_N, h_mid_Y] at h_val
    exact ⟨h_pc, h_sp', h_x30', h_cs', h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    subst h_branch
    have h_mem_mid : (mid_data.dmem =⋆
        BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆
        (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)) := by
      rw [h_mid_dmem]; ecancel
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_epilogue_err_correct mid_data r₀ (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)
        ⟨h_sp_align, h_mid_x29.trans h_x29, h_mem_mid⟩)
    rintro fin ⟨h_pc, h_x0, h_sp', h_x30', h_cs', h_mem'⟩
    exact ⟨h_pc, h_sp', h_x30', h_cs', h_x0, by ecancel⟩

/-! ## 5. Inner Shift Loop & `SHIFT256` Block Verification -/

theorem sub_one_beq_zero_false_of_gt_one (x : UInt64) (h : 1 < x.toNat) :
    ((x.toBitVec - 1#64) == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h_eq
  have h_nat : (x.toBitVec - 1#64).toNat = 0 := congrArg BitVec.toNat h_eq
  rw [BitVec.toNat_sub_of_le] at h_nat
  · change x.toNat - 1 = 0 at h_nat; omega
  · rw [BitVec.le_def]; change 1 ≤ x.toNat; omega

theorem toNat_sub_one_of_pos (x : UInt64) (h : 0 < x.toNat) :
    (UInt64.ofBitVec (x.toBitVec - 1#64)).toNat = x.toNat - 1 := by
  rw [UInt64.toNat_ofBitVec, BitVec.toNat_sub_of_le]
  · rfl
  · rw [BitVec.le_def]; change 1 ≤ x.toNat; omega

theorem pow2_mul_emod_step (m : Nat) (x x' n z : Int)
    (h_inv : (((2 ^ m : Nat) : Int) * x) % n = z)
    (h_step : (2 * x') % n = x % n) :
    (((2 ^ (m + 1) : Nat) : Int) * x') % n = z := by
  have h_pow : ((2 ^ (m + 1) : Nat) : Int) * x' = ((2 ^ m : Nat) : Int) * (2 * x') := by
    rw [Nat.pow_succ, Int.natCast_mul]; grind
  rw [h_pow, Int.mul_emod, h_step, ← Int.mul_emod, h_inv]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_shift_loop_X_pre_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X")
      (pre :=
        s.regs.X14 = 0 ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuX + s.regs.beeuN < 256 ^ 40)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lshift1_0" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X13 = s.regs.X13 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        st.data.regs.beeuX % 2 = 0 ∧
        st.data.regs.beeuX % s.regs.beeuN = s.regs.beeuX % s.regs.beeuN ∧
        st.data.regs.beeuX ≤ s.regs.beeuX + s.regs.beeuN) := by
  rintro ⟨h14, hN_odd, h_xn_lt⟩
  dsimp only [Reg64s.beeuX, Reg64s.beeuN] at hN_odd h_xn_lt ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_loop_X" to ".Lshift1_0" with s
  cases h_lsb : X3.toBitVec.getLsbD 0
  · have h_mod2 := getLsbD_zero_eq_false_mod2 X3 h_lsb
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only
    refine ⟨by kaddr beeu_mod_inverse_vartime, rfl, rfl, rfl, h14, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
    · rw [val320_emod_two]; omega
    · have := val256_nonneg X0 X1 X2 X30; omega
  · have h_mod2 := getLsbD_zero_eq_true_mod2 X3 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_lt320 : val320 X3 X4 X5 X6 X7 + val320 X0 X1 X2 X30 X14 < 256 ^ 40 := by
      subst h14; dsimp only [val320, val256] at h_xn_lt ⊢; omega
    have h_add := add320_val_of_lt X3 X4 X5 X6 X7 X0 X1 X2 X30 X14 h_lt320
    have h_n320 : val320 X0 X1 X2 X30 X14 = val256 X0 X1 X2 X30 := by
      subst h14; dsimp only [val320, val256]; omega
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only [add0Carry, adcCarry, add0Word, adcWord] at h_add ⊢
    simp only [BitVec.shiftLeft_zero, UInt64.toNat_toBitVec] at h_add ⊢
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, trivial, h14,
      trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_⟩
    · rw [h_add, h_n320]
      have hx := val320_emod_two X3 X4 X5 X6 X7
      omega
    · rw [h_add, h_n320, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
    · rw [h_add, h_n320]
      omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_shift1_0_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lshift1_0")
      (pre :=
        0 < s.regs.X13.toNat ∧
        s.regs.beeuX % 2 = 0)
      (post := fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y"
        else
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X") ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        2 * st.data.regs.beeuX = s.regs.beeuX) := by
  rintro ⟨h_x13_pos, h_x_even⟩
  by_cases h1 : s.regs.X13.toNat = 1
  · simp only [h1, ↓reduceIte]
    dsimp only [Reg64s.beeuX] at h_x_even ⊢
    kprologue beeu_mod_inverse_vartime at ".Lshift1_0" to ".Lbeeu_shift_A_Y" with s
    have h_x13_bv : X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have h_shift := shift1_val320 X3 X4 X5 X6 X7
    have h_x3_mod : (X3.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X3 X4 X5 X6 X7]; exact h_x_even
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only at h_shift ⊢
    simp only [extr_sem_eq, ubfm_lsr1_sem_eq]
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, ?_,
      trivial, trivial, trivial, trivial, trivial, trivial, by omega⟩
    rw [UInt64.toNat_ofBitVec, h_x13_bv]; rfl
  · simp only [h1, ↓reduceIte]
    have h_gt1 : 1 < s.regs.X13.toNat := by omega
    dsimp only [Reg64s.beeuX] at h_x_even ⊢
    kprologue beeu_mod_inverse_vartime at ".Lshift1_0" to ".Lbeeu_shift_A_Y" with s
    have h_nz := sub_one_beq_zero_false_of_gt_one X13 h_gt1
    have h_dec := toNat_sub_one_of_pos X13 h_x13_pos
    have h_shift := shift1_val320 X3 X4 X5 X6 X7
    have h_x3_mod : (X3.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X3 X4 X5 X6 X7]; exact h_x_even
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only at h_shift h_dec ⊢
    simp only [extr_sem_eq, ubfm_lsr1_sem_eq]
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, h_dec,
      trivial, trivial, trivial, trivial, trivial, trivial, by omega⟩

theorem beeu_shift_loop_X_step_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X")
      (pre :=
        0 < s.regs.X13.toNat ∧
        s.regs.X14 = 0 ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuX + s.regs.beeuN < 256 ^ 40)
      (post := fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y"
        else
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X") ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        (2 * st.data.regs.beeuX) % s.regs.beeuN = s.regs.beeuX % s.regs.beeuN ∧
        2 * st.data.regs.beeuX ≤ s.regs.beeuX + s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_xn_lt⟩
  apply (beeu_shift_loop_X_pre_correct s ⟨h14, hN_odd, h_xn_lt⟩).bind
  rintro ⟨mid, mid_pc⟩ ⟨rfl, h_sp, h_x29, h_x13, h_x14, h_B, h_A, h_N, h_Y, h_dmem, h_even, h_mod, h_le⟩
  dsimp only at h_sp h_x29 h_x13 h_x14 h_B h_A h_N h_Y h_dmem h_even h_mod h_le
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_shift1_0_correct mid ⟨h_x13.symm ▸ h_x13_pos, h_even⟩)
  rintro fin ⟨h_pc, h_sp', h_x29', h_x13', h_x14', h_B', h_A', h_N', h_Y', h_dmem', h_2x⟩
  rw [h_x13] at h_pc h_x13'
  refine ⟨h_pc, h_sp'.trans h_sp, h_x29'.trans h_x29, h_x13', h_x14'.trans h_x14,
    h_B'.trans h_B, h_A'.trans h_A, h_N'.trans h_N, h_Y'.trans h_Y, h_dmem'.trans h_dmem, ?_, ?_⟩
  · rw [h_2x, h_mod]
  · omega

theorem beeu_shift_loop_X_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X")
      (pre :=
        0 < s.regs.X13.toNat ∧
        s.regs.X14 = 0 ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuX + s.regs.beeuN < 256 ^ 40)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        (((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
          s.regs.beeuX % s.regs.beeuN ∧
        st.data.regs.beeuX < 256 ^ 40 / 2) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_xn_lt⟩
  let k₀ := s.regs.X13.toNat
  apply tailrec_loop (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X" ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      st.data.regs.X14 = 0 ∧
      st.data.regs.SP = s.regs.SP ∧
      st.data.regs.X29 = s.regs.X29 ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.regs.beeuY = s.regs.beeuY ∧
      st.data.dmem = s.dmem ∧
      st.data.regs.beeuX + s.regs.beeuN < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
        s.regs.beeuX % s.regs.beeuN)
    (Q := fun (_ : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y" ∧
      st.data.regs.SP = s.regs.SP ∧
      st.data.regs.X29 = s.regs.X29 ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.regs.beeuY = s.regs.beeuY ∧
      st.data.dmem = s.dmem ∧
      (((2 ^ k₀ : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
        s.regs.beeuX % s.regs.beeuN ∧
      st.data.regs.beeuX < 256 ^ 40 / 2)
    (lt := (· < ·))
    (Hwf := Nat.lt_wfRel.wf)
    (v0 := k₀)
    (g0 := ())
  · refine ⟨rfl, h_x13_pos, Nat.le_refl _, rfl, h14, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h_xn_lt, ?_⟩
    simp
  · rintro v _ ⟨st, st_pc⟩ ⟨rfl, hv_pos, hv_le, h_x13, h_x14, h_sp, h_x29, h_B, h_A, h_N, h_Y, h_dmem, h_xn, h_inv⟩
    dsimp only at h_x13 h_x14 h_sp h_x29 h_B h_A h_N h_Y h_dmem h_xn h_inv
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_X_step_correct st
        ⟨h_x13 ▸ hv_pos, h_x14, h_N.symm ▸ hN_odd, h_N.symm ▸ h_xn⟩)
    rintro mid ⟨h_pc, h_sp', h_x29', h_x13', h_x14', h_B', h_A', h_N', h_Y', h_dmem', h_mod', h_2x'⟩
    rw [h_x13] at h_pc h_x13'
    rw [h_N] at h_mod' h_2x'
    by_cases hv1 : v = 1
    · simp only [hv1, ↓reduceIte] at h_pc
      left
      refine ⟨h_pc, h_sp'.trans h_sp, h_x29'.trans h_x29, h_B'.trans h_B, h_A'.trans h_A,
        h_N'.trans h_N, h_Y'.trans h_Y, h_dmem'.trans h_dmem, ?_, by omega⟩
      have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
      have h_k : k₀ - v + 1 = k₀ := by omega
      rw [h_k] at h_step
      exact h_step
    · simp only [hv1, ↓reduceIte] at h_pc
      right
      refine ⟨v - 1, (), ⟨h_pc, by omega, by omega, h_x13', h_x14', h_sp'.trans h_sp, h_x29'.trans h_x29,
        h_B'.trans h_B, h_A'.trans h_A, h_N'.trans h_N, h_Y'.trans h_Y, h_dmem'.trans h_dmem,
        by omega, ?_⟩, by omega, fun _ hQ => hQ⟩
      have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
      have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
      rw [← h_k]
      exact h_step
  · intro st hQ
    exact hQ

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_shift_loop_Y_pre_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y")
      (pre :=
        s.regs.X14 = 0 ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuY + s.regs.beeuN < 256 ^ 40)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lshift1_1" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X13 = s.regs.X13 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.dmem = s.dmem ∧
        st.data.regs.beeuY % 2 = 0 ∧
        st.data.regs.beeuY % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
        st.data.regs.beeuY ≤ s.regs.beeuY + s.regs.beeuN) := by
  rintro ⟨h14, hN_odd, h_yn_lt⟩
  dsimp only [Reg64s.beeuY, Reg64s.beeuN] at hN_odd h_yn_lt ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_loop_Y" to ".Lshift1_1" with s
  cases h_lsb : X8.toBitVec.getLsbD 0
  · have h_mod2 := getLsbD_zero_eq_false_mod2 X8 h_lsb
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only
    refine ⟨by kaddr beeu_mod_inverse_vartime, rfl, rfl, rfl, h14, rfl, rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
    · rw [val320_emod_two]; omega
    · have := val256_nonneg X0 X1 X2 X30; omega
  · have h_mod2 := getLsbD_zero_eq_true_mod2 X8 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_lt320 : val320 X8 X9 X10 X11 X12 + val320 X0 X1 X2 X30 X14 < 256 ^ 40 := by
      subst h14; dsimp only [val320, val256] at h_yn_lt ⊢; omega
    have h_add := add320_val_of_lt X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_lt320
    have h_n320 : val320 X0 X1 X2 X30 X14 = val256 X0 X1 X2 X30 := by
      subst h14; dsimp only [val320, val256]; omega
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only [add0Carry, adcCarry, add0Word, adcWord] at h_add ⊢
    simp only [BitVec.shiftLeft_zero, UInt64.toNat_toBitVec] at h_add ⊢
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, trivial, h14,
      trivial, trivial, trivial, trivial, trivial, ?_, ?_, ?_⟩
    · rw [h_add, h_n320]
      have hy := val320_emod_two X8 X9 X10 X11 X12
      omega
    · rw [h_add, h_n320, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]
    · rw [h_add, h_n320]
      omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_shift1_1_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lshift1_1")
      (pre :=
        0 < s.regs.X13.toNat ∧
        s.regs.beeuY % 2 = 0)
      (post := fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y"
        else
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y") ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.dmem = s.dmem ∧
        2 * st.data.regs.beeuY = s.regs.beeuY) := by
  rintro ⟨h_x13_pos, h_y_even⟩
  by_cases h1 : s.regs.X13.toNat = 1
  · simp only [h1, ↓reduceIte]
    dsimp only [Reg64s.beeuY] at h_y_even ⊢
    kprologue beeu_mod_inverse_vartime at ".Lshift1_1" to ".Lbeeu_update_B_X_or_A_Y" with s
    have h_x13_bv : X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have h_shift := shift1_val320 X8 X9 X10 X11 X12
    have h_x8_mod : (X8.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X8 X9 X10 X11 X12]; exact h_y_even
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only at h_shift ⊢
    simp only [extr_sem_eq, ubfm_lsr1_sem_eq]
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, ?_,
      trivial, trivial, trivial, trivial, trivial, trivial, by omega⟩
    rw [UInt64.toNat_ofBitVec, h_x13_bv]; rfl
  · simp only [h1, ↓reduceIte]
    have h_gt1 : 1 < s.regs.X13.toNat := by omega
    dsimp only [Reg64s.beeuY] at h_y_even ⊢
    kprologue beeu_mod_inverse_vartime at ".Lshift1_1" to ".Lbeeu_update_B_X_or_A_Y" with s
    have h_nz := sub_one_beq_zero_false_of_gt_one X13 h_gt1
    have h_dec := toNat_sub_one_of_pos X13 h_x13_pos
    have h_shift := shift1_val320 X8 X9 X10 X11 X12
    have h_x8_mod : (X8.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X8 X9 X10 X11 X12]; exact h_y_even
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only at h_shift h_dec ⊢
    simp only [extr_sem_eq, ubfm_lsr1_sem_eq]
    refine ⟨by kaddr beeu_mod_inverse_vartime, trivial, trivial, h_dec,
      trivial, trivial, trivial, trivial, trivial, trivial, by omega⟩

theorem beeu_shift_loop_Y_step_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y")
      (pre :=
        0 < s.regs.X13.toNat ∧
        s.regs.X14 = 0 ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuY + s.regs.beeuN < 256 ^ 40)
      (post := fun st =>
        st.pc = (if s.regs.X13.toNat = 1 then
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y"
        else
          (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y") ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.dmem = s.dmem ∧
        (2 * st.data.regs.beeuY) % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
        2 * st.data.regs.beeuY ≤ s.regs.beeuY + s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_yn_lt⟩
  apply (beeu_shift_loop_Y_pre_correct s ⟨h14, hN_odd, h_yn_lt⟩).bind
  rintro ⟨mid, mid_pc⟩ ⟨rfl, h_sp, h_x29, h_x13, h_x14, h_B, h_A, h_N, h_X, h_dmem, h_even, h_mod, h_le⟩
  dsimp only at h_sp h_x29 h_x13 h_x14 h_B h_A h_N h_X h_dmem h_even h_mod h_le
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_shift1_1_correct mid ⟨h_x13.symm ▸ h_x13_pos, h_even⟩)
  rintro fin ⟨h_pc, h_sp', h_x29', h_x13', h_x14', h_B', h_A', h_N', h_X', h_dmem', h_2y⟩
  rw [h_x13] at h_pc h_x13'
  refine ⟨h_pc, h_sp'.trans h_sp, h_x29'.trans h_x29, h_x13', h_x14'.trans h_x14,
    h_B'.trans h_B, h_A'.trans h_A, h_N'.trans h_N, h_X'.trans h_X, h_dmem'.trans h_dmem, ?_, ?_⟩
  · rw [h_2y, h_mod]
  · omega

theorem beeu_shift_loop_Y_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y")
      (pre :=
        0 < s.regs.X13.toNat ∧
        s.regs.X14 = 0 ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuY + s.regs.beeuN < 256 ^ 40)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.dmem = s.dmem ∧
        (((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
          s.regs.beeuY % s.regs.beeuN ∧
        st.data.regs.beeuY < 256 ^ 40 / 2) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_yn_lt⟩
  let k₀ := s.regs.X13.toNat
  apply tailrec_loop (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y" ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      st.data.regs.X14 = 0 ∧
      st.data.regs.SP = s.regs.SP ∧
      st.data.regs.X29 = s.regs.X29 ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.regs.beeuX = s.regs.beeuX ∧
      st.data.dmem = s.dmem ∧
      st.data.regs.beeuY + s.regs.beeuN < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
        s.regs.beeuY % s.regs.beeuN)
    (Q := fun (_ : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y" ∧
      st.data.regs.SP = s.regs.SP ∧
      st.data.regs.X29 = s.regs.X29 ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.regs.beeuX = s.regs.beeuX ∧
      st.data.dmem = s.dmem ∧
      (((2 ^ k₀ : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
        s.regs.beeuY % s.regs.beeuN ∧
      st.data.regs.beeuY < 256 ^ 40 / 2)
    (lt := (· < ·))
    (Hwf := Nat.lt_wfRel.wf)
    (v0 := k₀)
    (g0 := ())
  · refine ⟨rfl, h_x13_pos, Nat.le_refl _, rfl, h14, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h_yn_lt, ?_⟩
    simp
  · rintro v _ ⟨st, st_pc⟩ ⟨rfl, hv_pos, hv_le, h_x13, h_x14, h_sp, h_x29, h_B, h_A, h_N, h_X, h_dmem, h_yn, h_inv⟩
    dsimp only at h_x13 h_x14 h_sp h_x29 h_B h_A h_N h_X h_dmem h_yn h_inv
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_Y_step_correct st
        ⟨h_x13 ▸ hv_pos, h_x14, h_N.symm ▸ hN_odd, h_N.symm ▸ h_yn⟩)
    rintro mid ⟨h_pc, h_sp', h_x29', h_x13', h_x14', h_B', h_A', h_N', h_X', h_dmem', h_mod', h_2y'⟩
    rw [h_x13] at h_pc h_x13'
    rw [h_N] at h_mod' h_2y'
    by_cases hv1 : v = 1
    · simp only [hv1, ↓reduceIte] at h_pc
      left
      refine ⟨h_pc, h_sp'.trans h_sp, h_x29'.trans h_x29, h_B'.trans h_B, h_A'.trans h_A,
        h_N'.trans h_N, h_X'.trans h_X, h_dmem'.trans h_dmem, ?_, by omega⟩
      have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
      have h_k : k₀ - v + 1 = k₀ := by omega
      rw [h_k] at h_step
      exact h_step
    · simp only [hv1, ↓reduceIte] at h_pc
      right
      refine ⟨v - 1, (), ⟨h_pc, by omega, by omega, h_x13', h_x14', h_sp'.trans h_sp, h_x29'.trans h_x29,
        h_B'.trans h_B, h_A'.trans h_A, h_N'.trans h_N, h_X'.trans h_X, h_dmem'.trans h_dmem,
        by omega, ?_⟩, by omega, fun _ hQ => hQ⟩
      have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
      have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
      rw [← h_k]
      exact h_step
  · intro st hQ
    exact hQ

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_shift_B_header_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre := 0 < s.regs.beeuB)
      (post := fun st =>
        let k := ctzClamped s.regs.X25
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        if k = 0#64 then
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y" ∧
          st.data.regs.beeuB = s.regs.beeuB
        else
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X" ∧
          st.data.regs.X13.toNat = k.toNat ∧
          0 < k.toNat ∧
          st.data.regs.X14 = 0 ∧
          ((2 ^ k.toNat : Nat) : Int) * st.data.regs.beeuB = s.regs.beeuB) := by
  intro hB_pos
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte]
    dsimp only [Reg64s.beeuB, ctzClamped] at hB_pos hk ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_loop_X" with s
    have h_nz := val256_pos_or_ne_zero X25 X26 X27 X28 hB_pos
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by kaddr beeu_mod_inverse_vartime, rfl⟩
  · simp only [hk, ↓reduceIte]
    dsimp only [Reg64s.beeuB, ctzClamped] at hB_pos hk ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_loop_X" with s
    have h_nz := val256_pos_or_ne_zero X25 X26 X27 X28 hB_pos
    have hk_beq : ((X25.toBitVec.reverse ||| 1#64).clz == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hk
    have h_shift := shift256_val256 X25 X26 X27 X28 hk
    have hk_pos : 0 < (X25.toBitVec.reverse ||| 1#64).clz.toNat := by
      have : (X25.toBitVec.reverse ||| 1#64).clz.toNat ≠ 0 :=
        fun h0 => hk (BitVec.eq_of_toNat_eq h0)
      omega
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only [ctzClamped, shift256Word, shift256TopWord] at h_shift ⊢
    simp only [BitVec.shiftLeft_zero, BitVec.xor_self] at h_shift ⊢
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      by kaddr beeu_mod_inverse_vartime, rfl, hk_pos, rfl, h_shift⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem beeu_shift_A_header_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y")
      (pre := True)
      (post := fun st =>
        let k := ctzClamped s.regs.X21
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        if k = 0#64 then
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y" ∧
          st.data.regs.beeuA = s.regs.beeuA
        else
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y" ∧
          st.data.regs.X13.toNat = k.toNat ∧
          0 < k.toNat ∧
          st.data.regs.X14 = 0 ∧
          ((2 ^ k.toNat : Nat) : Int) * st.data.regs.beeuA = s.regs.beeuA) := by
  intro _
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte]
    dsimp only [Reg64s.beeuA, ctzClamped] at hk ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_A_Y" to ".Lbeeu_shift_loop_Y" with s
    sym => kstep; tactic =>
    apply Eventually.done
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by kaddr beeu_mod_inverse_vartime, rfl⟩
  · simp only [hk, ↓reduceIte]
    dsimp only [Reg64s.beeuA, ctzClamped] at hk ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_A_Y" to ".Lbeeu_shift_loop_Y" with s
    have hk_beq : ((X21.toBitVec.reverse ||| 1#64).clz == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hk
    have h_shift := shift256_val256 X21 X22 X23 X24 hk
    have hk_pos : 0 < (X21.toBitVec.reverse ||| 1#64).clz.toNat := by
      have : (X21.toBitVec.reverse ||| 1#64).clz.toNat ≠ 0 :=
        fun h0 => hk (BitVec.eq_of_toNat_eq h0)
      omega
    sym => kstep; tactic =>
    apply Eventually.done
    dsimp +zetaDelta only [ctzClamped, shift256Word, shift256TopWord] at h_shift ⊢
    simp only [BitVec.shiftLeft_zero, BitVec.xor_self] at h_shift ⊢
    exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      by kaddr beeu_mod_inverse_vartime, rfl, hk_pos, rfl, h_shift⟩

theorem two_mul_emod_eq_zero_of_odd (z n : Int) (hn_odd : n % 2 = 1)
    (h : (2 * z) % n = 0) : z % n = 0 := by
  obtain ⟨q, hq⟩ : n ∣ 2 * z := Int.dvd_of_emod_eq_zero h
  have hn_eq : n = 2 * (n / 2) + 1 := by omega
  have hz : z = n * (z - (n / 2) * q) + (2 * z - n * q) * (n / 2) := by grind
  have h2z : 2 * z - n * q = 0 := by omega
  rw [h2z, Int.zero_mul, Int.add_zero] at hz
  exact Int.emod_eq_zero_of_dvd ⟨z - (n / 2) * q, hz⟩

theorem pow2_mul_emod_eq_zero_of_odd (k : Nat) (z n : Int) (hn_odd : n % 2 = 1)
    (h : (((2 ^ k : Nat) : Int) * z) % n = 0) : z % n = 0 := by
  induction k generalizing z with
  | zero =>
    simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul] at h
    exact h
  | succ k ih =>
    apply ih z
    apply two_mul_emod_eq_zero_of_odd (((2 ^ k : Nat) : Int) * z) n hn_odd
    have h_eq : 2 * (((2 ^ k : Nat) : Int) * z) = ((2 ^ (k + 1) : Nat) : Int) * z := by
      rw [Nat.pow_succ, Int.natCast_mul]; grind
    rw [h_eq]
    exact h

theorem pos_and_le_of_pow2_mul (k : Nat) (b b' : Int)
    (hb_pos : 0 < b) (hb'_nonneg : 0 ≤ b')
    (h_eq : ((2 ^ k : Nat) : Int) * b' = b) :
    0 < b' ∧ b' ≤ b := by
  have h_pow_nat : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
  have h_pow_pos : (1 : Int) ≤ ((2 ^ k : Nat) : Int) := by omega
  have hb'_pos : 0 < b' := by
    rcases Int.lt_trichotomy 0 b' with h_pos | h_zero | h_neg
    · exact h_pos
    · rw [← h_zero, Int.mul_zero] at h_eq; omega
    · omega
  have hb'_le : b' ≤ b := by
    have : 1 * b' ≤ ((2 ^ k : Nat) : Int) * b' :=
      Int.mul_le_mul_of_nonneg_right h_pow_pos hb'_nonneg
    omega
  exact ⟨hb'_pos, hb'_le⟩

theorem shift_B_X_mod_inv (k : Nat) (a B B' X X' n : Int)
    (hn_odd : n % 2 = 1)
    (hB : ((2 ^ k : Nat) : Int) * B' = B)
    (hX : (((2 ^ k : Nat) : Int) * X') % n = X % n)
    (h_inv : (a * X - B) % n = 0) :
    (a * X' - B') % n = 0 := by
  apply pow2_mul_emod_eq_zero_of_odd k (a * X' - B') n hn_odd
  have h_lin : ((2 ^ k : Nat) : Int) * (a * X' - B') =
      a * (((2 ^ k : Nat) : Int) * X') - B := by
    rw [← hB]; grind
  rw [h_lin, Int.sub_emod, Int.mul_emod a, hX, ← Int.mul_emod, ← Int.sub_emod, h_inv]

theorem shift_A_Y_mod_inv (k : Nat) (a A A' Y Y' n : Int)
    (hn_odd : n % 2 = 1)
    (hA : ((2 ^ k : Nat) : Int) * A' = A)
    (hY : (((2 ^ k : Nat) : Int) * Y') % n = Y % n)
    (h_inv : (a * Y + A) % n = 0) :
    (a * Y' + A') % n = 0 := by
  apply pow2_mul_emod_eq_zero_of_odd k (a * Y' + A') n hn_odd
  have h_lin : ((2 ^ k : Nat) : Int) * (a * Y' + A') =
      a * (((2 ^ k : Nat) : Int) * Y') + A := by
    rw [← hA]; grind
  rw [h_lin, Int.add_emod, Int.mul_emod a, hY, ← Int.mul_emod, ← Int.add_emod, h_inv]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Full verification of the `B`/`X` shift phase (`.Lbeeu_loop` to `.Lbeeu_shift_A_Y` when `B > 0`):
    shifts `B` right by `k = ctzClamped(b0)` bits and divides `X` by `2^k` modulo `N`. -/
theorem beeu_shift_B_X_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre :=
        0 < s.regs.beeuB ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuX < 256 ^ 40 / 2 ∧
        (a * s.regs.beeuX - s.regs.beeuB) % s.regs.beeuN = 0)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.dmem = s.dmem ∧
        0 < st.data.regs.beeuB ∧
        st.data.regs.beeuB ≤ s.regs.beeuB ∧
        st.data.regs.beeuX < 256 ^ 40 / 2 ∧
        (a * st.data.regs.beeuX - st.data.regs.beeuB) % s.regs.beeuN = 0) := by
  rintro ⟨hB_pos, hN_odd, hX_lt, h_inv⟩
  apply (beeu_shift_B_header_correct s hB_pos).bind
  rintro ⟨mid, mid_pc⟩ ⟨h_sp, h_x29, h_A, h_N, h_X, h_Y, h_dmem, h_branch⟩
  dsimp only at h_sp h_x29 h_A h_N h_X h_Y h_dmem h_branch
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_B⟩
    apply Eventually.done
    dsimp only
    exact ⟨h_pc, h_sp, h_x29, h_A, h_N, h_Y, h_dmem,
      h_B.symm ▸ hB_pos, by omega, h_X.symm ▸ hX_lt, by rw [h_X, h_B]; exact h_inv⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_x13, hk_pos, h_x14, h_B_shift⟩
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    have h_xn_lt : mid.regs.beeuX + mid.regs.beeuN < 256 ^ 40 := by omega
    subst h_pc
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_X_correct mid
        ⟨h_x13 ▸ hk_pos, h_x14, h_N.symm ▸ hN_odd, h_xn_lt⟩)
    rintro fin ⟨h_fin_pc, h_fin_sp, h_fin_x29, h_fin_B, h_fin_A, h_fin_N, h_fin_Y,
      h_fin_dmem, h_fin_X_mod, h_fin_X_lt⟩
    have hB_nonneg : 0 ≤ fin.data.regs.beeuB := val256_nonneg _ _ _ _
    have ⟨hB'_pos, hB'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X25).toNat s.regs.beeuB fin.data.regs.beeuB
      hB_pos hB_nonneg (h_fin_B.symm ▸ h_B_shift)
    refine ⟨h_fin_pc, h_fin_sp.trans h_sp, h_fin_x29.trans h_x29,
      h_fin_A.trans h_A, h_fin_N.trans h_N, h_fin_Y.trans h_Y, h_fin_dmem.trans h_dmem,
      hB'_pos, hB'_le, h_fin_X_lt, ?_⟩
    rw [h_x13, h_N, h_X] at h_fin_X_mod
    exact shift_B_X_mod_inv (ctzClamped s.regs.X25).toNat a
      s.regs.beeuB fin.data.regs.beeuB s.regs.beeuX fin.data.regs.beeuX s.regs.beeuN
      hN_odd (h_fin_B.symm ▸ h_B_shift) h_fin_X_mod h_inv

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Full verification of the `A`/`Y` shift phase (`.Lbeeu_shift_A_Y` to `.Lbeeu_update_B_X_or_A_Y`):
    shifts `A` right by `k = ctzClamped(a0)` bits and divides `Y` by `2^k` modulo `N`. -/
theorem beeu_shift_A_Y_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y")
      (pre :=
        0 < s.regs.beeuA ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuY < 256 ^ 40 / 2 ∧
        (a * s.regs.beeuY + s.regs.beeuA) % s.regs.beeuN = 0)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.dmem = s.dmem ∧
        0 < st.data.regs.beeuA ∧
        st.data.regs.beeuA ≤ s.regs.beeuA ∧
        st.data.regs.beeuY < 256 ^ 40 / 2 ∧
        (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0) := by
  rintro ⟨hA_pos, hN_odd, hY_lt, h_inv⟩
  apply (beeu_shift_A_header_correct s trivial).bind
  rintro ⟨mid, mid_pc⟩ ⟨h_sp, h_x29, h_B, h_N, h_X, h_Y, h_dmem, h_branch⟩
  dsimp only at h_sp h_x29 h_B h_N h_X h_Y h_dmem h_branch
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_A⟩
    apply Eventually.done
    dsimp only
    exact ⟨h_pc, h_sp, h_x29, h_B, h_N, h_X, h_dmem,
      h_A.symm ▸ hA_pos, by omega, h_Y.symm ▸ hY_lt, by rw [h_Y, h_A]; exact h_inv⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_x13, hk_pos, h_x14, h_A_shift⟩
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    have h_yn_lt : mid.regs.beeuY + mid.regs.beeuN < 256 ^ 40 := by omega
    subst h_pc
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_Y_correct mid
        ⟨h_x13 ▸ hk_pos, h_x14, h_N.symm ▸ hN_odd, h_yn_lt⟩)
    rintro fin ⟨h_fin_pc, h_fin_sp, h_fin_x29, h_fin_B, h_fin_A, h_fin_N, h_fin_X,
      h_fin_dmem, h_fin_Y_mod, h_fin_Y_lt⟩
    have hA_nonneg : 0 ≤ fin.data.regs.beeuA := val256_nonneg _ _ _ _
    have ⟨hA'_pos, hA'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X21).toNat s.regs.beeuA fin.data.regs.beeuA
      hA_pos hA_nonneg (h_fin_A.symm ▸ h_A_shift)
    refine ⟨h_fin_pc, h_fin_sp.trans h_sp, h_fin_x29.trans h_x29,
      h_fin_B.trans h_B, h_fin_N.trans h_N, h_fin_X.trans h_X, h_fin_dmem.trans h_dmem,
      hA'_pos, hA'_le, h_fin_Y_lt, ?_⟩
    rw [h_x13, h_N, h_Y] at h_fin_Y_mod
    exact shift_A_Y_mod_inv (ctzClamped s.regs.X21).toNat a
      s.regs.beeuA fin.data.regs.beeuA s.regs.beeuY fin.data.regs.beeuY s.regs.beeuN
      hN_odd (h_fin_A.symm ▸ h_A_shift) h_fin_Y_mod h_inv

/-! ## 6. Outer Loop & Top-Level `beeu_mod_inverse_vartime` Specification -/

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- One full iteration of `.Lbeeu_loop` when `0 < B`:
    executes `beeu_shift_B_X`, `beeu_shift_A_Y`, and `.Lbeeu_update_B_X_or_A_Y`,
    returning to `.Lbeeu_loop` with strictly smaller `(B + A).toNat` and preserving
    both modular invariants `(a * X - B) % N = 0` and `(a * Y + A) % N = 0`. -/
theorem beeu_loop_body_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre :=
        0 < s.regs.beeuB ∧
        0 < s.regs.beeuA ∧
        s.regs.beeuN % 2 = 1 ∧
        s.regs.beeuX < 256 ^ 40 / 2 ∧
        s.regs.beeuY < 256 ^ 40 / 2 ∧
        (a * s.regs.beeuX - s.regs.beeuB) % s.regs.beeuN = 0 ∧
        (a * s.regs.beeuY + s.regs.beeuA) % s.regs.beeuN = 0)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.dmem = s.dmem ∧
        0 ≤ st.data.regs.beeuB ∧
        st.data.regs.beeuB ≤ s.regs.beeuB ∧
        0 < st.data.regs.beeuA ∧
        st.data.regs.beeuA ≤ s.regs.beeuA ∧
        (st.data.regs.beeuB + st.data.regs.beeuA).toNat <
          (s.regs.beeuB + s.regs.beeuA).toNat ∧
        (a * st.data.regs.beeuX - st.data.regs.beeuB) % s.regs.beeuN = 0 ∧
        (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0) := by
  rintro ⟨hB_pos, hA_pos, hN_odd, hX_lt, hY_lt, hX_inv, hY_inv⟩
  apply (beeu_shift_B_X_correct s a ⟨hB_pos, hN_odd, hX_lt, hX_inv⟩).bind
  rintro ⟨st1, st1_pc⟩ ⟨h1_pc, h1_sp, h1_x29, h1_A, h1_N, h1_Y, h1_dmem,
    h1_B_pos, h1_B_le, h1_X_lt, h1_X_inv⟩
  dsimp only at h1_pc h1_sp h1_x29 h1_A h1_N h1_Y h1_dmem h1_B_pos h1_B_le h1_X_lt h1_X_inv
  subst h1_pc
  apply (beeu_shift_A_Y_correct st1 a
    ⟨h1_A.symm ▸ hA_pos, h1_N.symm ▸ hN_odd, h1_Y.symm ▸ hY_lt, by
      rw [h1_Y, h1_A, h1_N]; exact hY_inv⟩).bind
  rintro ⟨st2, st2_pc⟩ ⟨h2_pc, h2_sp, h2_x29, h2_B, h2_N, h2_X, h2_dmem,
    h2_A_pos, h2_A_le, h2_Y_lt, h2_Y_inv⟩
  dsimp only at h2_pc h2_sp h2_x29 h2_B h2_N h2_X h2_dmem h2_A_pos h2_A_le h2_Y_lt h2_Y_inv
  subst h2_pc
  have h_xy_lt : st2.regs.beeuX + st2.regs.beeuY < 256 ^ 40 := by omega
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_update_step_correct st2 h_xy_lt)
  rintro fin ⟨h3_pc, h3_sp, h3_x29, h3_N, h3_dmem, h3_branch, _⟩
  have h2_B_pos : 0 < st2.regs.beeuB := h2_B.symm ▸ h1_B_pos
  have h2_B_le : st2.regs.beeuB ≤ s.regs.beeuB := h2_B.symm ▸ h1_B_le
  have h2_A_le' : st2.regs.beeuA ≤ s.regs.beeuA := h1_A ▸ h2_A_le
  have h2_X_inv : (a * st2.regs.beeuX - st2.regs.beeuB) % s.regs.beeuN = 0 := by
    rw [h2_X, h2_B]; exact h1_X_inv
  have h2_Y_inv' : (a * st2.regs.beeuY + st2.regs.beeuA) % s.regs.beeuN = 0 := by
    rw [← h1_N]; exact h2_Y_inv
  refine ⟨h3_pc, h3_sp.trans (h2_sp.trans h1_sp), h3_x29.trans (h2_x29.trans h1_x29),
    h3_N.trans (h2_N.trans h1_N), h3_dmem.trans (h2_dmem.trans h1_dmem), ?_⟩
  by_cases h_ge : st2.regs.beeuB ≥ st2.regs.beeuA
  · simp only [h_ge, ↓reduceIte] at h3_branch
    rcases h3_branch with ⟨hB', hA', hX', hY'⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · have h_lin : a * fin.data.regs.beeuX - fin.data.regs.beeuB =
          (a * st2.regs.beeuX - st2.regs.beeuB) + (a * st2.regs.beeuY + st2.regs.beeuA) := by
        rw [hX', hB']; grind
      rw [h_lin, Int.add_emod, h2_X_inv, h2_Y_inv']
      simp
    · rw [hY', hA']; exact h2_Y_inv'
  · simp only [h_ge, ↓reduceIte] at h3_branch
    rcases h3_branch with ⟨hB', hA', hX', hY'⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · rw [hX', hB']; exact h2_X_inv
    · have h_lin : a * fin.data.regs.beeuY + fin.data.regs.beeuA =
          (a * st2.regs.beeuY + st2.regs.beeuA) + (a * st2.regs.beeuX - st2.regs.beeuB) := by
        rw [hY', hA']; grind
      rw [h_lin, Int.add_emod, h2_Y_inv', h2_X_inv]
      simp

/-- In BoringSSL's 5-limb (320-bit) BEEU representation, the 5th limb (`x7` for `X`, `x12` for `Y`)
    acts as a 64-bit buffer limb above the 256-bit modulus `n` so that the accumulators `X` and `Y`
    remain below `2^319` (`256 ^ 40 / 2`) across `.Lbeeu_loop` iterations. -/
def BeeuNoOverflow319 (a n : Int) : Prop :=
  ∀ r : Reg64s,
    r.beeuN = n →
    0 < r.beeuB → r.beeuB ≤ n →
    0 < r.beeuA → r.beeuA ≤ n →
    (a * r.beeuX - r.beeuB) % n = 0 →
    (a * r.beeuY + r.beeuA) % n = 0 →
    r.beeuX < 256 ^ 40 / 2 ∧ r.beeuY < 256 ^ 40 / 2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Full verification of the outer binary extended Euclidean loop (`.Lbeeu_loop` to `.Lbeeu_loop_end`):
    terminates by well-founded induction on `(B + A).toNat`, exiting with `B = 0`, `0 < A ≤ A₀`,
    and `(a * Y + A) % N = 0`. -/
theorem beeu_loop_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre :=
        0 ≤ s.regs.beeuB ∧ s.regs.beeuB ≤ s.regs.beeuN ∧
        0 < s.regs.beeuA ∧ s.regs.beeuA ≤ s.regs.beeuN ∧
        s.regs.beeuN % 2 = 1 ∧
        (a * s.regs.beeuX - s.regs.beeuB) % s.regs.beeuN = 0 ∧
        (a * s.regs.beeuY + s.regs.beeuA) % s.regs.beeuN = 0 ∧
        BeeuNoOverflow319 a s.regs.beeuN)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        st.data.regs.SP = s.regs.SP ∧
        st.data.regs.X29 = s.regs.X29 ∧
        st.data.regs.beeuN = s.regs.beeuN ∧
        st.data.dmem = s.dmem ∧
        0 < st.data.regs.beeuA ∧
        st.data.regs.beeuA ≤ s.regs.beeuA ∧
        (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0) := by
  rintro ⟨hB_nonneg, hB_le, hA_pos, hA_le, hN_odd, hX_inv, hY_inv, h_no_ovf⟩
  apply tailrec_loop (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
      st.data.regs.SP = s.regs.SP ∧
      st.data.regs.X29 = s.regs.X29 ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.dmem = s.dmem ∧
      0 ≤ st.data.regs.beeuB ∧
      st.data.regs.beeuB ≤ s.regs.beeuN ∧
      0 < st.data.regs.beeuA ∧
      st.data.regs.beeuA ≤ s.regs.beeuA ∧
      (st.data.regs.beeuB + st.data.regs.beeuA).toNat = v ∧
      (a * st.data.regs.beeuX - st.data.regs.beeuB) % s.regs.beeuN = 0 ∧
      (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0)
    (Q := fun (_ : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
      st.data.regs.SP = s.regs.SP ∧
      st.data.regs.X29 = s.regs.X29 ∧
      st.data.regs.beeuN = s.regs.beeuN ∧
      st.data.dmem = s.dmem ∧
      0 < st.data.regs.beeuA ∧
      st.data.regs.beeuA ≤ s.regs.beeuA ∧
      (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0)
    (lt := (· < ·))
    (Hwf := Nat.lt_wfRel.wf)
    (v0 := (s.regs.beeuB + s.regs.beeuA).toNat)
    (g0 := ())
  · exact ⟨rfl, rfl, rfl, rfl, rfl, hB_nonneg, hB_le, hA_pos, Int.le_refl _, rfl, hX_inv, hY_inv⟩
  · rintro v _ ⟨st_data, st_pc⟩ ⟨rfl, hst_sp, hst_x29, hst_N, hst_dmem,
      hst_B_nonneg, hst_B_le, hst_A_pos, hst_A_le, hst_v, hst_X_inv, hst_Y_inv⟩
    dsimp only at hst_sp hst_x29 hst_N hst_dmem hst_B_nonneg hst_B_le hst_A_pos hst_A_le hst_v hst_X_inv hst_Y_inv
    by_cases hB0 : st_data.regs.beeuB = 0
    · apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_loop_exit_when_B_zero st_data hB0)
      rintro fin ⟨h_pc, h_sp', h_x29', h_A', h_N', _, h_Y', h_dmem'⟩
      left
      refine ⟨h_pc, h_sp'.trans hst_sp, h_x29'.trans hst_x29,
        h_N'.trans hst_N, h_dmem'.trans hst_dmem,
        h_A'.symm ▸ hst_A_pos, h_A'.symm ▸ hst_A_le, ?_⟩
      rw [h_Y', h_A']
      exact hst_Y_inv
    · have hst_B_pos : 0 < st_data.regs.beeuB := by omega
      have hst_A_le_N : st_data.regs.beeuA ≤ s.regs.beeuN := by omega
      have ⟨hX_lt, hY_lt⟩ := h_no_ovf st_data.regs hst_N
        hst_B_pos hst_B_le hst_A_pos hst_A_le_N hst_X_inv hst_Y_inv
      apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_loop_body_correct st_data a
          ⟨hst_B_pos, hst_A_pos, hst_N.symm ▸ hN_odd, hX_lt, hY_lt,
           hst_N.symm ▸ hst_X_inv, hst_N.symm ▸ hst_Y_inv⟩)
      rintro mid ⟨h_pc, h_sp', h_x29', h_N', h_dmem',
        h_B_nonneg', h_B_le', h_A_pos', h_A_le', h_lt', h_X_inv', h_Y_inv'⟩
      rw [hst_N] at h_X_inv' h_Y_inv'
      right
      refine ⟨(mid.data.regs.beeuB + mid.data.regs.beeuA).toNat, (),
        ⟨h_pc, h_sp'.trans hst_sp, h_x29'.trans hst_x29,
         h_N'.trans hst_N, h_dmem'.trans hst_dmem,
         h_B_nonneg', by omega, h_A_pos', by omega, rfl, h_X_inv', h_Y_inv'⟩,
        by omega, fun _ hQ => hQ⟩
  · intro st hQ
    exact hQ

theorem mod_inv_of_beeu_end (a y out n : Int)
    (hn_pos : 0 < n)
    (h_inv : (a * y + 1) % n = 0)
    (h_out : out = n - (y % n)) :
    0 < out ∧ out ≤ n ∧ (a * out) % n = 1 % n := by
  have hy_nonneg : 0 ≤ y % n := Int.emod_nonneg y (by omega)
  have hy_lt : y % n < n := Int.emod_lt_of_pos y hn_pos
  refine ⟨by omega, by omega, ?_⟩
  have h_sub_mod : (y - y % n) % n = 0 := by
    rw [Int.sub_emod, Int.emod_emod, Int.sub_self, Int.zero_emod]
  obtain ⟨q, hq⟩ : n ∣ a * y + 1 := Int.dvd_of_emod_eq_zero h_inv
  obtain ⟨k, hk⟩ : n ∣ y - y % n := Int.dvd_of_emod_eq_zero h_sub_mod
  have h_eq : a * out = 1 + (a - q + a * k) * n := by
    rw [h_out]; grind
  rw [h_eq, Int.add_emod, Int.mul_emod, Int.emod_self, Int.mul_zero,
    Int.zero_emod, Int.add_zero, Int.emod_emod]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- Top-level end-to-end functional correctness of BoringSSL's `beeu_mod_inverse_vartime`:
    Given a 16-byte-aligned stack with 112 bytes of frame space, 32-byte input buffers `a_bs` at `x1`
    and odd modulus `n_bs` at `x2` with `0 ≤ a ≤ n`, and a 32-byte output buffer at `x0`,
    `beeu_mod_inverse_vartime` terminates and returns to `x30` with `sp` and all callee-saved
    registers (`x19..x29`) restored, and:
    - either returns `x0 = 1` and writes 256-bit `out` (`0 < out ≤ n`) to the output buffer such that
      `(a * out) % n = 1 % n` (the modular inverse of `a` modulo `n`),
    - or returns `x0 = 0` (if the loop terminated with `A ≠ 1`) with the output buffer unchanged. -/
theorem beeu_mod_inverse_vartime_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) (stack a_bs n_bs : List UInt8) (o0 o1 o2 o3 : UInt64) (R : DataMem → Prop) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pre :=
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        let a := Int.ofBytes a_bs
        let n := Int.ofBytes n_bs
        s₀.regs.SP.toBitVec % 16#64 = 0#64 ∧
        stack.length = 112 ∧
        a_bs.length = 32 ∧
        n_bs.length = 32 ∧
        a ≤ n ∧
        0 < n ∧
        n % 2 = 1 ∧
        BeeuNoOverflow319 a n ∧
        (s₀.dmem =⋆
          stack @ sp' ⋆
          Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
          a_bs @ s₀.regs.X1 ⋆
          n_bs @ s₀.regs.X2 ⋆
          R))
      (post := fun st =>
        let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
        let a := Int.ofBytes a_bs
        let n := Int.ofBytes n_bs
        st.pc = Int64.ofInt s₀.regs.X30.toBitVec.toInt ∧
        st.data.regs.SP = s₀.regs.SP ∧
        st.data.regs.X30 = s₀.regs.X30 ∧
        st.data.regs.CalleeSavedEq s₀.regs ∧
        ((st.data.regs.X0 = 1 ∧
          ∃ w0 w1 w2 w3 : UInt64,
            0 < val256 w0 w1 w2 w3 ∧
            val256 w0 w1 w2 w3 ≤ n ∧
            (a * val256 w0 w1 w2 w3) % n = 1 % n ∧
            (st.data.dmem =⋆
              BeeuStackFrame s₀.regs sp' ⋆
              Words256At w0 w1 w2 w3 s₀.regs.X0.toBitVec ⋆
              a_bs @ s₀.regs.X1 ⋆
              n_bs @ s₀.regs.X2 ⋆
              R)) ∨
         (st.data.regs.X0 = 0 ∧
          (st.data.dmem =⋆
            BeeuStackFrame s₀.regs sp' ⋆
            Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
            a_bs @ s₀.regs.X1 ⋆
            n_bs @ s₀.regs.X2 ⋆
            R)))) := by
  rintro ⟨h_sp_align, h_stack_len, h_a_len, h_n_len, h_a_le, h_n_pos, h_n_odd, h_no_ovf, h_mem⟩
  let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
  let a := Int.ofBytes a_bs
  let n := Int.ofBytes n_bs
  have h_mem_pro : (s₀.dmem =⋆
      stack @ sp' ⋆ a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆
      (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)) := by
    ecancel
  apply (beeu_prologue_correct s₀ stack a_bs n_bs
    (Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆ R)
    ⟨h_sp_align, h_stack_len, h_a_len, h_n_len, h_mem_pro⟩).bind
  rintro ⟨st1, st1_pc⟩ ⟨h1_pc, h1_sp, h1_x29, h1_B, h1_A, h1_N, h1_X, h1_Y, h1_mem⟩
  dsimp only at h1_pc h1_sp h1_x29 h1_B h1_A h1_N h1_X h1_Y h1_mem
  subst h1_pc
  have h1_B_nonneg : 0 ≤ st1.regs.beeuB := val256_nonneg _ _ _ _
  have h1_X_inv : (a * st1.regs.beeuX - st1.regs.beeuB) % st1.regs.beeuN = 0 := by
    rw [h1_X, h1_B]; change (a * 1 - a) % st1.regs.beeuN = 0; simp
  have h1_Y_inv : (a * st1.regs.beeuY + st1.regs.beeuA) % st1.regs.beeuN = 0 := by
    rw [h1_Y, h1_A, h1_N]; change (a * 0 + n) % n = 0; simp
  apply (beeu_loop_correct st1 a
    ⟨h1_B_nonneg, by omega, by omega, by omega,
     h1_N.symm ▸ h_n_odd, h1_X_inv, h1_Y_inv, h1_N.symm ▸ h_no_ovf⟩).bind
  rintro ⟨st2, st2_pc⟩ ⟨h2_pc, h2_sp, h2_x29, h2_N, h2_dmem, h2_A_pos, h2_A_le, h2_Y_inv⟩
  dsimp only at h2_pc h2_sp h2_x29 h2_N h2_dmem h2_A_pos h2_A_le h2_Y_inv
  subst h2_pc
  have h2_sp_eq : st2.regs.SP = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_sp]; exact h1_sp)
  have h2_x29_eq : st2.regs.X29 = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_x29]; exact h1_x29)
  have h2_mem : (st2.dmem =⋆
      BeeuStackFrame s₀.regs sp' ⋆
      Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
      (a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)) := by
    rw [h2_dmem]; ecancel
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_loop_end_to_return_correct st2 s₀.regs o0 o1 o2 o3
      (a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)
      ⟨h_sp_align, h2_sp_eq, h2_x29_eq, by omega, h2_mem⟩)
  rintro fin ⟨h_fin_pc, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_branch⟩
  refine ⟨h_fin_pc, h_fin_sp, h_fin_x30, h_fin_cs, ?_⟩
  by_cases hA1 : st2.regs.beeuA = 1
  · simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
    left
    have h_inv1 : (a * st2.regs.beeuY + 1) % n = 0 := by
      rw [hA1, h1_N] at h2_Y_inv; exact h2_Y_inv
    have h_val_n : val256 w0 w1 w2 w3 = n - (st2.regs.beeuY % n) := by
      rw [h2_N, h1_N] at h_val; exact h_val
    have ⟨h_out_pos, h_out_le, h_out_inv⟩ :=
      mod_inv_of_beeu_end a st2.regs.beeuY (val256 w0 w1 w2 w3) n h_n_pos h_inv1 h_val_n
    exact ⟨h_x0, w0, w1, w2, w3, h_out_pos, h_out_le, h_out_inv, by ecancel⟩
  · simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, h_mem'⟩
    right
    exact ⟨h_x0, by ecancel⟩








