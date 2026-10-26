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
  kfinish beeu_mod_inverse_vartime [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX,
    Reg64s.beeuY, sp_sub_112_add_zero]
  · exact val256_of_limbs a_bs h_a_len
  · exact val256_of_limbs n_bs h_n_len
  · exact val256_of_limbs n_bs h_n_len

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

/-! ## Block Frame (facts preserved by every block of the main loop region) -/

/-- Machine-state facts preserved by every block of the main loop region of
`beeu_mod_inverse_vartime`: stack pointer, frame pointer, the modulus `N`, and data memory. -/
structure BlockFrame (s st : MachineData) : Prop where
  sp : st.regs.SP = s.regs.SP
  x29 : st.regs.X29 = s.regs.X29
  N : st.regs.beeuN = s.regs.beeuN
  dmem : st.dmem = s.dmem

theorem BlockFrame.refl (s : MachineData) : BlockFrame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem BlockFrame.trans {s₁ s₂ s₃ : MachineData} (h₁ : BlockFrame s₁ s₂) (h₂ : BlockFrame s₂ s₃) :
    BlockFrame s₁ s₃ :=
  ⟨h₂.sp.trans h₁.sp, h₂.x29.trans h₁.x29, h₂.N.trans h₁.N, h₂.dmem.trans h₁.dmem⟩

/-! ## 2. Loop Exit Verification (`.Lbeeu_loop` to `.Lbeeu_loop_end` when `B = 0`) -/

theorem beeu_loop_exit_when_B_zero [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre := s₀.regs.beeuB = 0)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        BlockFrame s₀ st.data ∧
        st.data.regs.beeuA = s₀.regs.beeuA ∧
        st.data.regs.beeuX = s₀.regs.beeuX ∧
        st.data.regs.beeuY = s₀.regs.beeuY) := by
  intro h_B_zero
  have ⟨h25, h26, h27, h28⟩ := val256_eq_zero_limbs
    s₀.regs.X25 s₀.regs.X26 s₀.regs.X27 s₀.regs.X28 h_B_zero
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_A_Y" with s₀
  sym => kstep; tactic =>
  kfinish beeu_mod_inverse_vartime

/-! ## 3. Loop Update Step Verification (`.Lbeeu_update_B_X_or_A_Y` to `.Lbeeu_loop`) -/

theorem beeu_update_step_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s₀ : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s₀
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y")
      (pre := s₀.regs.beeuX + s₀.regs.beeuY < 256 ^ 40)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
        BlockFrame s₀ st.data ∧
        if s₀.regs.beeuB ≥ s₀.regs.beeuA then
          st.data.regs.beeuB = s₀.regs.beeuB - s₀.regs.beeuA ∧
          st.data.regs.beeuA = s₀.regs.beeuA ∧
          st.data.regs.beeuX = s₀.regs.beeuX + s₀.regs.beeuY ∧
          st.data.regs.beeuY = s₀.regs.beeuY
        else
          st.data.regs.beeuB = s₀.regs.beeuB ∧
          st.data.regs.beeuA = s₀.regs.beeuA - s₀.regs.beeuB ∧
          st.data.regs.beeuX = s₀.regs.beeuX ∧
          st.data.regs.beeuY = s₀.regs.beeuY + s₀.regs.beeuX) := by
  intro h_xy_bound
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_update_B_X_or_A_Y" to ".Lbeeu_B_greater_than_A" with s₀
  by_cases h_ge : val256 X25 X26 X27 X28 ≥ val256 X21 X22 X23 X24
  · have h_carry := sub256_carry_of_ge X25 X26 X27 X28 X21 X22 X23 X24 h_ge
    have hB' := sub256_val_of_ge X25 X26 X27 X28 X21 X22 X23 X24 h_ge
    have hX' := add320_val_of_lt X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 h_xy_bound
    sym => kstep; tactic =>
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_B_greater_than_A" to ".Lbeeu_loop_end"
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX,
      Reg64s.beeuY, h_ge]
  · have h_lt : val256 X25 X26 X27 X28 < val256 X21 X22 X23 X24 := Int.lt_of_not_ge h_ge
    have h_le : val256 X21 X22 X23 X24 ≥ val256 X25 X26 X27 X28 := Int.le_of_lt h_lt
    have h_carry := sub256_carry_of_lt X25 X26 X27 X28 X21 X22 X23 X24 h_lt
    have h_yx_bound : val320 X8 X9 X10 X11 X12 + val320 X3 X4 X5 X6 X7 < 256 ^ 40 := by
      dsimp only [Reg64s.beeuX, Reg64s.beeuY] at h_xy_bound; omega
    have hA' := sub256_val_of_ge X21 X22 X23 X24 X25 X26 X27 X28 h_le
    have hY' := add320_val_of_lt X8 X9 X10 X11 X12 X3 X4 X5 X6 X7 h_yx_bound
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [Reg64s.beeuB, Reg64s.beeuA, Reg64s.beeuN, Reg64s.beeuX,
      Reg64s.beeuY, h_ge]

/-! ## 4. Epilogue & Modular Negation Verification (`.Lbeeu_err` and `.Lbeeu_reduction_loop` to Return) -/

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
  kfinish beeu_mod_inverse_vartime [BitVec.ofInt_ofBytes_toBytes_64, Reg64s.CalleeSavedEq]
  apply UInt64.eq_of_toBitVec_eq
  change (r₀.SP.toBitVec + 18446744073709551504#64 + 0#64) + 112#64 = r₀.SP.toBitVec
  grind

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
  kfinish beeu_mod_inverse_vartime [BitVec.ofInt_ofBytes_toBytes_64, Reg64s.CalleeSavedEq]
  apply UInt64.eq_of_toBitVec_eq
  change (r₀.SP.toBitVec + 18446744073709551504#64 + 0#64) + 112#64 = r₀.SP.toBitVec
  grind

theorem beeu_loop_end_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end")
      (pre := True)
      (post := fun st =>
        BlockFrame s st.data ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        if s.regs.beeuA = 1 then
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
          st.data.regs.X14 = 0
        else
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_err") := by
  intro _
  by_cases hA : s.regs.beeuA = 1
  · simp only [hA, ↓reduceIte]
    dsimp only [Reg64s.beeuA] at hA
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop_end" to ".Lbeeu_reduction_loop" with s
    have ⟨h21, h22, h23, h24⟩ := val256_eq_one_limbs X21 X22 X23 X24 hA
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime
    rw [h21, h22, h23, h24]; decide
  · simp only [hA, ↓reduceIte]
    dsimp only [Reg64s.beeuA] at hA
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop_end" to ".Lbeeu_reduction_loop" with s
    have h_nz := val256_ne_one_or_ne_zero X21 X22 X23 X24 hA
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime

theorem beeu_reduction_step_ge_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop")
      (pre :=
        s.regs.X14 = 0 ∧
        s.regs.beeuY ≥ s.regs.beeuN)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
        BlockFrame s st.data ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuY = s.regs.beeuY - s.regs.beeuN) := by
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
  kfinish beeu_mod_inverse_vartime [sub0Carry, sbcCarry, sub0Word, sbcWord, h_carry]
  rw [h_sub]
  subst h14
  dsimp only [val320, val256]
  omega

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
  apply tailrec_loop_simple (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_reduction_loop" ∧
      BlockFrame s st.data ∧
      st.data.regs.X14 = 0 ∧
      st.data.regs.beeuY % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
      st.data.regs.beeuY.toNat = v)
    (lt := (· < ·)) (Hwf := Nat.lt_wfRel.wf) (v0 := s.regs.beeuY.toNat) (g0 := ())
  · exact ⟨rfl, BlockFrame.refl s, h_x14, rfl, rfl⟩
  · rintro v _ ⟨st_data, st_pc⟩ ⟨rfl, hst_fr, hst_x14, hst_Y_mod, hst_v⟩
    dsimp only at hst_fr hst_x14 hst_Y_mod hst_v
    by_cases h_ge : st_data.regs.beeuY ≥ st_data.regs.beeuN
    · apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_reduction_step_ge_correct st_data ⟨hst_x14, h_ge⟩)
      intro mid ⟨h_pc, h_fr', h_x14', h_Y'⟩
      right
      refine ⟨mid.data.regs.beeuY.toNat, (), ⟨h_pc, hst_fr.trans h_fr', h_x14', ?_, rfl⟩, ?_⟩
      · rw [h_Y', hst_fr.N, Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod, hst_Y_mod]
      · have hY_nonneg : 0 ≤ st_data.regs.beeuY := val320_nonneg _ _ _ _ _
        have hst_N := hst_fr.N
        rw [h_Y', hst_fr.N, ← hst_v]
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
        rw [hst_fr.dmem]
        dsimp only [BeeuStackFrame] at h_mem ⊢
        ecancel
      apply (beeu_reduction_and_store_correct st_data sp' r₀.X0.toBitVec o0 o1 o2 o3 _
        ⟨h_sp_align', hst_fr.sp.trans h_sp, h_x12, hst_x14, h_y256_lt, h_mem_st⟩).bind
      rintro ⟨mid_data, mid_pc⟩ ⟨rfl, h_mid_x0, h_mid_sp, h_mid_x29, w0, w1, w2, w3, h_mid_val, h_mid_mem⟩
      dsimp only at h_mid_x0 h_mid_sp h_mid_x29 h_mid_val h_mid_mem
      have h_mid_mem' : (mid_data.dmem =⋆
          BeeuStackFrame r₀ sp' ⋆
          (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)) := by
        dsimp +zetaDelta only [BeeuStackFrame] at h_mid_mem ⊢
        ecancel
      apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_finish_correct mid_data r₀ (Words256At w0 w1 w2 w3 r₀.X0.toBitVec ⋆ R)
          ⟨h_sp_align, h_mid_x29.trans (hst_fr.x29.trans h_x29), h_mid_mem'⟩)
      rintro fin ⟨h_fin_pc, h_fin_x0, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_mem⟩
      left
      refine ⟨h_fin_pc, h_fin_x0.trans h_mid_x0, h_fin_sp, h_fin_x30, h_fin_cs,
        w0, w1, w2, w3, ?_, by ecancel⟩
      have hY_nonneg : 0 ≤ st_data.regs.beeuY := val320_nonneg _ _ _ _ _
      have hY_mod_eq : st_data.regs.beeuY % s.regs.beeuN = st_data.regs.beeuY :=
        Int.emod_eq_of_lt hY_nonneg (hst_fr.N ▸ h_lt)
      dsimp only [Reg64s.beeuY256] at h_mid_val
      rw [h_mid_val, h_y256, hst_fr.N, ← hst_Y_mod, hY_mod_eq]

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
  rintro ⟨mid_data, mid_pc⟩ ⟨h_mid_fr, h_mid_Y, h_branch⟩
  dsimp only at h_mid_fr h_mid_Y h_branch
  by_cases hA : s.regs.beeuA = 1
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    rcases h_branch with ⟨rfl, h_mid_x14⟩
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_reduction_to_return_correct mid_data r₀ o0 o1 o2 o3 R
        ⟨h_sp_align, h_mid_fr.sp.trans h_sp, h_mid_fr.x29.trans h_x29, h_mid_x14,
         h_mid_fr.N.symm ▸ h_n_pos, h_mid_fr.dmem ▸ h_mem⟩)
    rintro fin ⟨h_pc, h_x0, h_sp', h_x30', h_cs', w0, w1, w2, w3, h_val, h_mem'⟩
    rw [h_mid_fr.N, h_mid_Y] at h_val
    exact ⟨h_pc, h_sp', h_x30', h_cs', h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
  · simp only [hA, ↓reduceIte] at h_branch ⊢
    subst h_branch
    have h_mem_mid : (mid_data.dmem =⋆
        BeeuStackFrame r₀ (r₀.SP.toBitVec + 18446744073709551504#64) ⋆
        (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)) := by
      rw [h_mid_fr.dmem]; ecancel
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_epilogue_err_correct mid_data r₀ (Words256At o0 o1 o2 o3 r₀.X0.toBitVec ⋆ R)
        ⟨h_sp_align, h_mid_fr.x29.trans h_x29, h_mem_mid⟩)
    rintro fin ⟨h_pc, h_x0, h_sp', h_x30', h_cs', h_mem'⟩
    exact ⟨h_pc, h_sp', h_x30', h_cs', h_x0, by ecancel⟩

/-! ## Accumulator Bound Invariant (reachable-state bound on `X` and `Y`) -/

/-- Multiplier bounding the accumulators at the top of `.Lbeeu_loop`: `X, Y < 2 · N · beeuBound σ τ c`,
where `σ`/`τ` count the halvings of `X`/`Y` performed so far and `c` counts clamped 63-bit shifts
(`63 · c ≤ σ + τ`). -/
def beeuBound (σ τ c : Nat) : Int := ((σ + τ + 2) * 2 ^ c : Nat)

theorem beeuBound_pos (σ τ c : Nat) : 0 < beeuBound σ τ c := by
  unfold beeuBound
  have := Nat.two_pow_pos c
  exact_mod_cast Nat.mul_pos (by omega) this

theorem beeuBound_mono {σ τ c σ' τ' c' : Nat} (hσ : σ ≤ σ') (hτ : τ ≤ τ') (hc : c ≤ c') :
    beeuBound σ τ c ≤ beeuBound σ' τ' c' := by
  unfold beeuBound
  exact_mod_cast Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) hc)

theorem beeuBound_add_left (σ τ c k : Nat) :
    beeuBound σ τ c + k ≤ beeuBound (σ + k) τ c := by
  unfold beeuBound
  have h1 : 1 ≤ 2 ^ c := Nat.two_pow_pos c
  have : (σ + τ + 2) * 2 ^ c + k ≤ (σ + k + τ + 2) * 2 ^ c := by
    have : (σ + k + τ + 2) * 2 ^ c = (σ + τ + 2) * 2 ^ c + k * 2 ^ c := by
      rw [show σ + k + τ + 2 = (σ + τ + 2) + k by omega, Nat.add_mul]
    rw [this]
    have : k ≤ k * 2 ^ c := Nat.le_mul_of_pos_right k h1
    omega
  exact_mod_cast this

theorem beeuBound_add_right (σ τ c k : Nat) :
    beeuBound σ τ c + k ≤ beeuBound σ (τ + k) c := by
  have := beeuBound_add_left σ τ c k
  have h : beeuBound (σ + k) τ c = beeuBound σ (τ + k) c := by
    unfold beeuBound; rw [show σ + k + τ = σ + (τ + k) by omega]
  rw [← h]; exact this

theorem beeuBound_succ (σ τ c : Nat) : beeuBound σ τ (c + 1) = 2 * beeuBound σ τ c := by
  unfold beeuBound
  rw [Nat.pow_succ, Int.natCast_mul, Int.natCast_mul, Int.natCast_mul]
  grind

theorem beeuBound_le (σ τ c : Nat) (hσ : σ ≤ 255) (hτ : τ ≤ 255) (hc : c ≤ 8) :
    beeuBound σ τ c ≤ 131072 := by
  have h1 : (σ + τ + 2) * 2 ^ c ≤ 512 * 2 ^ 8 :=
    Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) hc)
  have h2 : (σ + τ + 2) * 2 ^ c ≤ 131072 := Nat.le_trans h1 (by decide)
  unfold beeuBound
  exact Int.ofNat_le.mpr h2

theorem beeuBound_zero : beeuBound 0 0 0 = 2 := by decide

/-- After `k ≥ 1` corrected halvings (`p = 2^k`), `X' < N·(M+1)` whenever `X < 2·N·M`. -/
theorem shift_bound_step (X X' N M : Int) (p : Nat) (hp : 2 ≤ p) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hX : X < 2 * (N * M)) (h : (p : Int) * X' ≤ X + ((p : Int) - 1) * N) : X' < N * (M + 1) := by
  rcases Int.lt_or_le X' (N * (M + 1)) with hlt | hle
  · exact hlt
  exfalso
  have h1 : (p : Int) * (N * (M + 1)) ≤ (p : Int) * X' :=
    Int.mul_le_mul_of_nonneg_left hle (by omega)
  have h2 : 2 * (N * M) ≤ (p : Int) * (N * M) :=
    Int.mul_le_mul_of_nonneg_right (by omega) (Int.mul_nonneg hN hM)
  grind

theorem update_bound_even (X₁ Y₁ N M M₂ : Int) (k₁ k₂ : Nat) (hN : 0 ≤ N)
    (hX : X₁ < N * (M + k₁)) (hY : Y₁ < N * (M + k₂)) (hM₂ : M + k₁ + k₂ ≤ M₂) :
    X₁ + Y₁ < 2 * (N * M₂) := by
  have : N * (M + k₁ + (M + k₂)) ≤ N * (2 * M₂) :=
    Int.mul_le_mul_of_nonneg_left (by omega) hN
  grind

theorem update_bound_odd (X₁ Y₁ N M M₂ : Int) (k₁ k₂ : Nat) (hN : 0 ≤ N)
    (hX : X₁ < N * (M + k₁)) (hY : Y₁ < N * (M + k₂)) (hM₂ : 2 * (M + k₁ + k₂) ≤ M₂) :
    X₁ + Y₁ < N * M₂ := by
  have : N * (M + k₁ + (M + k₂)) ≤ N * M₂ :=
    Int.mul_le_mul_of_nonneg_left (by omega) hN
  grind

theorem bound_mono_right (N M M' Z : Int) (hN : 0 ≤ N) (h : Z < N * M) (hM : M ≤ M') : Z < N * M' := by
  have := Int.mul_le_mul_of_nonneg_left hM hN
  omega

theorem ctzClamped_eq_zero_imp_odd (b0 : BitVec 64) (h : (b0.reverse ||| 1#64).clz = 0#64) :
    b0.getLsbD 0 = true := by
  revert h; bv_decide

theorem shift256Word_lsb_or_clamped (b0 b1 : BitVec 64) :
    let k := (b0.reverse ||| 1#64).clz
    ((b0 >>> (k % 64#64)) ||| (b1 <<< ((0#64 - k) % 64#64))).getLsbD 0 = true ∨ k = 63#64 := by
  bv_decide

/-- If the (clamped) shift amount is zero then `B` is odd. -/
theorem val256_odd_of_ctzClamped_eq_zero (b0 b1 b2 b3 : UInt64)
    (h : ctzClamped b0 = 0#64) : val256 b0 b1 b2 b3 % 2 = 1 := by
  rw [val256_emod_two]
  have := getLsbD_zero_eq_true_mod2 b0 (ctzClamped_eq_zero_imp_odd b0.toBitVec h)
  omega

/-- If the shifted `B` is still even, the shift was clamped to 63. -/
theorem shift256_val256_even_imp_clamped (b0 b1 b2 b3 : UInt64) :
    let k := ctzClamped b0
    val256 (UInt64.ofBitVec (shift256Word b0 b1 k)) (UInt64.ofBitVec (shift256Word b1 b2 k))
      (UInt64.ofBitVec (shift256Word b2 b3 k)) (UInt64.ofBitVec (shift256TopWord b3 k)) % 2 = 0 →
    k = 63#64 := by
  intro k h
  rw [val256_emod_two] at h
  rcases shift256Word_lsb_or_clamped b0.toBitVec b1.toBitVec with h1 | h1
  · exfalso
    have h2 : (UInt64.ofBitVec (shift256Word b0 b1 k)).toBitVec.getLsbD 0 = true := by
      rw [UInt64.toBitVec_ofBitVec, shift256Word_eq]; exact h1
    have := getLsbD_zero_eq_true_mod2 _ h2
    omega
  · exact h1

/-! ### gcd facts: dividing by powers of two preserves an odd gcd -/

theorem odd_of_dvd_odd (c g : Int) (hg : g % 2 = 1) (h : c ∣ g) : c % 2 = 1 := by
  obtain ⟨q, rfl⟩ := h
  have h01 : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases h01 with h0 | h1
  · rw [Int.mul_emod, h0, Int.zero_mul, Int.zero_emod] at hg
    omega
  · exact h1

theorem odd_dvd_of_dvd_two_mul (c m : Int) (hc : c % 2 = 1) (h : c ∣ 2 * m) : c ∣ m := by
  have h2 : (c + 1) / 2 * 2 = c + 1 :=
    Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero (by omega))
  have h_eq : m = (c + 1) / 2 * (2 * m) - c * m := by
    rw [← Int.mul_assoc, h2, Int.add_mul, Int.one_mul]
    omega
  rw [h_eq]
  exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h) (Int.dvd_mul_right c m)

theorem odd_dvd_of_dvd_two_pow_mul (c : Int) (hc : c % 2 = 1) (k : Nat) (m : Int)
    (h : c ∣ ((2 ^ k : Nat) : Int) * m) : c ∣ m := by
  induction k generalizing m with
  | zero => simpa using h
  | succ k ih =>
    apply odd_dvd_of_dvd_two_mul c m hc
    apply ih
    have : ((2 ^ (k + 1) : Nat) : Int) * m = ((2 ^ k : Nat) : Int) * (2 * m) := by
      rw [Nat.pow_succ, Int.natCast_mul]; grind
    rw [← this]
    exact h

/-- Dividing `B` by a power of two does not change `gcd A B` when that gcd is odd. -/
theorem Int.gcd_of_two_pow_mul_odd (A B B' : Int) (k : Nat) (h : ((2 ^ k : Nat) : Int) * B' = B)
    (hodd : (Int.gcd A B : Int) % 2 = 1) : Int.gcd A B' = Int.gcd A B := by
  rw [Int.gcd_right_eq_iff]
  intro c hcA
  constructor
  · intro hcB'
    rw [← h]
    exact Int.dvd_mul_of_dvd_right hcB'
  · intro hcB
    have hcg : c ∣ (Int.gcd A B : Int) := Int.dvd_coe_gcd hcA hcB
    have hc_odd : c % 2 = 1 := odd_of_dvd_odd c _ hodd hcg
    exact odd_dvd_of_dvd_two_pow_mul c hc_odd k B' (h ▸ hcB)

/-- Loop invariant at the top of `.Lbeeu_loop`, with ghost counters `σ`/`τ` (total halvings of
`X`/`Y` performed so far) and `c` (number of clamped 63-bit shifts). Besides the range and modular
facts, it bounds the 320-bit accumulators in every reachable state:
- `2^σ · B ≤ N` and `2^τ · A ≤ N` give `σ, τ ≤ 255` while `B, A > 0`, and `63 · c ≤ σ + τ`
  gives `c ≤ 8`, so `beeuBound σ τ c ≤ 2^17`;
- `X < 2 · N · beeuBound σ τ c` (and `X < N · beeuBound σ τ c` when `B` is odd, i.e. when `X` has
  already been halved since its last update), symmetrically for `Y`/`A`.
Hence `X, Y < 2^18 · N < 2^274`, so `X + N` and `X + Y` never overflow five limbs.
Finally `gcd A B = gcd a N` (Euclid's invariant), so the loop exits with `A = gcd a N`. -/
structure BeeuInv (a N : Int) (σ τ c : Nat) (B A X Y : Int) : Prop where
  N_odd : N % 2 = 1
  gcd_eq : Int.gcd A B = Int.gcd a N
  B_nonneg : 0 ≤ B
  B_le : B ≤ N
  A_pos : 0 < A
  A_le : A ≤ N
  X_inv : (a * X - B) % N = 0
  Y_inv : (a * Y + A) % N = 0
  B_shifted : ((2 ^ σ : Nat) : Int) * B ≤ N
  A_shifted : ((2 ^ τ : Nat) : Int) * A ≤ N
  clamps : 63 * c ≤ σ + τ
  X_lt : X < 2 * (N * beeuBound σ τ c)
  X_lt_odd : B % 2 = 1 → X < N * beeuBound σ τ c
  Y_lt : Y < 2 * (N * beeuBound σ τ c)
  Y_lt_odd : A % 2 = 1 → Y < N * beeuBound σ τ c

theorem two_pow_le_imp_le_255 (σ : Nat) (N : Int) (h : ((2 ^ σ : Nat) : Int) ≤ N)
    (hN : N < 256 ^ 32) : σ ≤ 255 := by
  have h256 : ((2 ^ 256 : Nat) : Int) = 256 ^ 32 := by decide
  have h1 : ((2 ^ σ : Nat) : Int) < ((2 ^ 256 : Nat) : Int) := by rw [h256]; omega
  have h2 : (2 ^ σ : Nat) < 2 ^ 256 := by exact_mod_cast h1
  have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2
  omega

theorem BeeuInv.sigma_le {a N : Int} {σ τ c : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ c B A X Y) (hB : 0 < B) (hN : N < 256 ^ 32) : σ ≤ 255 := by
  have h0 : (0 : Int) ≤ ((2 ^ σ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ B by omega) h0
  have h2 := h.B_shifted
  exact two_pow_le_imp_le_255 σ N (by omega) hN

theorem BeeuInv.tau_le {a N : Int} {σ τ c : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ c B A X Y) (hN : N < 256 ^ 32) : τ ≤ 255 := by
  have h0 : (0 : Int) ≤ ((2 ^ τ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ A by have := h.A_pos; omega) h0
  have h2 := h.A_shifted
  exact two_pow_le_imp_le_255 τ N (by omega) hN

/-- The absolute bounds needed by the per-phase lemmas: `X, Y < 2^319`. -/
theorem BeeuInv.bounds {a N : Int} {σ τ c : Nat} {B A X Y : Int}
    (h : BeeuInv a N σ τ c B A X Y) (hB : 0 < B) (hN : N < 256 ^ 32) :
    X < 256 ^ 40 / 2 ∧ Y < 256 ^ 40 / 2 := by
  have hσ := h.sigma_le hB hN
  have hτ := h.tau_le hN
  have hc : c ≤ 8 := by have := h.clamps; omega
  have hM := beeuBound_le σ τ c hσ hτ hc
  have hN0 : 0 ≤ N := by have := h.A_pos; have := h.A_le; omega
  have h1 : N * beeuBound σ τ c ≤ N * 131072 := Int.mul_le_mul_of_nonneg_left hM hN0
  have hX := h.X_lt
  have hY := h.Y_lt
  omega

theorem pow2_mul_bound_step (m : Nat) (x x' n z : Int)
    (h_inv : ((2 ^ m : Nat) : Int) * x ≤ z + (((2 ^ m : Nat) : Int) - 1) * n)
    (h_step : 2 * x' ≤ x + n) :
    ((2 ^ (m + 1) : Nat) : Int) * x' ≤ z + (((2 ^ (m + 1) : Nat) : Int) - 1) * n := by
  have h0 : (0 : Int) ≤ ((2 ^ m : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h1 := Int.mul_le_mul_of_nonneg_left h_step h0
  have h_pow : ((2 ^ (m + 1) : Nat) : Int) = ((2 ^ m : Nat) : Int) * 2 := by
    rw [Nat.pow_succ, Int.natCast_mul]; rfl
  rw [h_pow]
  grind

/-- Bound on `X` (resp. `Y`) right after its shift phase, in terms of the loop-top multiplier `M`:
`X₁ < N·(M + k)` whenever `X < 2·N·M`, `(B odd → X < N·M)`, `(B even → 1 ≤ k)` and
`2^k·X₁ ≤ X + (2^k − 1)·N`. -/
theorem shift_phase_bound (X X₁ N M B : Int) (k : Nat) (hN : 0 ≤ N) (hM : 0 ≤ M)
    (hX : X < 2 * (N * M)) (hX_odd : B % 2 = 1 → X < N * M)
    (hk : B % 2 = 0 → 1 ≤ k)
    (h : ((2 ^ k : Nat) : Int) * X₁ ≤ X + (((2 ^ k : Nat) : Int) - 1) * N) :
    X₁ < N * (M + k) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul, Int.sub_self, Int.zero_mul,
      Int.add_zero, Int.natCast_zero] at h ⊢
    have hB : B % 2 = 1 := by
      have h01 : B % 2 = 0 ∨ B % 2 = 1 := by omega
      rcases h01 with h0 | h1
      · exact absurd (hk h0) (by omega)
      · exact h1
    have := hX_odd hB
    omega
  · have hp : 2 ≤ 2 ^ k := Nat.one_lt_two_pow hk0
    have h1 := shift_bound_step X X₁ N M (2 ^ k) hp hN hM hX h
    exact bound_mono_right N (M + 1) (M + k) X₁ hN h1 (by omega)

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
        BlockFrame s st.data ∧
        st.data.regs.X13 = s.regs.X13 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        st.data.regs.beeuX % 2 = 0 ∧
        st.data.regs.beeuX % s.regs.beeuN = s.regs.beeuX % s.regs.beeuN ∧
        st.data.regs.beeuX ≤ s.regs.beeuX + s.regs.beeuN) := by
  rintro ⟨h14, hN_odd, h_xn_lt⟩
  dsimp only [Reg64s.beeuX, Reg64s.beeuN] at hN_odd h_xn_lt ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_loop_X" to ".Lshift1_0" with s
  cases h_lsb : X3.toBitVec.getLsbD 0
  · have h_mod2 := getLsbD_zero_eq_false_mod2 X3 h_lsb
    have := val256_nonneg X0 X1 X2 X30
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime
    rw [val320_emod_two]; omega
  · have h_mod2 := getLsbD_zero_eq_true_mod2 X3 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_lt320 : val320 X3 X4 X5 X6 X7 + val320 X0 X1 X2 X30 X14 < 256 ^ 40 := by
      subst h14; dsimp only [val320, val256] at h_xn_lt ⊢; omega
    have h_add := add320_val_of_lt X3 X4 X5 X6 X7 X0 X1 X2 X30 X14 h_lt320
    have h_n320 : val320 X0 X1 X2 X30 X14 = val256 X0 X1 X2 X30 := by
      subst h14; dsimp only [val320, val256]; omega
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [add0Carry, adcCarry, add0Word, adcWord]
    · rw [h_add, h_n320]
      have hx := val320_emod_two X3 X4 X5 X6 X7
      omega
    · rw [h_add, h_n320, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

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
        BlockFrame s st.data ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        2 * st.data.regs.beeuX = s.regs.beeuX) := by
  rintro ⟨h_x13_pos, h_x_even⟩
  dsimp only [Reg64s.beeuX] at h_x_even ⊢
  by_cases h1 : s.regs.X13.toNat = 1
  · simp only [h1, ↓reduceIte]
    kprologue beeu_mod_inverse_vartime at ".Lshift1_0" to ".Lbeeu_shift_A_Y" with s
    have h_x13_bv : X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have h_shift := shift1_val320 X3 X4 X5 X6 X7
    have h_x3_mod : (X3.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X3 X4 X5 X6 X7]; exact h_x_even
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [extr_sem_eq, ubfm_lsr1_sem_eq]
    rw [UInt64.toNat_ofBitVec, h_x13_bv]; rfl
  · simp only [h1, ↓reduceIte]
    have h_gt1 : 1 < s.regs.X13.toNat := by omega
    kprologue beeu_mod_inverse_vartime at ".Lshift1_0" to ".Lbeeu_shift_A_Y" with s
    have h_nz := sub_one_beq_zero_false_of_gt_one X13 h_gt1
    have h_dec := toNat_sub_one_of_pos X13 h_x13_pos
    have h_shift := shift1_val320 X3 X4 X5 X6 X7
    have h_x3_mod : (X3.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X3 X4 X5 X6 X7]; exact h_x_even
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [extr_sem_eq, ubfm_lsr1_sem_eq]

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
        BlockFrame s st.data ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        (2 * st.data.regs.beeuX) % s.regs.beeuN = s.regs.beeuX % s.regs.beeuN ∧
        2 * st.data.regs.beeuX ≤ s.regs.beeuX + s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_xn_lt⟩
  apply (beeu_shift_loop_X_pre_correct s ⟨h14, hN_odd, h_xn_lt⟩).bind
  rintro ⟨mid, mid_pc⟩ ⟨rfl, h_fr, h_x13, h_x14, h_B, h_A, h_Y, h_even, h_mod, h_le⟩
  dsimp only at h_fr h_x13 h_x14 h_B h_A h_Y h_even h_mod h_le
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_shift1_0_correct mid ⟨h_x13.symm ▸ h_x13_pos, h_even⟩)
  rintro fin ⟨h_pc, h_fr', h_x13', h_x14', h_B', h_A', h_Y', h_2x⟩
  rw [h_x13] at h_pc h_x13'
  refine ⟨h_pc, h_fr.trans h_fr', h_x13', h_x14'.trans h_x14, h_B'.trans h_B, h_A'.trans h_A,
    h_Y'.trans h_Y, ?_, ?_⟩
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
        BlockFrame s st.data ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        (((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
          s.regs.beeuX % s.regs.beeuN ∧
        st.data.regs.beeuX < 256 ^ 40 / 2 ∧
        ((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuX ≤
          s.regs.beeuX + (((2 ^ s.regs.X13.toNat : Nat) : Int) - 1) * s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_xn_lt⟩
  let k₀ := s.regs.X13.toNat
  have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
  apply tailrec_loop_simple (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X" ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      st.data.regs.X14 = 0 ∧
      BlockFrame s st.data ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      st.data.regs.beeuY = s.regs.beeuY ∧
      st.data.regs.beeuX + s.regs.beeuN < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuX) % s.regs.beeuN =
        s.regs.beeuX % s.regs.beeuN ∧
      ((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuX ≤
        s.regs.beeuX + (((2 ^ (k₀ - v) : Nat) : Int) - 1) * s.regs.beeuN)
    (lt := (· < ·)) (Hwf := Nat.lt_wfRel.wf) (v0 := k₀) (g0 := ())
  · refine ⟨rfl, h_x13_pos, Nat.le_refl _, rfl, h14, BlockFrame.refl s, rfl, rfl, rfl, h_xn_lt, ?_, ?_⟩
    · simp
    · simp
  · rintro v _ ⟨st, st_pc⟩ ⟨rfl, hv_pos, hv_le, h_x13, h_x14, h_fr, h_B, h_A, h_Y, h_xn, h_inv, h_bnd⟩
    dsimp only at h_x13 h_x14 h_fr h_B h_A h_Y h_xn h_inv h_bnd
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_X_step_correct st
        ⟨h_x13 ▸ hv_pos, h_x14, h_fr.N.symm ▸ hN_odd, h_fr.N.symm ▸ h_xn⟩)
    rintro mid ⟨h_pc, h_fr', h_x13', h_x14', h_B', h_A', h_Y', h_mod', h_2x'⟩
    rw [h_x13] at h_pc h_x13'
    rw [h_fr.N] at h_mod' h_2x'
    have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
    have h_bstep := pow2_mul_bound_step (k₀ - v) _ _ _ _ h_bnd h_2x'
    by_cases hv1 : v = 1
    · simp only [hv1, ↓reduceIte] at h_pc
      have h_k : k₀ - v + 1 = k₀ := by omega
      rw [h_k] at h_step h_bstep
      exact Or.inl ⟨h_pc, h_fr.trans h_fr', h_B'.trans h_B, h_A'.trans h_A, h_Y'.trans h_Y,
        h_step, by omega, h_bstep⟩
    · simp only [hv1, ↓reduceIte] at h_pc
      have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
      rw [h_k] at h_step h_bstep
      exact Or.inr ⟨v - 1, (), ⟨h_pc, by omega, by omega, h_x13', h_x14', h_fr.trans h_fr',
        h_B'.trans h_B, h_A'.trans h_A, h_Y'.trans h_Y, by omega, h_step, h_bstep⟩, by omega⟩

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
        BlockFrame s st.data ∧
        st.data.regs.X13 = s.regs.X13 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.regs.beeuY % 2 = 0 ∧
        st.data.regs.beeuY % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
        st.data.regs.beeuY ≤ s.regs.beeuY + s.regs.beeuN) := by
  rintro ⟨h14, hN_odd, h_yn_lt⟩
  dsimp only [Reg64s.beeuY, Reg64s.beeuN] at hN_odd h_yn_lt ⊢
  kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_loop_Y" to ".Lshift1_1" with s
  cases h_lsb : X8.toBitVec.getLsbD 0
  · have h_mod2 := getLsbD_zero_eq_false_mod2 X8 h_lsb
    have := val256_nonneg X0 X1 X2 X30
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime
    rw [val320_emod_two]; omega
  · have h_mod2 := getLsbD_zero_eq_true_mod2 X8 h_lsb
    have h0 : (0 : UInt64).toNat = 0 := rfl
    have h_lt320 : val320 X8 X9 X10 X11 X12 + val320 X0 X1 X2 X30 X14 < 256 ^ 40 := by
      subst h14; dsimp only [val320, val256] at h_yn_lt ⊢; omega
    have h_add := add320_val_of_lt X8 X9 X10 X11 X12 X0 X1 X2 X30 X14 h_lt320
    have h_n320 : val320 X0 X1 X2 X30 X14 = val256 X0 X1 X2 X30 := by
      subst h14; dsimp only [val320, val256]; omega
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [add0Carry, adcCarry, add0Word, adcWord]
    · rw [h_add, h_n320]
      have hy := val320_emod_two X8 X9 X10 X11 X12
      omega
    · rw [h_add, h_n320, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

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
        BlockFrame s st.data ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = s.regs.X14 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        2 * st.data.regs.beeuY = s.regs.beeuY) := by
  rintro ⟨h_x13_pos, h_y_even⟩
  dsimp only [Reg64s.beeuY] at h_y_even ⊢
  by_cases h1 : s.regs.X13.toNat = 1
  · simp only [h1, ↓reduceIte]
    kprologue beeu_mod_inverse_vartime at ".Lshift1_1" to ".Lbeeu_update_B_X_or_A_Y" with s
    have h_x13_bv : X13.toBitVec = 1#64 := BitVec.eq_of_toNat_eq h1
    have h_shift := shift1_val320 X8 X9 X10 X11 X12
    have h_x8_mod : (X8.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X8 X9 X10 X11 X12]; exact h_y_even
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [extr_sem_eq, ubfm_lsr1_sem_eq]
    rw [UInt64.toNat_ofBitVec, h_x13_bv]; rfl
  · simp only [h1, ↓reduceIte]
    have h_gt1 : 1 < s.regs.X13.toNat := by omega
    kprologue beeu_mod_inverse_vartime at ".Lshift1_1" to ".Lbeeu_update_B_X_or_A_Y" with s
    have h_nz := sub_one_beq_zero_false_of_gt_one X13 h_gt1
    have h_dec := toNat_sub_one_of_pos X13 h_x13_pos
    have h_shift := shift1_val320 X8 X9 X10 X11 X12
    have h_x8_mod : (X8.toNat % 2 : Int) = 0 := by
      rw [← val320_emod_two X8 X9 X10 X11 X12]; exact h_y_even
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime [extr_sem_eq, ubfm_lsr1_sem_eq]

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
        BlockFrame s st.data ∧
        st.data.regs.X13.toNat = s.regs.X13.toNat - 1 ∧
        st.data.regs.X14 = 0 ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        (2 * st.data.regs.beeuY) % s.regs.beeuN = s.regs.beeuY % s.regs.beeuN ∧
        2 * st.data.regs.beeuY ≤ s.regs.beeuY + s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_yn_lt⟩
  apply (beeu_shift_loop_Y_pre_correct s ⟨h14, hN_odd, h_yn_lt⟩).bind
  rintro ⟨mid, mid_pc⟩ ⟨rfl, h_fr, h_x13, h_x14, h_B, h_A, h_X, h_even, h_mod, h_le⟩
  dsimp only at h_fr h_x13 h_x14 h_B h_A h_X h_even h_mod h_le
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_shift1_1_correct mid ⟨h_x13.symm ▸ h_x13_pos, h_even⟩)
  rintro fin ⟨h_pc, h_fr', h_x13', h_x14', h_B', h_A', h_X', h_2y⟩
  rw [h_x13] at h_pc h_x13'
  refine ⟨h_pc, h_fr.trans h_fr', h_x13', h_x14'.trans h_x14, h_B'.trans h_B, h_A'.trans h_A,
    h_X'.trans h_X, ?_, ?_⟩
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
        BlockFrame s st.data ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        (((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
          s.regs.beeuY % s.regs.beeuN ∧
        st.data.regs.beeuY < 256 ^ 40 / 2 ∧
        ((2 ^ s.regs.X13.toNat : Nat) : Int) * st.data.regs.beeuY ≤
          s.regs.beeuY + (((2 ^ s.regs.X13.toNat : Nat) : Int) - 1) * s.regs.beeuN) := by
  rintro ⟨h_x13_pos, h14, hN_odd, h_yn_lt⟩
  let k₀ := s.regs.X13.toNat
  have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
  apply tailrec_loop_simple (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (_ : Unit) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y" ∧
      0 < v ∧ v ≤ k₀ ∧
      st.data.regs.X13.toNat = v ∧
      st.data.regs.X14 = 0 ∧
      BlockFrame s st.data ∧
      st.data.regs.beeuB = s.regs.beeuB ∧
      st.data.regs.beeuA = s.regs.beeuA ∧
      st.data.regs.beeuX = s.regs.beeuX ∧
      st.data.regs.beeuY + s.regs.beeuN < 256 ^ 40 ∧
      (((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuY) % s.regs.beeuN =
        s.regs.beeuY % s.regs.beeuN ∧
      ((2 ^ (k₀ - v) : Nat) : Int) * st.data.regs.beeuY ≤
        s.regs.beeuY + (((2 ^ (k₀ - v) : Nat) : Int) - 1) * s.regs.beeuN)
    (lt := (· < ·)) (Hwf := Nat.lt_wfRel.wf) (v0 := k₀) (g0 := ())
  · refine ⟨rfl, h_x13_pos, Nat.le_refl _, rfl, h14, BlockFrame.refl s, rfl, rfl, rfl, h_yn_lt, ?_, ?_⟩
    · simp
    · simp
  · rintro v _ ⟨st, st_pc⟩ ⟨rfl, hv_pos, hv_le, h_x13, h_x14, h_fr, h_B, h_A, h_X, h_yn, h_inv, h_bnd⟩
    dsimp only at h_x13 h_x14 h_fr h_B h_A h_X h_yn h_inv h_bnd
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_Y_step_correct st
        ⟨h_x13 ▸ hv_pos, h_x14, h_fr.N.symm ▸ hN_odd, h_fr.N.symm ▸ h_yn⟩)
    rintro mid ⟨h_pc, h_fr', h_x13', h_x14', h_B', h_A', h_X', h_mod', h_2y'⟩
    rw [h_x13] at h_pc h_x13'
    rw [h_fr.N] at h_mod' h_2y'
    have h_step := pow2_mul_emod_step (k₀ - v) _ _ _ _ h_inv h_mod'
    have h_bstep := pow2_mul_bound_step (k₀ - v) _ _ _ _ h_bnd h_2y'
    by_cases hv1 : v = 1
    · simp only [hv1, ↓reduceIte] at h_pc
      have h_k : k₀ - v + 1 = k₀ := by omega
      rw [h_k] at h_step h_bstep
      exact Or.inl ⟨h_pc, h_fr.trans h_fr', h_B'.trans h_B, h_A'.trans h_A, h_X'.trans h_X,
        h_step, by omega, h_bstep⟩
    · simp only [hv1, ↓reduceIte] at h_pc
      have h_k : k₀ - v + 1 = k₀ - (v - 1) := by omega
      rw [h_k] at h_step h_bstep
      exact Or.inr ⟨v - 1, (), ⟨h_pc, by omega, by omega, h_x13', h_x14', h_fr.trans h_fr',
        h_B'.trans h_B, h_A'.trans h_A, h_X'.trans h_X, by omega, h_step, h_bstep⟩, by omega⟩

theorem beeu_shift_B_header_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre := 0 < s.regs.beeuB)
      (post := fun st =>
        let k := ctzClamped s.regs.X25
        BlockFrame s st.data ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        if k = 0#64 then
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y" ∧
          st.data.regs.beeuB = s.regs.beeuB ∧
          s.regs.beeuB % 2 = 1
        else
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_X" ∧
          st.data.regs.X13.toNat = k.toNat ∧
          0 < k.toNat ∧
          st.data.regs.X14 = 0 ∧
          ((2 ^ k.toNat : Nat) : Int) * st.data.regs.beeuB = s.regs.beeuB ∧
          (st.data.regs.beeuB % 2 = 0 → k = 63#64)) := by
  intro hB_pos
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte]
    have h_odd := val256_odd_of_ctzClamped_eq_zero s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28 hk
    dsimp only [Reg64s.beeuB, ctzClamped] at hB_pos hk h_odd ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_loop" to ".Lbeeu_shift_loop_X" with s
    have h_nz := val256_pos_or_ne_zero X25 X26 X27 X28 hB_pos
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime
  · simp only [hk, ↓reduceIte]
    have h_par := shift256_val256_even_imp_clamped s.regs.X25 s.regs.X26 s.regs.X27 s.regs.X28
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
    kfinish beeu_mod_inverse_vartime [ctzClamped, shift256Word, shift256TopWord]

theorem beeu_shift_A_header_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_A_Y")
      (pre := True)
      (post := fun st =>
        let k := ctzClamped s.regs.X21
        BlockFrame s st.data ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        if k = 0#64 then
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_update_B_X_or_A_Y" ∧
          st.data.regs.beeuA = s.regs.beeuA ∧
          s.regs.beeuA % 2 = 1
        else
          st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_shift_loop_Y" ∧
          st.data.regs.X13.toNat = k.toNat ∧
          0 < k.toNat ∧
          st.data.regs.X14 = 0 ∧
          ((2 ^ k.toNat : Nat) : Int) * st.data.regs.beeuA = s.regs.beeuA ∧
          (st.data.regs.beeuA % 2 = 0 → k = 63#64)) := by
  intro _
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte]
    have h_odd := val256_odd_of_ctzClamped_eq_zero s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24 hk
    dsimp only [Reg64s.beeuA, ctzClamped] at hk h_odd ⊢
    kprologue beeu_mod_inverse_vartime at ".Lbeeu_shift_A_Y" to ".Lbeeu_shift_loop_Y" with s
    sym => kstep; tactic =>
    kfinish beeu_mod_inverse_vartime
  · simp only [hk, ↓reduceIte]
    have h_par := shift256_val256_even_imp_clamped s.regs.X21 s.regs.X22 s.regs.X23 s.regs.X24
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
    kfinish beeu_mod_inverse_vartime [ctzClamped, shift256Word, shift256TopWord]

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
        BlockFrame s st.data ∧
        st.data.regs.beeuA = s.regs.beeuA ∧
        st.data.regs.beeuY = s.regs.beeuY ∧
        0 < st.data.regs.beeuB ∧
        st.data.regs.beeuB ≤ s.regs.beeuB ∧
        st.data.regs.beeuX < 256 ^ 40 / 2 ∧
        (a * st.data.regs.beeuX - st.data.regs.beeuB) % s.regs.beeuN = 0 ∧
        ∃ k : Nat, k ≤ 63 ∧
          ((2 ^ k : Nat) : Int) * st.data.regs.beeuB = s.regs.beeuB ∧
          ((2 ^ k : Nat) : Int) * st.data.regs.beeuX ≤
            s.regs.beeuX + (((2 ^ k : Nat) : Int) - 1) * s.regs.beeuN ∧
          (s.regs.beeuB % 2 = 0 → 1 ≤ k) ∧
          (st.data.regs.beeuB % 2 = 0 → k = 63)) := by
  rintro ⟨hB_pos, hN_odd, hX_lt, h_inv⟩
  apply (beeu_shift_B_header_correct s hB_pos).bind
  rintro ⟨mid, mid_pc⟩ ⟨h_fr, h_A, h_X, h_Y, h_branch⟩
  dsimp only at h_fr h_A h_X h_Y h_branch
  by_cases hk : ctzClamped s.regs.X25 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_B, h_odd⟩
    apply Eventually.done
    dsimp only
    refine ⟨h_pc, h_fr, h_A, h_Y, h_B.symm ▸ hB_pos, by omega, h_X.symm ▸ hX_lt,
      by rw [h_X, h_B]; exact h_inv,
      0, by omega, by rw [h_B]; simp, by rw [h_X]; simp, by intro h; omega, by rw [h_B]; intro h; omega⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_x13, hk_pos, h_x14, h_B_shift, h_par⟩
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    have h_xn_lt : mid.regs.beeuX + mid.regs.beeuN < 256 ^ 40 := by rw [h_X, h_fr.N]; omega
    subst h_pc
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_X_correct mid
        ⟨h_x13 ▸ hk_pos, h_x14, h_fr.N.symm ▸ hN_odd, h_xn_lt⟩)
    rintro fin ⟨h_fin_pc, h_fin_fr, h_fin_B, h_fin_A, h_fin_Y, h_fin_X_mod, h_fin_X_lt, h_fin_X_bnd⟩
    have hB_nonneg : 0 ≤ fin.data.regs.beeuB := val256_nonneg _ _ _ _
    have ⟨hB'_pos, hB'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X25).toNat s.regs.beeuB fin.data.regs.beeuB
      hB_pos hB_nonneg (h_fin_B.symm ▸ h_B_shift)
    have hk63 : (ctzClamped s.regs.X25).toNat ≤ 63 :=
      BitVec.le_def.mp (clz_reverse_or_one_le_63 s.regs.X25.toBitVec)
    rw [h_x13, h_fr.N, h_X] at h_fin_X_mod h_fin_X_bnd
    refine ⟨h_fin_pc, h_fr.trans h_fin_fr, h_fin_A.trans h_A, h_fin_Y.trans h_Y,
      hB'_pos, hB'_le, h_fin_X_lt, ?_, (ctzClamped s.regs.X25).toNat, hk63,
      h_fin_B.symm ▸ h_B_shift, h_fin_X_bnd, fun _ => hk_pos, ?_⟩
    · exact shift_B_X_mod_inv (ctzClamped s.regs.X25).toNat a
        s.regs.beeuB fin.data.regs.beeuB s.regs.beeuX fin.data.regs.beeuX s.regs.beeuN
        hN_odd (h_fin_B.symm ▸ h_B_shift) h_fin_X_mod h_inv
    · intro h_even
      rw [h_fin_B] at h_even
      exact congrArg BitVec.toNat (h_par h_even)

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
        BlockFrame s st.data ∧
        st.data.regs.beeuB = s.regs.beeuB ∧
        st.data.regs.beeuX = s.regs.beeuX ∧
        0 < st.data.regs.beeuA ∧
        st.data.regs.beeuA ≤ s.regs.beeuA ∧
        st.data.regs.beeuY < 256 ^ 40 / 2 ∧
        (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0 ∧
        ∃ k : Nat, k ≤ 63 ∧
          ((2 ^ k : Nat) : Int) * st.data.regs.beeuA = s.regs.beeuA ∧
          ((2 ^ k : Nat) : Int) * st.data.regs.beeuY ≤
            s.regs.beeuY + (((2 ^ k : Nat) : Int) - 1) * s.regs.beeuN ∧
          (s.regs.beeuA % 2 = 0 → 1 ≤ k) ∧
          (st.data.regs.beeuA % 2 = 0 → k = 63)) := by
  rintro ⟨hA_pos, hN_odd, hY_lt, h_inv⟩
  apply (beeu_shift_A_header_correct s trivial).bind
  rintro ⟨mid, mid_pc⟩ ⟨h_fr, h_B, h_X, h_Y, h_branch⟩
  dsimp only at h_fr h_B h_X h_Y h_branch
  by_cases hk : ctzClamped s.regs.X21 = 0#64
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_A, h_odd⟩
    apply Eventually.done
    dsimp only
    refine ⟨h_pc, h_fr, h_B, h_X, h_A.symm ▸ hA_pos, by omega, h_Y.symm ▸ hY_lt,
      by rw [h_Y, h_A]; exact h_inv,
      0, by omega, by rw [h_A]; simp, by rw [h_Y]; simp, by intro h; omega, by rw [h_A]; intro h; omega⟩
  · simp only [hk, ↓reduceIte] at h_branch
    rcases h_branch with ⟨h_pc, h_x13, hk_pos, h_x14, h_A_shift, h_par⟩
    have h_N_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
    have h_yn_lt : mid.regs.beeuY + mid.regs.beeuN < 256 ^ 40 := by rw [h_Y, h_fr.N]; omega
    subst h_pc
    apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
      ?_ (beeu_shift_loop_Y_correct mid
        ⟨h_x13 ▸ hk_pos, h_x14, h_fr.N.symm ▸ hN_odd, h_yn_lt⟩)
    rintro fin ⟨h_fin_pc, h_fin_fr, h_fin_B, h_fin_A, h_fin_X, h_fin_Y_mod, h_fin_Y_lt, h_fin_Y_bnd⟩
    have hA_nonneg : 0 ≤ fin.data.regs.beeuA := val256_nonneg _ _ _ _
    have ⟨hA'_pos, hA'_le⟩ := pos_and_le_of_pow2_mul
      (ctzClamped s.regs.X21).toNat s.regs.beeuA fin.data.regs.beeuA
      hA_pos hA_nonneg (h_fin_A.symm ▸ h_A_shift)
    have hk63 : (ctzClamped s.regs.X21).toNat ≤ 63 :=
      BitVec.le_def.mp (clz_reverse_or_one_le_63 s.regs.X21.toBitVec)
    rw [h_x13, h_fr.N, h_Y] at h_fin_Y_mod h_fin_Y_bnd
    refine ⟨h_fin_pc, h_fr.trans h_fin_fr, h_fin_B.trans h_B, h_fin_X.trans h_X,
      hA'_pos, hA'_le, h_fin_Y_lt, ?_, (ctzClamped s.regs.X21).toNat, hk63,
      h_fin_A.symm ▸ h_A_shift, h_fin_Y_bnd, fun _ => hk_pos, ?_⟩
    · exact shift_A_Y_mod_inv (ctzClamped s.regs.X21).toNat a
        s.regs.beeuA fin.data.regs.beeuA s.regs.beeuY fin.data.regs.beeuY s.regs.beeuN
        hN_odd (h_fin_A.symm ▸ h_A_shift) h_fin_Y_mod h_inv
    · intro h_even
      rw [h_fin_A] at h_even
      exact congrArg BitVec.toNat (h_par h_even)

/-! ## 6. Outer Loop & Top-Level `beeu_mod_inverse_vartime` Specification -/

/-- One full iteration of `.Lbeeu_loop` when `0 < B`:
    executes `beeu_shift_B_X`, `beeu_shift_A_Y`, and `.Lbeeu_update_B_X_or_A_Y`,
    returning to `.Lbeeu_loop` with strictly smaller `(B + A).toNat` and re-establishing
    the loop invariant `BeeuInv` for updated ghost counters `σ' τ' c'`. -/
theorem beeu_loop_body_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) (σ τ c : Nat) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre :=
        0 < s.regs.beeuB ∧
        BeeuInv a s.regs.beeuN σ τ c s.regs.beeuB s.regs.beeuA s.regs.beeuX s.regs.beeuY)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
        BlockFrame s st.data ∧
        st.data.regs.beeuA ≤ s.regs.beeuA ∧
        (st.data.regs.beeuB + st.data.regs.beeuA).toNat <
          (s.regs.beeuB + s.regs.beeuA).toNat ∧
        ∃ σ' τ' c' : Nat,
          BeeuInv a s.regs.beeuN σ' τ' c' st.data.regs.beeuB st.data.regs.beeuA
            st.data.regs.beeuX st.data.regs.beeuY) := by
  rintro ⟨hB_pos, hI⟩
  have hN_lt : s.regs.beeuN < 256 ^ 32 := val256_lt _ _ _ _
  have hN_pos : 0 < s.regs.beeuN := by have := hI.A_pos; have := hI.A_le; omega
  have hN0 : 0 ≤ s.regs.beeuN := Int.le_of_lt hN_pos
  have hM0 : 0 ≤ beeuBound σ τ c := Int.le_of_lt (beeuBound_pos σ τ c)
  obtain ⟨hX_lt, hY_lt⟩ := hI.bounds hB_pos hN_lt
  -- Phase 1: shift B and X.
  apply (beeu_shift_B_X_correct s a ⟨hB_pos, hI.N_odd, hX_lt, hI.X_inv⟩).bind
  rintro ⟨st1, st1_pc⟩ ⟨h1_pc, h1_fr, h1_A, h1_Y, h1_B_pos, h1_B_le, h1_X_lt, h1_X_inv,
    k₁, hk₁_le, h1_B_shift, h1_X_bnd, h1_k₁_pos, h1_clamp⟩
  dsimp only at h1_pc h1_fr h1_A h1_Y h1_B_pos h1_B_le h1_X_lt h1_X_inv
  dsimp only at h1_B_shift h1_X_bnd h1_k₁_pos h1_clamp
  subst h1_pc
  -- Phase 2: shift A and Y.
  apply (beeu_shift_A_Y_correct st1 a
    ⟨h1_A.symm ▸ hI.A_pos, h1_fr.N.symm ▸ hI.N_odd, h1_Y.symm ▸ hY_lt, by
      rw [h1_Y, h1_A, h1_fr.N]; exact hI.Y_inv⟩).bind
  rintro ⟨st2, st2_pc⟩ ⟨h2_pc, h2_fr, h2_B, h2_X, h2_A_pos, h2_A_le, h2_Y_lt, h2_Y_inv,
    k₂, hk₂_le, h2_A_shift, h2_Y_bnd, h2_k₂_pos, h2_clamp⟩
  dsimp only at h2_pc h2_fr h2_B h2_X h2_A_pos h2_A_le h2_Y_lt h2_Y_inv
  dsimp only at h2_A_shift h2_Y_bnd h2_k₂_pos h2_clamp
  subst h2_pc
  rw [h1_A] at h2_A_shift h2_k₂_pos h2_A_le
  rw [h1_Y, h1_fr.N] at h2_Y_bnd
  rw [h1_fr.N] at h2_Y_inv
  -- Quantitative bounds after the shift phases, relative to the loop-top multiplier `M`.
  have hX₂ : st2.regs.beeuX < s.regs.beeuN * (beeuBound σ τ c + k₁) := by
    rw [h2_X]
    exact shift_phase_bound _ _ _ _ _ k₁ hN0 hM0 hI.X_lt hI.X_lt_odd h1_k₁_pos h1_X_bnd
  have hY₂ : st2.regs.beeuY < s.regs.beeuN * (beeuBound σ τ c + k₂) :=
    shift_phase_bound _ _ _ _ _ k₂ hN0 hM0 hI.Y_lt hI.Y_lt_odd h2_k₂_pos h2_Y_bnd
  -- Phase 3: the update step.
  have h_xy_lt : st2.regs.beeuX + st2.regs.beeuY < 256 ^ 40 := by omega
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_update_step_correct st2 h_xy_lt)
  rintro fin ⟨h3_pc, h3_fr, h3_branch⟩
  have h2_B_pos : 0 < st2.regs.beeuB := h2_B.symm ▸ h1_B_pos
  have h2_B_le : st2.regs.beeuB ≤ s.regs.beeuB := h2_B.symm ▸ h1_B_le
  have h2_X_inv : (a * st2.regs.beeuX - st2.regs.beeuB) % s.regs.beeuN = 0 := by
    rw [h2_X, h2_B]; exact h1_X_inv
  have hI_B_le := hI.B_le
  have hI_A_le := hI.A_le
  have hI_B_nonneg := hI.B_nonneg
  have hI_A_pos := hI.A_pos
  -- Euclid's invariant survives the shifts because `gcd A B ∣ N` is odd.
  have hg_odd : (Int.gcd s.regs.beeuA s.regs.beeuB : Int) % 2 = 1 := by
    rw [hI.gcd_eq]
    exact odd_of_dvd_odd _ _ hI.N_odd (Int.gcd_dvd_right a s.regs.beeuN)
  have hg1 : Int.gcd s.regs.beeuA st2.regs.beeuB = Int.gcd s.regs.beeuA s.regs.beeuB :=
    Int.gcd_of_two_pow_mul_odd _ _ _ k₁ (by rw [h2_B]; exact h1_B_shift) hg_odd
  have hg_odd' : (Int.gcd st2.regs.beeuB s.regs.beeuA : Int) % 2 = 1 := by
    rw [Int.gcd_comm, hg1]; exact hg_odd
  have hg2 : Int.gcd st2.regs.beeuA st2.regs.beeuB = Int.gcd a s.regs.beeuN := by
    rw [Int.gcd_comm, Int.gcd_of_two_pow_mul_odd _ _ _ k₂ h2_A_shift hg_odd', Int.gcd_comm, hg1,
      hI.gcd_eq]
  -- New ghost state: `σ + k₁`, `τ + k₂`, `c + dB + dA` with `dB`/`dA` flagging clamped shifts.
  obtain ⟨dB, hdB⟩ : ∃ dB : Nat, dB = if st2.regs.beeuB % 2 = 0 then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨dA, hdA⟩ : ∃ dA : Nat, dA = if st2.regs.beeuA % 2 = 0 then 1 else 0 := ⟨_, rfl⟩
  have hdB_le : dB ≤ 1 := by rw [hdB]; split <;> omega
  have hdA_le : dA ≤ 1 := by rw [hdA]; split <;> omega
  have hdB_clamp : dB = 1 → k₁ = 63 := by
    intro h; rw [hdB] at h; split at h
    · exact h1_clamp (h2_B ▸ ‹_›)
    · omega
  have hdA_clamp : dA = 1 → k₂ = 63 := by
    intro h; rw [hdA] at h; split at h
    · exact h2_clamp ‹_›
    · omega
  have hM_le : beeuBound σ τ c + k₁ + k₂ ≤ beeuBound (σ + k₁) (τ + k₂) (c + dB + dA) := by
    have h1 := beeuBound_add_left σ τ c k₁
    have h2 := beeuBound_add_right (σ + k₁) τ c k₂
    have h3 := beeuBound_mono (Nat.le_refl (σ + k₁)) (Nat.le_refl (τ + k₂))
      (show c ≤ c + dB + dA by omega)
    omega
  have hM_le2 : 1 ≤ dB + dA →
      2 * (beeuBound σ τ c + k₁ + k₂) ≤ beeuBound (σ + k₁) (τ + k₂) (c + dB + dA) := by
    intro hd
    have h1 := beeuBound_add_left σ τ c k₁
    have h2 := beeuBound_add_right (σ + k₁) τ c k₂
    have h3 := beeuBound_mono (Nat.le_refl (σ + k₁)) (Nat.le_refl (τ + k₂))
      (show c + 1 ≤ c + dB + dA by omega)
    have h4 := beeuBound_succ (σ + k₁) (τ + k₂) c
    omega
  have h_clamps : 63 * (c + dB + dA) ≤ (σ + k₁) + (τ + k₂) := by
    have := hI.clamps
    rcases Nat.eq_zero_or_pos dB with h0 | h1 <;> rcases Nat.eq_zero_or_pos dA with h0' | h1'
    · omega
    · have := hdA_clamp (by omega); omega
    · have := hdB_clamp (by omega); omega
    · have := hdA_clamp (by omega); have := hdB_clamp (by omega); omega
  have h_parity_d : (st2.regs.beeuB - st2.regs.beeuA) % 2 = 1 ∨
      (st2.regs.beeuA - st2.regs.beeuB) % 2 = 1 → 1 ≤ dB + dA := by
    intro h
    have hBe : st2.regs.beeuB % 2 = 0 ∨ st2.regs.beeuA % 2 = 0 := by omega
    rw [hdB, hdA]
    rcases hBe with h | h
    · simp only [h, ↓reduceIte]; omega
    · simp only [h, ↓reduceIte]; omega
  -- Shifted-multiple facts for B and A.
  have hpow_σ : ((2 ^ (σ + k₁) : Nat) : Int) = ((2 ^ σ : Nat) : Int) * ((2 ^ k₁ : Nat) : Int) := by
    rw [Nat.pow_add, Int.natCast_mul]
  have hpow_τ : ((2 ^ (τ + k₂) : Nat) : Int) = ((2 ^ τ : Nat) : Int) * ((2 ^ k₂ : Nat) : Int) := by
    rw [Nat.pow_add, Int.natCast_mul]
  have h2σ : (0 : Int) ≤ ((2 ^ σ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2τ : (0 : Int) ≤ ((2 ^ τ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2k₁ : (0 : Int) ≤ ((2 ^ k₁ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have h2k₂ : (0 : Int) ≤ ((2 ^ k₂ : Nat) : Int) := by exact_mod_cast Nat.zero_le _
  have hB_shifted' : ∀ B₃ : Int, B₃ ≤ st2.regs.beeuB →
      ((2 ^ (σ + k₁) : Nat) : Int) * B₃ ≤ s.regs.beeuN := by
    intro B₃ hB₃
    calc ((2 ^ (σ + k₁) : Nat) : Int) * B₃
        = ((2 ^ σ : Nat) : Int) * (((2 ^ k₁ : Nat) : Int) * B₃) := by rw [hpow_σ, Int.mul_assoc]
      _ ≤ ((2 ^ σ : Nat) : Int) * (((2 ^ k₁ : Nat) : Int) * st2.regs.beeuB) :=
          Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hB₃ h2k₁) h2σ
      _ = ((2 ^ σ : Nat) : Int) * s.regs.beeuB := by rw [h2_B, h1_B_shift]
      _ ≤ s.regs.beeuN := hI.B_shifted
  have hA_shifted' : ∀ A₃ : Int, A₃ ≤ st2.regs.beeuA →
      ((2 ^ (τ + k₂) : Nat) : Int) * A₃ ≤ s.regs.beeuN := by
    intro A₃ hA₃
    calc ((2 ^ (τ + k₂) : Nat) : Int) * A₃
        = ((2 ^ τ : Nat) : Int) * (((2 ^ k₂ : Nat) : Int) * A₃) := by rw [hpow_τ, Int.mul_assoc]
      _ ≤ ((2 ^ τ : Nat) : Int) * (((2 ^ k₂ : Nat) : Int) * st2.regs.beeuA) :=
          Int.mul_le_mul_of_nonneg_left (Int.mul_le_mul_of_nonneg_left hA₃ h2k₂) h2τ
      _ = ((2 ^ τ : Nat) : Int) * s.regs.beeuA := by rw [h2_A_shift]
      _ ≤ s.regs.beeuN := hI.A_shifted
  have hM'0 : 0 ≤ s.regs.beeuN * beeuBound (σ + k₁) (τ + k₂) (c + dB + dA) :=
    Int.mul_nonneg hN0 (Int.le_of_lt (beeuBound_pos _ _ _))
  refine ⟨h3_pc, h1_fr.trans (h2_fr.trans h3_fr), ?_, ?_, σ + k₁, τ + k₂, c + dB + dA, ?_⟩
  all_goals by_cases h_ge : st2.regs.beeuB ≥ st2.regs.beeuA
  all_goals simp only [h_ge, ↓reduceIte] at h3_branch
  all_goals rcases h3_branch with ⟨hB', hA', hX', hY'⟩
  · omega
  · omega
  · omega
  · omega
  · -- B ≥ A: B := B − A, X := X + Y
    refine ⟨hI.N_odd, ?_, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, h_clamps, ?_, ?_, ?_, ?_⟩
    · rw [hA', hB', Int.gcd_sub_self_right]; exact hg2
    · have h_lin : a * fin.data.regs.beeuX - fin.data.regs.beeuB =
          (a * st2.regs.beeuX - st2.regs.beeuB) + (a * st2.regs.beeuY + st2.regs.beeuA) := by
        rw [hX', hB']; grind
      rw [h_lin, Int.add_emod, h2_X_inv, h2_Y_inv]; simp
    · rw [hY', hA']; exact h2_Y_inv
    · exact hB_shifted' _ (by omega)
    · exact hA_shifted' _ (by omega)
    · rw [hX']
      exact update_bound_even _ _ _ _ _ k₁ k₂ hN0 hX₂ hY₂ hM_le
    · intro h_odd
      rw [hX']
      have hd : 1 ≤ dB + dA := h_parity_d (Or.inl (hB' ▸ h_odd))
      exact update_bound_odd _ _ _ _ _ k₁ k₂ hN0 hX₂ hY₂ (hM_le2 hd)
    · rw [hY']
      have := bound_mono_right _ _ _ _ hN0 hY₂
        (by omega : beeuBound σ τ c + k₂ ≤ beeuBound (σ + k₁) (τ + k₂) (c + dB + dA))
      omega
    · intro _
      rw [hY']
      exact bound_mono_right _ _ _ _ hN0 hY₂ (by omega)
  · -- B < A: A := A − B, Y := Y + X
    refine ⟨hI.N_odd, ?_, by omega, by omega, by omega, by omega, ?_, ?_, ?_, ?_, h_clamps, ?_, ?_, ?_, ?_⟩
    · rw [hA', hB', Int.gcd_sub_self_left]; exact hg2
    · rw [hX', hB']; exact h2_X_inv
    · have h_lin : a * fin.data.regs.beeuY + fin.data.regs.beeuA =
          (a * st2.regs.beeuY + st2.regs.beeuA) + (a * st2.regs.beeuX - st2.regs.beeuB) := by
        rw [hY', hA']; grind
      rw [h_lin, Int.add_emod, h2_Y_inv, h2_X_inv]; simp
    · exact hB_shifted' _ (by omega)
    · exact hA_shifted' _ (by omega)
    · rw [hX']
      have := bound_mono_right _ _ _ _ hN0 hX₂
        (by omega : beeuBound σ τ c + k₁ ≤ beeuBound (σ + k₁) (τ + k₂) (c + dB + dA))
      omega
    · intro _
      rw [hX']
      exact bound_mono_right _ _ _ _ hN0 hX₂ (by omega)
    · rw [hY']
      have := update_bound_even st2.regs.beeuY st2.regs.beeuX s.regs.beeuN (beeuBound σ τ c)
        (beeuBound (σ + k₁) (τ + k₂) (c + dB + dA)) k₂ k₁ hN0 hY₂ hX₂ (by omega)
      omega
    · intro h_odd
      rw [hY']
      have hd : 1 ≤ dB + dA := h_parity_d (Or.inr (hA' ▸ h_odd))
      have := update_bound_odd st2.regs.beeuY st2.regs.beeuX s.regs.beeuN (beeuBound σ τ c)
        (beeuBound (σ + k₁) (τ + k₂) (c + dB + dA)) k₂ k₁ hN0 hY₂ hX₂ (by have := hM_le2 hd; omega)
      omega

/-- Full verification of the outer binary extended Euclidean loop (`.Lbeeu_loop` to `.Lbeeu_loop_end`):
    terminates by well-founded induction on `(B + A).toNat`, carrying the ghost invariant `BeeuInv`
    (which keeps `X, Y < 2^319` in every reachable state), exiting with `B = 0`, `0 < A ≤ A₀`,
    `(a * Y + A) % N = 0`, and `A = 1 ↔ gcd a N = 1`. -/
theorem beeu_loop_correct [layout : Layout] [Layout.Valid beeu_mod_inverse_vartime]
    (s : MachineData) (a : Int) :
    (layout beeu_mod_inverse_vartime).Spec s
      (pc := (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop")
      (pre := BeeuInv a s.regs.beeuN 0 0 0 s.regs.beeuB s.regs.beeuA s.regs.beeuX s.regs.beeuY)
      (post := fun st =>
        st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop_end" ∧
        BlockFrame s st.data ∧
        0 < st.data.regs.beeuA ∧
        st.data.regs.beeuA ≤ s.regs.beeuA ∧
        (a * st.data.regs.beeuY + st.data.regs.beeuA) % s.regs.beeuN = 0 ∧
        (st.data.regs.beeuA = 1 ↔ Int.gcd a s.regs.beeuN = 1)) := by
  intro hI
  apply tailrec_loop_simple (step1 (layout beeu_mod_inverse_vartime)) _ _
    (P := fun (v : Nat) (g : Nat × Nat × Nat) st =>
      st.pc = (layout beeu_mod_inverse_vartime).label ".Lbeeu_loop" ∧
      BlockFrame s st.data ∧
      st.data.regs.beeuA ≤ s.regs.beeuA ∧
      (st.data.regs.beeuB + st.data.regs.beeuA).toNat = v ∧
      BeeuInv a s.regs.beeuN g.1 g.2.1 g.2.2 st.data.regs.beeuB st.data.regs.beeuA
        st.data.regs.beeuX st.data.regs.beeuY)
    (lt := (· < ·)) (Hwf := Nat.lt_wfRel.wf)
    (v0 := (s.regs.beeuB + s.regs.beeuA).toNat) (g0 := (0, 0, 0))
  · exact ⟨rfl, BlockFrame.refl s, Int.le_refl _, rfl, hI⟩
  · rintro v ⟨σ, τ, c⟩ ⟨st_data, st_pc⟩ ⟨rfl, hst_fr, hst_A_le, hst_v, hst_I⟩
    dsimp only at hst_fr hst_A_le hst_v hst_I
    by_cases hB0 : st_data.regs.beeuB = 0
    · apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_loop_exit_when_B_zero st_data hB0)
      rintro fin ⟨h_pc, h_fr', h_A', _, h_Y'⟩
      left
      refine ⟨h_pc, hst_fr.trans h_fr', h_A'.symm ▸ hst_I.A_pos, h_A'.symm ▸ hst_A_le, ?_, ?_⟩
      · rw [h_Y', h_A']
        exact hst_I.Y_inv
      · -- `B = 0`, so `A = gcd A 0 = gcd a N`.
        have hg := hst_I.gcd_eq
        rw [hB0, Int.gcd_zero] at hg
        have hA_pos := hst_I.A_pos
        rw [h_A']
        constructor
        · intro h; rw [← hg]; omega
        · intro h; rw [← hg] at h; omega
    · have hst_B_pos : 0 < st_data.regs.beeuB := by have := hst_I.B_nonneg; omega
      have hst_I' : BeeuInv a st_data.regs.beeuN σ τ c st_data.regs.beeuB st_data.regs.beeuA
          st_data.regs.beeuX st_data.regs.beeuY := by
        rw [hst_fr.N]; exact hst_I
      apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
        ?_ (beeu_loop_body_correct st_data a σ τ c ⟨hst_B_pos, hst_I'⟩)
      rintro mid ⟨h_pc, h_fr', h_A_le', h_lt', σ', τ', c', hI'⟩
      right
      refine ⟨(mid.data.regs.beeuB + mid.data.regs.beeuA).toNat, (σ', τ', c'),
        ⟨h_pc, hst_fr.trans h_fr', Int.le_trans h_A_le' hst_A_le, rfl, ?_⟩, by omega⟩
      rw [← hst_fr.N]
      exact hI'

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

/-- Top-level end-to-end functional correctness of BoringSSL's `beeu_mod_inverse_vartime`:
    Given a 16-byte-aligned stack with 112 bytes of frame space, 32-byte input buffers `a_bs` at `x1`
    and odd modulus `n_bs` at `x2` with `0 ≤ a ≤ n`, and a 32-byte output buffer at `x0`,
    `beeu_mod_inverse_vartime` terminates and returns to `x30` with `sp` and all callee-saved
    registers (`x19..x29`) restored, and:
    - if `gcd a n = 1`, returns `x0 = 1` and writes 256-bit `out` (`0 < out ≤ n`) to the output buffer
      such that `(a * out) % n = 1 % n` (the modular inverse of `a` modulo `n`),
    - otherwise returns `x0 = 0` with the output buffer unchanged. -/
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
        if Int.gcd a n = 1 then
          st.data.regs.X0 = 1 ∧
          ∃ w0 w1 w2 w3 : UInt64,
            0 < val256 w0 w1 w2 w3 ∧
            val256 w0 w1 w2 w3 ≤ n ∧
            (a * val256 w0 w1 w2 w3) % n = 1 % n ∧
            (st.data.dmem =⋆
              BeeuStackFrame s₀.regs sp' ⋆
              Words256At w0 w1 w2 w3 s₀.regs.X0.toBitVec ⋆
              a_bs @ s₀.regs.X1 ⋆
              n_bs @ s₀.regs.X2 ⋆
              R)
        else
          st.data.regs.X0 = 0 ∧
          (st.data.dmem =⋆
            BeeuStackFrame s₀.regs sp' ⋆
            Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
            a_bs @ s₀.regs.X1 ⋆
            n_bs @ s₀.regs.X2 ⋆
            R)) := by
  rintro ⟨h_sp_align, h_stack_len, h_a_len, h_n_len, h_a_le, h_n_pos, h_n_odd, h_mem⟩
  let sp' := s₀.regs.SP.toBitVec + 18446744073709551504#64
  let a := Int.ofBytes a_bs
  let n := Int.ofBytes n_bs
  have h_a_nonneg : 0 ≤ a := Int.ofBytes_ge_zero a_bs
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
  have h1_I : BeeuInv a st1.regs.beeuN 0 0 0 st1.regs.beeuB st1.regs.beeuA
      st1.regs.beeuX st1.regs.beeuY := by
    rw [h1_B, h1_A, h1_N, h1_X, h1_Y]
    refine ⟨h_n_odd, Int.gcd_comm _ _, h_a_nonneg, h_a_le, h_n_pos, Int.le_refl _, ?_, ?_, ?_, ?_,
      by omega, ?_, ?_, ?_, ?_⟩
    · change (a * 1 - a) % n = 0; simp
    · change (a * 0 + n) % n = 0; simp
    · simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul]; exact h_a_le
    · simp only [Nat.pow_zero, Int.natCast_one, Int.one_mul]; exact Int.le_refl _
    · rw [beeuBound_zero]; omega
    · intro _; rw [beeuBound_zero]; omega
    · rw [beeuBound_zero]; omega
    · intro _; rw [beeuBound_zero]; omega
  apply (beeu_loop_correct st1 a h1_I).bind
  rintro ⟨st2, st2_pc⟩ ⟨h2_pc, h2_fr, h2_A_pos, h2_A_le, h2_Y_inv, h2_gcd⟩
  dsimp only at h2_pc h2_fr h2_A_pos h2_A_le h2_Y_inv h2_gcd
  rw [h1_N] at h2_gcd
  subst h2_pc
  have h2_sp_eq : st2.regs.SP = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_fr.sp]; exact h1_sp)
  have h2_x29_eq : st2.regs.X29 = UInt64.ofBitVec sp' :=
    UInt64.eq_of_toBitVec_eq (by rw [h2_fr.x29]; exact h1_x29)
  have h2_mem : (st2.dmem =⋆
      BeeuStackFrame s₀.regs sp' ⋆
      Words256At o0 o1 o2 o3 s₀.regs.X0.toBitVec ⋆
      (a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)) := by
    rw [h2_fr.dmem]; ecancel
  apply eventually_weaken (step1 (layout beeu_mod_inverse_vartime)) _ _ _
    ?_ (beeu_loop_end_to_return_correct st2 s₀.regs o0 o1 o2 o3
      (a_bs @ s₀.regs.X1 ⋆ n_bs @ s₀.regs.X2 ⋆ R)
      ⟨h_sp_align, h2_sp_eq, h2_x29_eq, by rw [h2_fr.N, h1_N]; exact h_n_pos, h2_mem⟩)
  rintro fin ⟨h_fin_pc, h_fin_sp, h_fin_x30, h_fin_cs, h_fin_branch⟩
  refine ⟨h_fin_pc, h_fin_sp, h_fin_x30, h_fin_cs, ?_⟩
  split
  · rename_i hg
    have hA1 : st2.regs.beeuA = 1 := h2_gcd.mpr hg
    simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, w0, w1, w2, w3, h_val, h_mem'⟩
    have h_inv1 : (a * st2.regs.beeuY + 1) % n = 0 := by
      rw [hA1, h1_N] at h2_Y_inv; exact h2_Y_inv
    have h_val_n : val256 w0 w1 w2 w3 = n - (st2.regs.beeuY % n) := by
      rw [h2_fr.N, h1_N] at h_val; exact h_val
    have ⟨h_out_pos, h_out_le, h_out_inv⟩ :=
      mod_inv_of_beeu_end a st2.regs.beeuY (val256 w0 w1 w2 w3) n h_n_pos h_inv1 h_val_n
    exact ⟨h_x0, w0, w1, w2, w3, h_out_pos, h_out_le, h_out_inv, by ecancel⟩
  · rename_i hg
    have hA1 : ¬ st2.regs.beeuA = 1 := fun h => hg (h2_gcd.mp h)
    simp only [hA1, ↓reduceIte] at h_fin_branch
    rcases h_fin_branch with ⟨h_x0, h_mem'⟩
    exact ⟨h_x0, by ecancel⟩
