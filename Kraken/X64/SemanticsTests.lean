module

import Kraken.X64.Semantics

/-!
# Semantics shape tests (x86-64)

Regression guard for the grind/omega-friendliness of the shapes the semantics hand to proofs:
the flag functions and their value-level projections, and the compare idiom. Every goal here must
close with `grind`, `omega` or `simp` in milliseconds.
-/

open Kraken

/-! ### Flag projections (`@[kcond]`) are the value-level facts -/

example (a b : BitVec 64) : (StatusFlags.sub a b).cf = decide (a.toNat < b.toNat) := by simp
example (a b : BitVec 64) : (StatusFlags.sub a b).zf = decide (a = b) := by simp
example (a b : BitVec 64) : (StatusFlags.add a b).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.adc a b c).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.sbb a b c).cf = decide (a.toNat < b.toNat + c.toNat) := by simp
example (a : BitVec 64) (cf : Bool) : (StatusFlags.dec a cf).zf = decide (a = 1#64) := by simp
example (a : BitVec 64) (cf : Bool) : (StatusFlags.dec a cf).cf = cf := by simp
example (v : BitVec 64) (af : Bool) : (StatusFlags.logical v af).zf = decide (v = 0#64) := by simp

-- A branch condition after `cmp a, b` reads as the comparison itself.
example (a b : BitVec 64) : CondCode.interp .c (StatusFlags.sub a b) = decide (a.toNat < b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .be (StatusFlags.sub a b) = decide (a.toNat ≤ b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .a (StatusFlags.sub a b) = decide (b.toNat < a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .l (StatusFlags.sub a b) = decide (a.toInt < b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .ge (StatusFlags.sub a b) = decide (b.toInt ≤ a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .g (StatusFlags.sub a b) = decide (b.toInt < a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .le (StatusFlags.sub a b) = decide (a.toInt ≤ b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .z (StatusFlags.sub a b) = decide (a = b) := by
  simp [CondCode.interp]

/-! ### Carry chains: the limb identities feed `omega` directly -/

example (a0 b0 a1 b1 : BitVec 64) (c : Bool) :
    ((a0 + b0 + BitVec.ofNat 64 c.toNat).toNat : Int) +
      2 ^ 64 * (a1 + b1 + BitVec.ofNat 64 ((StatusFlags.adc a0 b0 c).cf).toNat).toNat +
      2 ^ 128 * ((StatusFlags.adc a1 b1 (StatusFlags.adc a0 b0 c).cf).cf).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) + c.toNat := by
  have h0 := StatusFlags.adc_toNat a0 b0 c (by decide)
  have h1 := StatusFlags.adc_toNat a1 b1 (StatusFlags.adc a0 b0 c).cf (by decide)
  simp only [Nat.reducePow] at h0 h1
  omega
