module

import Kraken.AArch64.Semantics

/-!
# Semantics shape tests (AArch64)

Regression guard for the grind/omega-friendliness of the shapes the semantics hand to proofs:
the flag functions and their value-level projections, immediates, `UInt64`/`BitVec`/`Nat`
bridging, and the compare idiom. Every goal here must close with `grind`, `omega` or `simp` in
milliseconds; if a semantics change makes one of them fail, the proof ergonomics regressed.
-/

open Kraken

/-! ### Flag projections (`@[kcond]`) are the value-level facts -/

example (a b : BitVec 64) : (StatusFlags.subs a b).c = decide (b.toNat ≤ a.toNat) := by simp
example (a b : BitVec 64) : (StatusFlags.subs a b).z = decide (a = b) := by simp
example (a b : BitVec 64) : (StatusFlags.adds a b).c = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.adcs a b c).c = decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat) := by simp
example (a b : BitVec 64) (c : Bool) :
    (StatusFlags.sbcs a b c).c = decide (b.toNat + (!c).toNat ≤ a.toNat) := by simp

-- A branch condition after `subs`/`cmp` reads as the comparison itself.
example (a b : BitVec 64) : CondCode.interp .CS (StatusFlags.subs a b) = decide (b.toNat ≤ a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .LT (StatusFlags.subs a b) = decide (a.toInt < b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .GE (StatusFlags.subs a b) = decide (b.toInt ≤ a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .GT (StatusFlags.subs a b) = decide (b.toInt < a.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .LE (StatusFlags.subs a b) = decide (a.toInt ≤ b.toInt) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .HI (StatusFlags.subs a b) = decide (b.toNat < a.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .LS (StatusFlags.subs a b) = decide (a.toNat ≤ b.toNat) := by
  simp [CondCode.interp]
example (a b : BitVec 64) : CondCode.interp .EQ (StatusFlags.subs a b) = decide (a = b) := by
  simp [CondCode.interp]

-- `cmn xzr, xzr` clears the carry.
example : (StatusFlags.adds 0#64 0#64).c = false := by simp

/-! ### Carry chains: the limb identities feed `omega` directly -/

example (a0 b0 a1 b1 : BitVec 64) (c : Bool) :
    ((a0 + b0 + BitVec.ofNat 64 c.toNat).toNat : Int) +
      2 ^ 64 * (a1 + b1 + BitVec.ofNat 64 ((StatusFlags.adcs a0 b0 c).c).toNat).toNat +
      2 ^ 128 * ((StatusFlags.adcs a1 b1 (StatusFlags.adcs a0 b0 c).c).c).toNat =
      a0.toNat + 2 ^ 64 * a1.toNat + (b0.toNat + 2 ^ 64 * b1.toNat) + c.toNat := by
  have h0 := StatusFlags.adcs_toNat a0 b0 c (by decide)
  have h1 := StatusFlags.adcs_toNat a1 b1 (StatusFlags.adcs a0 b0 c).c (by decide)
  simp only [Nat.reducePow] at h0 h1
  omega

/-! ### The raw definitions are still what grind sees through, if needed -/

-- The carry as defined (wrapped result ≠ exact result) is itself grind-friendly.
example (a b : BitVec 64) :
    ((((a - b).toNat : Int) == (a.toNat : Int) - (b.toNat : Int)) = true) ↔ b.toNat ≤ a.toNat := by
  grind

example (a b : BitVec 64) :
    ((((a - b).toInt) != a.toInt - b.toInt) = true) ↔
      ¬ (-(2 ^ 63) ≤ a.toInt - b.toInt ∧ a.toInt - b.toInt < 2 ^ 63) := by
  grind

/-! ### `UInt64` registers, `BitVec` arithmetic, `Nat` specs -/

example (x : UInt64) (h : 1 < x.toNat) : (x.toBitVec - 1#64 == 0#64) = false := by grind
example (x : UInt64) (h : x.toBitVec = 1#64) : x.toNat = 1 := by grind
example (x : UInt64) : (UInt64.ofBitVec (x.toBitVec + 1#64)).toNat = (x.toNat + 1) % 2 ^ 64 := by grind
example (x : UInt64) (h : 0 < x.toNat) : (x.toBitVec != 0#64) = true := by grind

/-! ### Immediates -/

example (x : BitVec 64) : x - BitVec.ofInt 64 1 = x - 1#64 := by grind
example (x : BitVec 64) : x + BitVec.ofInt 64 (Int64.toInt (-112)) = x - 112#64 := by grind
