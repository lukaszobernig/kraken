module

import Kraken.Attribute

/-!
# 64-bit shift / mask arithmetic

Instruction-level identities relating `BitVec` shifts, masks, funnel shifts and the
`rbit`/`clz` trailing-zero idiom to `Nat` arithmetic (`/ 2^k`, `% 2^k`, `* 2^(64-k)`). They let
multi-limb proofs stay at the `Nat`/`Int` level (`omega`, `grind`) instead of running `bv_decide`
on wide multiplications.

Policy for `bv_decide` in Kraken proofs: avoid it. Every call adds a trusted
`*._native.bv_decide.ax` axiom (the SAT certificate checker runs as native code) and its cost
grows quickly with width and with `*`/`/`. Prefer `grind` (linear `BitVec` arithmetic, `|||`/`=0`
reasoning), `omega` on `toNat` images, and the lemmas below; if `bv_decide` is still needed, keep
it to facts at most 64 bits wide with no non-constant multiplication or division (milliseconds).
-/

public section

namespace BitVec

variable {w : Nat}

theorem umod_64_eq_self {k : BitVec 64} (hk63 : k ≤ 63#64) : k % 64#64 = k := by grind

theorem toNat_le_63 {k : BitVec 64} (hk63 : k ≤ 63#64) : k.toNat ≤ 63 := by
  simpa [BitVec.le_def] using hk63

theorem one_le_toNat {k : BitVec 64} (hk1 : 1#64 ≤ k) : 1 ≤ k.toNat := by
  simpa [BitVec.le_def] using hk1

theorem neg_umod_64 {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    (0#64 - k) % 64#64 = 64#64 - k := by grind

theorem toNat_neg_umod_64 {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((0#64 - k) % 64#64).toNat = 64 - k.toNat := by
  have hk := toNat_le_63 hk63
  rw [neg_umod_64 hk1 hk63, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem two_pow_le_two_pow_63 {k : BitVec 64} (hk63 : k ≤ 63#64) : 2 ^ k.toNat ≤ 2 ^ 63 :=
  Nat.pow_le_pow_right (by decide) (toNat_le_63 hk63)

/-- `1 << k` as a number. -/
theorem toNat_one_shiftLeft {k : BitVec 64} (hk63 : k ≤ 63#64) :
    (1#64 <<< k).toNat = 2 ^ k.toNat := by
  have hk := toNat_le_63 hk63
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- The mask `(1 << k) - 1` as a number. -/
theorem toNat_mask {k : BitVec 64} (hk63 : k ≤ 63#64) :
    ((1#64 <<< k) - 1#64).toNat = 2 ^ k.toNat - 1 := by
  rw [BitVec.toNat_sub, toNat_one_shiftLeft hk63, BitVec.toNat_ofNat]
  have : 1 % 2 ^ 64 = 1 := by decide
  rw [this]
  have hp_pos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have hp_le := two_pow_le_two_pow_63 hk63
  omega

/-- `x & ((1 << k) - 1) = x mod 2^k`. -/
theorem toNat_and_mask (x : BitVec 64) {k : BitVec 64} (hk63 : k ≤ 63#64) :
    (x &&& ((1#64 <<< k) - 1#64)).toNat = x.toNat % 2 ^ k.toNat := by
  rw [BitVec.toNat_and, toNat_mask hk63, Nat.and_two_pow_sub_one_eq_mod]

/-- A full-width register read in `BitVec` form: `BitVec.ofNat 64 x.toNat` is `x.toBitVec`
(the shape left by sub-register extraction, `extractLsb' 0 64`, on `UInt64` registers). -/
theorem _root_.UInt64.bitVecOfNat_toNat (x : UInt64) : BitVec.ofNat 64 x.toNat = x.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

theorem _root_.UInt32.bitVecOfNat_toNat (x : UInt32) : BitVec.ofNat 32 x.toNat = x.toBitVec :=
  BitVec.eq_of_toNat_eq (by simp)

/-- `x >> k = x / 2^k`. -/
theorem toNat_ushiftRight_bv (x k : BitVec 64) :
    (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `ubfm`/`lsr #k` with an immediate: extracting the low `m ≥ w - k` bits of `x >>> k` and
re-extending to `w` bits is the identity (the top `k` bits are already zero). Used by `kstep` as
a normal-form rule for the `ubfm` residue, and a `grind` rewrite rule. -/
@[grind =]
theorem setWidth_extractLsb'_ushiftRight (x : BitVec w) {k m : Nat} (h : w ≤ m + k) :
    BitVec.setWidth w (BitVec.extractLsb' 0 m (x >>> k)) = x >>> k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat / 2 ^ k < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt

theorem two_pow_mul_two_pow_sub {k : BitVec 64} (hk63 : k ≤ 63#64) :
    2 ^ k.toNat * 2 ^ (64 - k.toNat) = 2 ^ 64 := by
  have hk := toNat_le_63 hk63
  rw [← Nat.pow_add]; congr 1; omega

/-- `x << (64 - k) = (x mod 2^k) · 2^(64-k)` (the bits of `x` that survive the shift). -/
theorem toNat_shiftLeft_neg (x : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    (x <<< ((0#64 - k) % 64#64)).toNat = (x.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [BitVec.shiftLeft_eq', toNat_neg_umod_64 hk1 hk63, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    ← two_pow_mul_two_pow_sub hk63, Nat.mul_mod_mul_right]

/-! ### Funnel shifts

`(lo >> k) | (hi << (w - k))` concatenates the top `w - k` bits of `lo` with the low `k` bits of
`hi`. The two halves occupy disjoint bit ranges, so `|||` is `+` and the result is
`lo / 2^k + (hi mod 2^k) · 2^(w-k)` with no overflow. -/

/-- Funnel shift with `Nat` shift amounts `k` and `m`, `k + m = w` (the form produced by
`extr`-style instructions with immediate shift amounts). A `grind` rewrite rule: with literal
amounts `grind` discharges `k + m = w` itself. -/
@[grind =]
theorem toNat_funnel_nat' (lo hi : BitVec w) {k m : Nat} (hkm : k + m = w) :
    ((lo >>> k) ||| (hi <<< m)).toNat = lo.toNat / 2 ^ k + (hi.toNat % 2 ^ k) * 2 ^ m := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hpq : 2 ^ k * 2 ^ m = 2 ^ w := by rw [← Nat.pow_add, hkm]
  rw [← hpq, Nat.mul_mod_mul_right]
  have hA : lo.toNat / 2 ^ k < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hpq]; exact lo.isLt
  have h := Nat.two_pow_add_eq_or_of_lt hA (hi.toNat % 2 ^ k)
  rw [Nat.mul_comm (hi.toNat % 2 ^ k), Nat.or_comm, ← h]
  omega

/-- Funnel shift with `Nat` shift amounts `k` and `w - k`. -/
theorem toNat_funnel_nat (lo hi : BitVec w) {k : Nat} (hkw : k ≤ w) :
    ((lo >>> k) ||| (hi <<< (w - k))).toNat =
      lo.toNat / 2 ^ k + (hi.toNat % 2 ^ k) * 2 ^ (w - k) :=
  toNat_funnel_nat' lo hi (by omega)

/-- Funnel shift with 64-bit register shift amounts `k % 64` and `(-k) % 64` (the form produced
by variable-shift instructions: `lsr`/`lsl` by a register). -/
theorem toNat_funnel (lo hi : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat =
      lo.toNat / 2 ^ k.toNat + (hi.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq', umod_64_eq_self hk63,
    toNat_neg_umod_64 hk1 hk63]
  have hk := toNat_le_63 hk63
  exact toNat_funnel_nat lo hi (by omega)

/-- Multi-limb funnel-shift limb identity: multiplying the funnel-shifted word
`(lo >> k) | (hi << (-k))` by `2^k` and adding the low `k` bits of `lo` yields
`lo + 2^64 · (low k bits of hi)`. -/
theorem toNat_funnel_mul_add_and_mask (lo hi : BitVec 64) {k : BitVec 64}
    (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat +
      (lo &&& mask).toNat =
      lo.toNat + 2 ^ 64 * (hi &&& mask).toNat := by
  dsimp only
  rw [toNat_funnel lo hi hk1 hk63, umod_64_eq_self hk63, toNat_and_mask lo hk63,
    toNat_and_mask hi hk63]
  have := two_pow_mul_two_pow_sub hk63
  have := Nat.div_add_mod lo.toNat (2 ^ k.toNat)
  grind

/-- Multi-limb right-shift top-limb identity: multiplying `hi >> k` by `2^k` and adding the low
`k` bits of `hi` reconstructs `hi`. -/
theorem toNat_ushiftRight_mul_add_and_mask (hi : BitVec 64) {k : BitVec 64}
    (hk63 : k ≤ 63#64) :
    let mask := (1#64 <<< (k % 64#64)) - 1#64
    2 ^ k.toNat * (hi >>> (k % 64#64)).toNat + (hi &&& mask).toNat = hi.toNat := by
  dsimp only
  rw [BitVec.ushiftRight_eq', umod_64_eq_self hk63, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, toNat_and_mask hi hk63]
  exact Nat.div_add_mod hi.toNat (2 ^ k.toNat)

/-! ### Clamped count-trailing-zeros: `rbit; orr #1; clz`

`(x.reverse ||| 1).clz` is `min (ctz x) (w - 1)`, the clamped trailing-zero count computed by the
`rbit`/`orr`/`clz` idiom (forcing bit `w - 1` of the reversed word makes `clz` well defined for
`x = 0` and bounds the result by `w - 1`). The lemmas below characterise it through core's
`BitVec.ctz` API: `c ≤ w - 1`, bits `0 .. c-1` of `x` are clear (`x mod 2^c = 0`), and bit `c` of
`x` is set unless the count was clamped (`c = w - 1`). -/

/-- Bits of `(x.reverse ||| 1).reverse`: `x` with bit `w - 1` forced. -/
theorem getLsbD_reverse_or_one_reverse (x : BitVec w) (i : Nat) (hw : 0 < w) :
    (x.reverse ||| 1#w).reverse.getLsbD i = (x.getLsbD i || decide (i = w - 1)) := by
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_or, BitVec.getMsbD_reverse, BitVec.getMsbD_eq_getLsbD,
    BitVec.getLsbD_one]
  by_cases hi : i < w
  · have : (w - 1 - i = 0) ↔ (i = w - 1) := by omega
    simp [hi, hw, this]
  · have hx : x.getLsbD i = false := BitVec.getLsbD_of_ge x i (by omega)
    have : ¬ (i = w - 1) := by omega
    simp [hi, hx, this]

theorem reverse_or_one_reverse_ne_zero (x : BitVec w) (hw : 0 < w) :
    (x.reverse ||| 1#w).reverse ≠ 0#w := by
  intro h
  have := getLsbD_reverse_or_one_reverse x (w - 1) hw
  rw [h] at this
  simp at this

/-- The clamped count is `< w`. -/
theorem clz_reverse_or_one_lt (x : BitVec w) (hw : 0 < w) :
    (x.reverse ||| 1#w).clz < BitVec.ofNat w w := by
  rw [BitVec.clz_eq_reverse_ctz]
  exact BitVec.ctz_lt_iff_ne_zero.mpr (reverse_or_one_reverse_ne_zero x hw)

theorem toNat_clz_reverse_or_one_lt (x : BitVec w) (hw : 0 < w) :
    ((x.reverse ||| 1#w).clz).toNat < w := by
  have h := BitVec.lt_def.mp (clz_reverse_or_one_lt x hw)
  rw [BitVec.toNat_ofNat] at h
  exact Nat.lt_of_lt_of_le h (Nat.mod_le _ _)

/-- The clamped count is `≤ 63` for 64-bit words. -/
theorem clz_reverse_or_one_le_63 (x : BitVec 64) : (x.reverse ||| 1#64).clz ≤ 63#64 := by
  have h := toNat_clz_reverse_or_one_lt x (by decide)
  rw [BitVec.le_def]
  change _ ≤ 63
  omega

/-- The bits of `x` below the clamped count are clear. -/
theorem getLsbD_false_of_lt_clz_reverse_or_one {x : BitVec w} {i : Nat} (hw : 0 < w)
    (hi : i < ((x.reverse ||| 1#w).clz).toNat) : x.getLsbD i = false := by
  rw [BitVec.clz_eq_reverse_ctz] at hi
  have h := BitVec.getLsbD_false_of_lt_ctz hi
  rw [getLsbD_reverse_or_one_reverse x i hw] at h
  exact (Bool.or_eq_false_iff.mp h).1

/-- `x mod 2^c = 0` for the clamped count `c`. -/
theorem toNat_mod_two_pow_clz_reverse_or_one (x : BitVec w) (hw : 0 < w) :
    x.toNat % 2 ^ ((x.reverse ||| 1#w).clz).toNat = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
  by_cases hi : i < ((x.reverse ||| 1#w).clz).toNat
  · have h := getLsbD_false_of_lt_clz_reverse_or_one hw hi
    simp only [hi, decide_true, Bool.true_and]
    exact h
  · simp [hi]

/-- Bit `c` of `x` is set unless the count was clamped (`c = w - 1`). -/
theorem getLsbD_clz_reverse_or_one (x : BitVec w) (hw : 0 < w) :
    x.getLsbD ((x.reverse ||| 1#w).clz).toNat = true ∨ ((x.reverse ||| 1#w).clz).toNat = w - 1 := by
  rw [BitVec.clz_eq_reverse_ctz]
  have h := BitVec.getLsbD_true_ctz_of_ne_zero (reverse_or_one_reverse_ne_zero x hw)
  rw [getLsbD_reverse_or_one_reverse x _ hw, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

/-- 64-bit form of `getLsbD_clz_reverse_or_one`. -/
theorem getLsbD_clz_reverse_or_one_64 (x : BitVec 64) :
    x.getLsbD ((x.reverse ||| 1#64).clz).toNat = true ∨ (x.reverse ||| 1#64).clz = 63#64 := by
  rcases getLsbD_clz_reverse_or_one x (by decide) with h | h
  · exact Or.inl h
  · exact Or.inr (BitVec.eq_of_toNat_eq h)

/-- If the clamped count is zero then bit 0 of `x` is set (needs `1 < w`: at width 1 the count is
always clamped to `0`). -/
theorem getLsbD_zero_of_clz_reverse_or_one_eq_zero {x : BitVec w} (hw : 1 < w)
    (h : (x.reverse ||| 1#w).clz = 0#w) : x.getLsbD 0 = true := by
  have hc : ((x.reverse ||| 1#w).clz).toNat = 0 := by rw [h]; simp
  rcases getLsbD_clz_reverse_or_one x (by omega) with h' | h'
  · rwa [hc] at h'
  · omega

/-- `x &&& ((1 <<< c) - 1) = 0` for the clamped count `c` (64-bit form). -/
theorem and_mask_clz_reverse_or_one (x : BitVec 64) :
    x &&& ((1#64 <<< ((x.reverse ||| 1#64).clz % 64#64)) - 1#64) = 0#64 := by
  have hk63 := clz_reverse_or_one_le_63 x
  apply BitVec.eq_of_toNat_eq
  rw [umod_64_eq_self hk63, toNat_and_mask x hk63, toNat_mod_two_pow_clz_reverse_or_one x (by decide)]
  rfl


/-! ### Flags at the value level

Helpers for presenting processor flags (carry, borrow, overflow, condition codes) as decided
value-level facts: `BitVec` addition/subtraction as `Nat` case disjunctions (without `Nat`
subtraction, so `omega` can use them directly), `Int.bmod` facts for signed overflow, and the
compare idiom. -/

/-- `(x + y).toNat` is the exact sum, or the exact sum minus `2^w` on carry-out. -/
theorem toNat_add_cases (x y : BitVec w) :
    (x.toNat + y.toNat < 2 ^ w ∧ (x + y).toNat = x.toNat + y.toNat) ∨
    (2 ^ w ≤ x.toNat + y.toNat ∧ (x + y).toNat + 2 ^ w = x.toNat + y.toNat) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : x.toNat + y.toNat < 2 ^ w
  · exact Or.inl ⟨h, BitVec.toNat_add_of_lt h⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [BitVec.toNat_add, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- `(x - y).toNat` is the exact difference, or the exact difference plus `2^w` on borrow. -/
theorem toNat_sub_cases (x y : BitVec w) :
    (y.toNat ≤ x.toNat ∧ (x - y).toNat + y.toNat = x.toNat) ∨
    (x.toNat < y.toNat ∧ (x - y).toNat + y.toNat = x.toNat + 2 ^ w) := by
  have hx := x.isLt
  have hy := y.isLt
  by_cases h : y.toNat ≤ x.toNat
  · exact Or.inl ⟨h, by rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)]; omega⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [BitVec.toNat_sub_of_lt (BitVec.lt_def.mpr (by omega))]
    omega

theorem toNat_ofNat_toNat_bool (hw : 0 < w) (c : Bool) :
    (BitVec.ofNat w c.toNat).toNat = c.toNat := by
  rw [BitVec.toNat_ofNat]
  cases c
  · simp
  · exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

/-- `x.bmod (2^w) = x` iff `x` is a representable signed `w`-bit value (`0 < w`). -/
theorem _root_.Int.bmod_two_pow_eq_self_iff (hw : 0 < w) (x : Int) :
    x.bmod (2 ^ w) = x ↔ -2 ^ (w - 1) ≤ x ∧ x < 2 ^ (w - 1) := by
  obtain ⟨w, rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  have h2 : (2 ^ (w + 1) : Nat) = 2 * 2 ^ w := by rw [Nat.pow_succ]; omega
  have hlo := Int.le_bmod (x := x) (m := 2 ^ (w + 1)) (Nat.two_pow_pos _)
  have hhi := Int.bmod_lt (x := x) (m := 2 ^ (w + 1)) (Nat.two_pow_pos _)
  simp only [Nat.add_one_sub_one]
  constructor
  · intro h
    rw [h] at hlo hhi
    push_cast [h2] at hlo hhi
    omega
  · rintro ⟨h1, h3⟩
    apply Int.bmod_eq_of_le
    · push_cast [h2]; omega
    · push_cast [h2]; omega

theorem toInt_ofNat_toNat_bool (hw : 1 < w) (c : Bool) :
    (BitVec.ofNat w c.toNat).toInt = c.toNat := by
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat_toNat_bool (by omega)]
  have hn : 2 ≤ 2 ^ (w - 1) := Nat.one_lt_two_pow (by omega)
  have hi : (2 : Int) ≤ 2 ^ (w - 1) := by exact_mod_cast hn
  rw [(Int.bmod_two_pow_eq_self_iff (by omega) _).mpr]
  cases c <;> simp <;> omega


/-- Signed subtraction overflow as a decided range test (not a simp lemma: the `v`/`of` flag
projections present the flag as `ssubOverflow a b`, which simp's numeral folding leaves alone). -/
theorem ssubOverflow_eq_decide (a b : BitVec w) :
    BitVec.ssubOverflow a b =
      decide (a.toInt - b.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ a.toInt - b.toInt) := by
  simp only [BitVec.ssubOverflow, ge_iff_le, Bool.decide_or, Bool.or_comm]

/-- Signed addition overflow as a decided range test. -/
theorem saddOverflow_eq_decide (a b : BitVec w) :
    BitVec.saddOverflow a b =
      decide (a.toInt + b.toInt < -2 ^ (w - 1) ∨ 2 ^ (w - 1) ≤ a.toInt + b.toInt) := by
  simp only [BitVec.saddOverflow, ge_iff_le, Bool.decide_or, Bool.or_comm]

section
variable (a b : BitVec w)

/-! ### The compare idiom: condition codes after `cmp a, b` (`subs`/`sub` flags)

A condition code unfolds to a `Bool` combination of the flag projections (`(subs a b).n != …`);
these `@[kcond]` lemmas fold the combinations back into one decided comparison
(`b.lo` ↦ `decide (a.toNat < b.toNat)`, `b.lt` ↦ `decide (a.toInt < b.toInt)`, …). They are
stated on the simp normal form of the projections, so they apply after them. -/

/-- `LT`: `n ≠ v` after `cmp a, b` is the signed comparison. -/
@[simp, kcond] theorem cmp_lt :
    ((a - b).msb != BitVec.ssubOverflow a b) = decide (a.toInt < b.toInt) := by
  rw [ssubOverflow_eq_decide]
  rcases w with _ | w
  · simp [BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    have h1 := BitVec.toInt_sub_toInt_lt_twoPow_iff (x := a) (y := b)
    have h2 := BitVec.twoPow_le_toInt_sub_toInt_iff (x := a) (y := b)
    have hself := Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega) (a.toInt - b.toInt)
    simp only [Nat.add_one_sub_one] at h1 h2 hself ⊢
    simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, bne_iff_ne, ne_eq, decide_eq_true_eq,
      decide_eq_decide]
    omega

/-- `GE`: `n = v` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_ge :
    ((a - b).msb == BitVec.ssubOverflow a b) = decide (b.toInt ≤ a.toInt) := by
  rw [ssubOverflow_eq_decide]
  rcases w with _ | w
  · simp [BitVec.of_length_zero]
  · rw [Bool.eq_iff_iff]
    have h1 := BitVec.toInt_sub_toInt_lt_twoPow_iff (x := a) (y := b)
    have h2 := BitVec.twoPow_le_toInt_sub_toInt_iff (x := a) (y := b)
    have hself := Int.bmod_two_pow_eq_self_iff (w := w + 1) (by omega) (a.toInt - b.toInt)
    simp only [Nat.add_one_sub_one] at h1 h2 hself ⊢
    simp only [BitVec.msb_eq_toInt, BitVec.toInt_sub, beq_iff_eq, decide_eq_true_eq,
      decide_eq_decide]
    omega

/-- `GT`: `¬z ∧ n = v` after `cmp a, b` (stated on the simp normal form of the projections). -/
@[simp, kcond] theorem cmp_gt :
    (!decide (a = b) && decide (b.toInt ≤ a.toInt)) = decide (b.toInt < a.toInt) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  constructor
  · rintro ⟨hne, hle⟩
    rcases Int.lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (BitVec.toInt_inj.mp h.symm) hne
  · intro h
    exact ⟨fun heq => by subst heq; omega, Int.le_of_lt h⟩

/-- `LE`: `z ∨ n ≠ v` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_le :
    (decide (a = b) || decide (a.toInt < b.toInt)) = decide (a.toInt ≤ b.toInt) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · subst h; omega
    · exact Int.le_of_lt h
  · intro h
    rcases Int.lt_or_eq_of_le h with h | h
    · exact Or.inr h
    · exact Or.inl (BitVec.toInt_inj.mp h)

/-- `HI`: `c ∧ ¬z` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_hi :
    (decide (b.toNat ≤ a.toNat) && !decide (a = b)) = decide (b.toNat < a.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    ← BitVec.toNat_inj]
  omega

/-- `LS`: `¬c ∨ z` after `cmp a, b`. -/
@[simp, kcond] theorem cmp_ls :
    (!decide (b.toNat ≤ a.toNat) || decide (a = b)) = decide (a.toNat ≤ b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    ← BitVec.toNat_inj]
  omega


/-- `BE`/`LS` with the borrow flag (x86 `cf` after `cmp a, b` is `decide (a.toNat < b.toNat)`). -/
@[simp, kcond] theorem cmp_be :
    (decide (a.toNat < b.toNat) || decide (a = b)) = decide (a.toNat ≤ b.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, ← BitVec.toNat_inj]
  omega

/-- `A`/`HI` with the borrow flag. -/
@[simp, kcond] theorem cmp_a :
    (!decide (a.toNat < b.toNat) && !decide (a = b)) = decide (b.toNat < a.toNat) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
    ← BitVec.toNat_inj]
  omega

/-- `LE` with the disjuncts in the x86 order (`(sf != of) || zf`). -/
@[simp, kcond] theorem cmp_le' :
    (decide (a.toInt < b.toInt) || decide (a = b)) = decide (a.toInt ≤ b.toInt) := by
  rw [Bool.or_comm]; exact cmp_le a b

end

/-- Stack-pointer alignment modulo 16 is invariant under adding a 16-byte-aligned offset. -/
@[kcond] theorem add_umod_16_right (a b : BitVec 64) (hb : b % 16#64 = 0#64) :
    (a + b) % 16#64 = a % 16#64 := by
  grind

@[kcond] theorem add_umod_16_left (a b : BitVec 64) (ha : a % 16#64 = 0#64) :
    (a + b) % 16#64 = b % 16#64 := by
  grind

end BitVec

theorem UInt64.getLsbD_zero_eq_false_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = false) :
    x.toNat % 2 = 0 := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_false_iff_not] at h
  rw [← UInt64.toNat_toBitVec]
  omega

theorem UInt64.getLsbD_zero_eq_true_mod2 (x : UInt64) (h : x.toBitVec.getLsbD 0 = true) :
    x.toNat % 2 = 1 := by
  simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_true_eq] at h
  rw [← UInt64.toNat_toBitVec]
  exact h

end
