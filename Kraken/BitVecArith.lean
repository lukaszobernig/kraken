module

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

/-- `x >> k = x / 2^k`. -/
theorem toNat_ushiftRight_bv (x k : BitVec 64) :
    (x >>> k).toNat = x.toNat / 2 ^ k.toNat := by
  rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `ubfm`/`lsr #k` with an immediate: extracting the low `m ≥ w - k` bits of `x >>> k` and
re-extending to `w` bits is the identity (the top `k` bits are already zero). -/
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
`extr`-style instructions with immediate shift amounts). -/
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

end BitVec

end
