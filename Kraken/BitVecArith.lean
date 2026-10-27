module

public import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide

/-!
# 64-bit shift / mask arithmetic

Instruction-level identities relating `BitVec 64` shifts, masks and funnel shifts to `Nat`
arithmetic (`/ 2^k`, `% 2^k`, `* 2^(64-k)`). They let multi-limb proofs stay at the `Nat`/`Int`
level (`omega`, `grind`) instead of running `bv_decide` on wide multiplications.

Policy for `bv_decide` in Kraken proofs: use it only for facts that are at most 64 bits wide and
contain no (non-constant) multiplication or division — those are decided in milliseconds. Anything
wider, or with `*`/`/`, should go through `BitVec.toNat` and the lemmas below.
-/

public section

namespace BitVec

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

theorem two_pow_mul_two_pow_sub {k : BitVec 64} (hk63 : k ≤ 63#64) :
    2 ^ k.toNat * 2 ^ (64 - k.toNat) = 2 ^ 64 := by
  have hk := toNat_le_63 hk63
  rw [← Nat.pow_add]; congr 1; omega

/-- `x << (64 - k) = (x mod 2^k) · 2^(64-k)` (the bits of `x` that survive the shift). -/
theorem toNat_shiftLeft_neg (x : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    (x <<< ((0#64 - k) % 64#64)).toNat = (x.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [BitVec.shiftLeft_eq', toNat_neg_umod_64 hk1 hk63, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    ← two_pow_mul_two_pow_sub hk63, Nat.mul_mod_mul_right]

/-- The two halves of a funnel shift occupy disjoint bit ranges, so `|||` is `+`
(64-bit, no multiplication: cheap for `bv_decide`). -/
theorem funnel_or_eq_add (lo hi k : BitVec 64) (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))) =
      (lo >>> (k % 64#64)) + (hi <<< ((0#64 - k) % 64#64)) := by
  bv_decide

/-- The funnel-shifted limb as a number: `lo / 2^k + (hi mod 2^k) · 2^(64-k)` (no overflow). -/
theorem toNat_funnel (lo hi : BitVec 64) {k : BitVec 64} (hk1 : 1#64 ≤ k) (hk63 : k ≤ 63#64) :
    ((lo >>> (k % 64#64)) ||| (hi <<< ((0#64 - k) % 64#64))).toNat =
      lo.toNat / 2 ^ k.toNat + (hi.toNat % 2 ^ k.toNat) * 2 ^ (64 - k.toNat) := by
  rw [funnel_or_eq_add lo hi k hk1 hk63, umod_64_eq_self hk63, BitVec.toNat_add,
    toNat_ushiftRight_bv lo k, toNat_shiftLeft_neg hi hk1 hk63]
  apply Nat.mod_eq_of_lt
  have hpq := two_pow_mul_two_pow_sub hk63
  have hB : hi.toNat % 2 ^ k.toNat < 2 ^ k.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hA : lo.toNat / 2 ^ k.toNat < 2 ^ (64 - k.toNat) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, hpq]; exact lo.isLt
  have h1 : (hi.toNat % 2 ^ k.toNat + 1) * 2 ^ (64 - k.toNat) ≤ 2 ^ k.toNat * 2 ^ (64 - k.toNat) :=
    Nat.mul_le_mul_right _ hB
  rw [hpq, Nat.add_mul, Nat.one_mul] at h1
  omega

end BitVec

end
