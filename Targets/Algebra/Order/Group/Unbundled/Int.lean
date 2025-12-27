import VerifiedAgora.tagger
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic

/-!
# Facts about `ℤ` as an (unbundled) ordered group

See note [foundational algebra order theory].

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton Ring

open Function Nat

namespace Int

@[target]
theorem natCast_strictMono : StrictMono (· : ℕ → ℤ) := sorry

theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| ofNat_zero_le _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _

@[simp, norm_cast] lemma natCast_natAbs (n : ℤ) : (n.natAbs : ℤ) = |n| := n.abs_eq_natAbs.symm

@[target]
theorem natAbs_abs (a : ℤ) : natAbs |a| = natAbs a := by sorry

theorem sign_mul_abs (a : ℤ) : sign a * |a| = a := by
  rw [abs_eq_natAbs, sign_mul_natAbs a]

theorem sign_mul_self_eq_abs (a : ℤ) : sign a * a = |a| := by
  rw [abs_eq_natAbs, sign_mul_self_eq_natAbs]

@[target]
lemma natAbs_le_self_sq (a : ℤ) : (Int.natAbs a : ℤ) ≤ a ^ 2 := by sorry

lemma le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

@[norm_cast] lemma abs_natCast (n : ℕ) : |(n : ℤ)| = n := abs_of_nonneg (natCast_nonneg n)

theorem natAbs_sub_pos_iff {i j : ℤ} : 0 < natAbs (i - j) ↔ i ≠ j := by
  rw [natAbs_pos, ne_eq, sub_eq_zero]

@[target]
theorem natAbs_sub_ne_zero_iff {i j : ℤ} : natAbs (i - j) ≠ 0 ↔ i ≠ j :=
  sorry

@[target, simp]
theorem abs_lt_one_iff {a : ℤ} : |a| < 1 ↔ a = 0 := by sorry

@[target]
theorem abs_le_one_iff {a : ℤ} : |a| ≤ 1 ↔ a = 0 ∨ a = 1 ∨ a = -1 := by sorry

@[target]
theorem one_le_abs {z : ℤ} (h₀ : z ≠ 0) : 1 ≤ |z| :=
  sorry

lemma eq_zero_of_abs_lt_dvd {m x : ℤ} (h1 : m ∣ x) (h2 : |x| < m) : x = 0 := by
  by_contra h
  have := Int.natAbs_le_of_dvd_ne_zero h1 h
  rw [Int.abs_eq_natAbs] at h2
  omega

@[target]
lemma abs_sub_lt_of_lt_lt {m a b : ℕ} (ha : a < m) (hb : b < m) : |(b : ℤ) - a| < m := by sorry

@[target]
theorem ediv_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 :=
  sorry

@[target, simp]
theorem emod_abs (a b : ℤ) : a % |b| = a % b :=
  sorry

theorem emod_lt (a : ℤ) {b : ℤ} (H : b ≠ 0) : a % b < |b| := by
  rw [← emod_abs]; exact emod_lt_of_pos _ (abs_pos.2 H)

/-! ### properties of `/` and `%` -/

@[target]
theorem abs_ediv_le_abs : ∀ a b : ℤ, |a / b| ≤ |a| :=
  sorry

theorem abs_sign_of_nonzero {z : ℤ} (hz : z ≠ 0) : |z.sign| = 1 := by
  rw [abs_eq_natAbs, natAbs_sign_of_nonzero hz, Int.ofNat_one]

protected theorem sign_eq_ediv_abs (a : ℤ) : sign a = a / |a| :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left (mt abs_eq_zero.1 az) (sign_mul_abs _).symm).symm

protected theorem sign_eq_abs_ediv (a : ℤ) : sign a = |a| / a :=
  if az : a = 0 then by simp [az]
  else (Int.ediv_eq_of_eq_mul_left az (sign_mul_self_eq_abs _).symm).symm

end Int

section Group
variable {G : Type*} [Group G]

@[target, to_additive (attr := by sorry

end Group
