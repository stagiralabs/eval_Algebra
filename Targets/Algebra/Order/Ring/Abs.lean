import VerifiedAgora.tagger
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Absolute values in linear ordered rings.
-/


variable {α : Type*}

section LinearOrderedAddCommGroup
variable [LinearOrderedCommGroup α]

@[to_additive] lemma mabs_zpow (n : ℤ) (a : α) : |a ^ n|ₘ = |a|ₘ ^ |n| := by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [mabs_pow, zpow_natCast, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← mabs_inv, ← zpow_neg, ← abs_neg, h, zpow_natCast, Nat.abs_cast, zpow_natCast]
    exact mabs_pow m _

end LinearOrderedAddCommGroup

@[target]
lemma odd_abs [LinearOrder α] [Ring α] {a : α} : Odd (abs a) ↔ Odd a := by sorry

section LinearOrderedRing

variable [LinearOrderedRing α] {n : ℕ} {a b : α}

@[simp] lemma abs_one : |(1 : α)| = 1 := abs_of_pos zero_lt_one

lemma abs_two : |(2 : α)| = 2 := abs_of_pos zero_lt_two

@[target]
lemma abs_mul (a b : α) : |a * b| = |a| * |b| := by sorry
def absHom : α →*₀ α where
  toFun := abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[target, simp]
lemma abs_pow (a : α) (n : ℕ) : |a ^ n| = |a| ^ n := sorry

@[target]
lemma pow_abs (a : α) (n : ℕ) : |a| ^ n = |a ^ n| := sorry

lemma Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n := by
  rw [← abs_pow, abs_eq_self]; exact hn.pow_nonneg _

@[target]
lemma abs_neg_one_pow (n : ℕ) : |(-1 : α) ^ n| = 1 := by sorry

@[target]
lemma abs_pow_eq_one (a : α) (h : n ≠ 0) : |a ^ n| = 1 ↔ |a| = 1 := by sorry

@[simp] lemma abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
  abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)

@[target, simp]
lemma abs_mul_self (a : α) : |a * a| = a * a := by sorry

@[target]
lemma abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b := by sorry

lemma abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b := by
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

@[target]
lemma abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b := by sorry

@[target]
lemma abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 := by sorry

@[simp] lemma sq_abs (a : α) : |a| ^ 2 = a ^ 2 := by simpa only [sq] using abs_mul_abs_self a

@[target]
lemma abs_sq (x : α) : |x ^ 2| = x ^ 2 := by sorry

lemma sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b| := by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)

@[target]
lemma sq_lt_sq' (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2 :=
  sorry

lemma sq_le_sq : a ^ 2 ≤ b ^ 2 ↔ |a| ≤ |b| := by
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)

lemma sq_le_sq' (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 :=
  sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

lemma abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : |a| < b := by
  rwa [← abs_of_nonneg hb, ← sq_lt_sq]

@[target]
lemma abs_lt_of_sq_lt_sq' (h : a ^ 2 < b ^ 2) (hb : 0 ≤ b) : -b < a ∧ a < b :=
  sorry

lemma abs_le_of_sq_le_sq (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : |a| ≤ b := by
  rwa [← abs_of_nonneg hb, ← sq_le_sq]

@[target]
theorem le_of_sq_le_sq (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b :=
  sorry

@[target]
lemma abs_le_of_sq_le_sq' (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : -b ≤ a ∧ a ≤ b :=
  sorry

@[target]
lemma sq_eq_sq_iff_abs_eq_abs (a b : α) : a ^ 2 = b ^ 2 ↔ |a| = |b| := by sorry

@[simp] lemma sq_le_one_iff_abs_le_one (a : α) : a ^ 2 ≤ 1 ↔ |a| ≤ 1 := by
  simpa only [one_pow, abs_one] using @sq_le_sq _ _ a 1

@[simp] lemma sq_lt_one_iff_abs_lt_one (a : α) : a ^ 2 < 1 ↔ |a| < 1 := by
  simpa only [one_pow, abs_one] using @sq_lt_sq _ _ a 1

@[simp] lemma one_le_sq_iff_one_le_abs (a : α) : 1 ≤ a ^ 2 ↔ 1 ≤ |a| := by
  simpa only [one_pow, abs_one] using @sq_le_sq _ _ 1 a

@[simp] lemma one_lt_sq_iff_one_lt_abs (a : α) : 1 < a ^ 2 ↔ 1 < |a| := by
  simpa only [one_pow, abs_one] using @sq_lt_sq _ _ 1 a

@[target]
lemma exists_abs_lt {α : Type*} [LinearOrderedRing α] (a : α) : ∃ b > 0, |a| < b :=
  sorry

end LinearOrderedRing

section LinearOrderedCommRing

variable [LinearOrderedCommRing α] (a b : α) (n : ℕ)

@[target]
theorem abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b := by sorry

@[target]
lemma abs_unit_intCast (a : ℤˣ) : |((a : ℤ) : α)| = 1 := by sorry

@[target]
theorem abs_pow_sub_pow_le : |a ^ n - b ^ n| ≤ |a - b| * n * max |a| |b| ^ (n - 1) := by sorry

end LinearOrderedCommRing

section

variable [Ring α] [LinearOrder α]

@[target, simp]
theorem abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b := by sorry

@[target]
theorem abs_dvd_self (a : α) : |a| ∣ a :=
  sorry

@[target, simp]
theorem dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b := by sorry

@[target]
theorem self_dvd_abs (a : α) : a ∣ |a| :=
  sorry

@[target]
theorem abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
  sorry

open Nat

section LinearOrderedRing
variable {R : Type*} [LinearOrderedRing R] {a b : R} {n : ℕ}

@[target]
lemma pow_eq_pow_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  sorry

lemma pow_eq_pow_iff_cases : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]

@[target]
lemma pow_eq_one_iff_of_ne_zero (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by sorry

lemma pow_eq_one_iff_cases : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_cases]

@[target]
lemma pow_eq_neg_pow_iff (hb : b ≠ 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  sorry

lemma pow_eq_neg_one_iff : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

end LinearOrderedRing

variable {m n a : ℕ}

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
lemma Odd.mod_even_iff (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
lemma Even.mod_even_iff (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <|
      even_iff_two_dvd.mpr <| (even_iff_two_dvd.mp ha).trans <| dvd_sub_mod n).symm

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
lemma Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a) := (Odd.mod_even_iff ha).mpr hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
@[target]
lemma Even.mod_even (hn : Even n) (ha : Even a) : Even (n % a) :=
  sorry

lemma Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m :=
  not_even_iff_odd.1 <| mt hm.even (not_even_iff_odd.2 hn)

/-- `2` is not a factor of an odd natural number. -/
@[target]
lemma Odd.ne_two_of_dvd_nat {m n : ℕ} (hn : Odd n) (hm : m ∣ n) : m ≠ 2 := by sorry