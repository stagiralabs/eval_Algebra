import VerifiedAgora.tagger
/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Lemmas about divisibility in rings

## Main results:
* `dvd_smul_of_dvd`: stating that `x ∣ y → x ∣ m • y` for any scalar `m`.
* `Commute.pow_dvd_add_pow_of_pow_eq_zero_right`: stating that if `y` is nilpotent then
  `x ^ m ∣ (x + y) ^ p` for sufficiently large `p` (together with many variations for convenience).
-/

variable {R : Type*}

@[target]
lemma dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R] {x y : R}
    (m : M) (h : x ∣ y) : x ∣ m • y :=
  sorry

lemma dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : ℕ) (h : x ∣ y) : x ∣ n • y :=
  dvd_smul_of_dvd n h

@[target]
lemma dvd_zsmul_of_dvd [NonUnitalRing R] {x y : R} (z : ℤ) (h : x ∣ y) : x ∣ z • y :=
  sorry

namespace Commute

variable {x y : R} {n m p : ℕ}

section Semiring

variable [Semiring R]

@[target]
lemma pow_dvd_add_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x + y) ^ p := by sorry

lemma pow_dvd_add_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x + y) ^ p :=
  add_comm x y ▸ h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right hp hx

end Semiring

section Ring

variable [Ring R]

@[target]
lemma pow_dvd_pow_of_sub_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ p := by sorry

lemma pow_dvd_pow_of_add_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x + y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← neg_neg y, neg_pow']
  apply dvd_mul_of_dvd_left
  apply h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero hp
  simpa

@[target]
lemma pow_dvd_sub_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x - y) ^ p :=
  sorry

@[target]
lemma pow_dvd_sub_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x - y) ^ p := by sorry

@[target]
lemma add_pow_dvd_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : (x + y) ^ m ∣ y ^ p :=
  sorry

@[target]
lemma add_pow_dvd_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : (x + y) ^ m ∣ x ^ p :=
  sorry

end Ring

end Commute
section CommRing

variable [CommRing R]

lemma dvd_mul_sub_mul_mul_left_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * x := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨d * k1 - b * k2, ?_⟩
  rw [show (a * d - b * c) * x = a * x * d - c * x * b by ring, eq_sub_of_add_eq hk1,
    eq_sub_of_add_eq hk2]
  ring

@[target]
lemma dvd_mul_sub_mul_mul_right_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * y :=
  sorry

@[target]
lemma dvd_mul_sub_mul_mul_gcd_of_dvd {p a b c d x y : R} [IsDomain R] [GCDMonoid R]
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * gcd x y := by sorry

end CommRing
