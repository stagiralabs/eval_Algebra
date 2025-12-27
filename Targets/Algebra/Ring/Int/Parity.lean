import VerifiedAgora.tagger
/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Group.Int.Even

/-!
# Basic parity lemmas for the ring `ℤ`

See note [foundational algebra order theory].
-/

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/-! #### Parity -/

variable {m n : ℤ}

@[target]
lemma odd_iff : Odd n ↔ n % 2 = 1 where
  mp := sorry

lemma not_odd_iff : ¬Odd n ↔ n % 2 = 0 := by rw [odd_iff, emod_two_ne_one]

@[simp] lemma not_odd_zero : ¬Odd (0 : ℤ) := not_odd_iff.mpr rfl

@[simp] lemma not_odd_iff_even : ¬Odd n ↔ Even n := by rw [not_odd_iff, even_iff]
@[simp] lemma not_even_iff_odd : ¬Even n ↔ Odd n := by rw [not_even_iff, odd_iff]

@[target, deprecated not_odd_iff_even (since := by sorry

@[deprecated not_even_iff_odd (since := "2024-08-21")]
lemma odd_iff_not_even : Odd n ↔ ¬Even n := by rw [not_even_iff, odd_iff]

lemma even_or_odd (n : ℤ) : Even n ∨ Odd n := Or.imp_right not_even_iff_odd.1 <| em <| Even n

@[target]
lemma even_or_odd' (n : ℤ) : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := by sorry

lemma even_xor'_odd (n : ℤ) : Xor' (Even n) (Odd n) := by
  cases even_or_odd n with
  | inl h => exact Or.inl ⟨h, not_odd_iff_even.2 h⟩
  | inr h => exact Or.inr ⟨h, not_even_iff_odd.2 h⟩

@[target]
lemma even_xor'_odd' (n : ℤ) : ∃ k, Xor' (n = 2 * k) (n = 2 * k + 1) := by sorry

instance : DecidablePred (Odd : ℤ → Prop) := fun _ => decidable_of_iff _ not_even_iff_odd

@[target]
lemma even_add' : Even (m + n) ↔ (Odd m ↔ Odd n) := by sorry

@[target]
lemma not_even_two_mul_add_one (n : ℤ) : ¬ Even (2 * n + 1) :=
  sorry

lemma even_sub' : Even (m - n) ↔ (Odd m ↔ Odd n) := by
  rw [even_sub, ← not_odd_iff_even, ← not_odd_iff_even, not_iff_not]

lemma odd_mul : Odd (m * n) ↔ Odd m ∧ Odd n := by simp [← not_even_iff_odd, not_or, parity_simps]

lemma Odd.of_mul_left (h : Odd (m * n)) : Odd m := (odd_mul.mp h).1

@[target]
lemma Odd.of_mul_right (h : Odd (m * n)) : Odd n := sorry

@[parity_simps] lemma odd_pow {n : ℕ} : Odd (m ^ n) ↔ Odd m ∨ n = 0 := by
  rw [← not_iff_not, not_odd_iff_even, not_or, not_odd_iff_even, even_pow]

@[target]
lemma odd_pow' {n : ℕ} (h : n ≠ 0) : Odd (m ^ n) ↔ Odd m := sorry

@[parity_simps] lemma odd_add : Odd (m + n) ↔ (Odd m ↔ Even n) := by
  rw [← not_even_iff_odd, even_add, not_iff, ← not_even_iff_odd]

@[target]
lemma odd_add' : Odd (m + n) ↔ (Odd n ↔ Even m) := by sorry

@[target]
lemma ne_of_odd_add (h : Odd (m + n)) : m ≠ n := by sorry

@[parity_simps] lemma odd_sub : Odd (m - n) ↔ (Odd m ↔ Even n) := by
  rw [← not_even_iff_odd, even_sub, not_iff, ← not_even_iff_odd]

@[target]
lemma odd_sub' : Odd (m - n) ↔ (Odd n ↔ Even m) := by sorry

@[target]
lemma even_mul_succ_self (n : ℤ) : Even (n * (n + 1)) := by sorry

@[target]
lemma even_mul_pred_self (n : ℤ) : Even (n * (n - 1)) := by sorry

@[simp, norm_cast] lemma odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by
  rw [← not_even_iff_odd, ← Nat.not_even_iff_odd, even_coe_nat]

@[simp] lemma natAbs_even : Even n.natAbs ↔ Even n := by
  simp [even_iff_two_dvd, dvd_natAbs, natCast_dvd.symm]

@[target, simp]
lemma natAbs_odd : Odd n.natAbs ↔ Odd n := by sorry

@[target]
lemma four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) :
    4 ∣ a + b ∨ 4 ∣ a - b := by sorry

@[target]
lemma two_mul_ediv_two_add_one_of_odd : Odd n → 2 * (n / 2) + 1 = n := by sorry

lemma ediv_two_mul_two_add_one_of_odd : Odd n → n / 2 * 2 + 1 = n := by
  rintro ⟨c, rfl⟩
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]

lemma add_one_ediv_two_mul_two_of_odd : Odd n → 1 + n / 2 * 2 = n := by
  rintro ⟨c, rfl⟩
  rw [add_comm]
  convert Int.ediv_add_emod' (2 * c + 1) 2
  simp [Int.add_emod]

@[target]
lemma two_mul_ediv_two_of_odd (h : Odd n) : 2 * (n / 2) = n - 1 :=
  sorry

@[target, norm_cast, simp]
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℤ) ↔ IsSquare n := by sorry

@[simp]
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℤ) ↔ IsSquare (ofNat(n) : ℕ) :=
  isSquare_natCast_iff

end Int
