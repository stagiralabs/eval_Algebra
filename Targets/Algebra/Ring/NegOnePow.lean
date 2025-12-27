import VerifiedAgora.tagger
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Integer powers of (-1)

This file defines the map `negOnePow : ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.

The definition of `negOnePow` and some lemmas first appeared in contributions by
Johan Commelin to the Liquid Tensor Experiment.

-/

assert_not_exists Field
assert_not_exists TwoSidedIdeal

namespace Int

/-- The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`. -/
def negOnePow (n : ℤ) : ℤˣ := (-1 : ℤˣ) ^ n

@[target]
lemma negOnePow_def (n : ℤ) : n.negOnePow = (-1 : ℤˣ) ^ n := sorry

@[target]
lemma negOnePow_add (n₁ n₂ : ℤ) :
    (n₁ + n₂).negOnePow =  n₁.negOnePow * n₂.negOnePow :=
  sorry

@[target, simp]
lemma negOnePow_zero : negOnePow 0 = 1 := sorry

@[target, simp]
lemma negOnePow_one : negOnePow 1 = -1 := sorry

@[target]
lemma negOnePow_succ (n : ℤ) : (n + 1).negOnePow = - n.negOnePow := by sorry

@[target]
lemma negOnePow_even (n : ℤ) (hn : Even n) : n.negOnePow = 1 := by sorry

@[simp]
lemma negOnePow_two_mul (n : ℤ) : (2 * n).negOnePow = 1 :=
  negOnePow_even _ ⟨n, two_mul n⟩

@[target]
lemma negOnePow_odd (n : ℤ) (hn : Odd n) : n.negOnePow = -1 := by sorry

@[target, simp]
lemma negOnePow_two_mul_add_one (n : ℤ) : (2 * n + 1).negOnePow = -1 :=
  sorry

@[target]
lemma negOnePow_eq_one_iff (n : ℤ) : n.negOnePow = 1 ↔ Even n := by sorry

lemma negOnePow_eq_neg_one_iff (n : ℤ) : n.negOnePow = -1 ↔ Odd n := by
  constructor
  · intro h
    rw [← Int.not_even_iff_odd]
    intro h'
    rw [negOnePow_even _ h'] at h
    contradiction
  · exact negOnePow_odd n

@[simp]
theorem abs_negOnePow (n : ℤ) : |(n.negOnePow : ℤ)| = 1 := by
  rw [abs_eq_natAbs, Int.units_natAbs, Nat.cast_one]

@[target, simp]
lemma negOnePow_neg (n : ℤ) : (-n).negOnePow = n.negOnePow := by sorry

@[target, simp]
lemma negOnePow_abs (n : ℤ) : |n|.negOnePow = n.negOnePow := by sorry

@[target]
lemma negOnePow_sub (n₁ n₂ : ℤ) :
    (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow := by sorry

lemma negOnePow_eq_iff (n₁ n₂ : ℤ) :
    n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  · rw [negOnePow_even _ h₂, Int.even_sub, negOnePow_eq_one_iff]
    tauto
  · rw [Int.not_even_iff_odd] at h₂
    rw [negOnePow_odd _ h₂, Int.even_sub, negOnePow_eq_neg_one_iff,
      ← Int.not_odd_iff_even, ← Int.not_odd_iff_even]
    tauto

@[target, simp]
lemma negOnePow_mul_self (n : ℤ) : (n * n).negOnePow = n.negOnePow := by sorry

@[target]
lemma cast_negOnePow_natCast (R : Type*) [Ring R] (n : ℕ) : negOnePow n = (-1 : R) ^ n := by sorry

lemma coe_negOnePow_natCast (n : ℕ) : negOnePow n = (-1 : ℤ) ^ n := cast_negOnePow_natCast ..

end Int
