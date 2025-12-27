import VerifiedAgora.tagger
/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend

/-!
# Quadratic discriminants and roots of a quadratic

This file defines the discriminant of a quadratic and gives the solution to a quadratic equation.

## Main definition

- `discrim a b c`: the discriminant of a quadratic `a * (x * x) + b * x + c` is `b * b - 4 * a * c`.

## Main statements

- `quadratic_eq_zero_iff`: roots of a quadratic can be written as
  `(-b + s) / (2 * a)` or `(-b - s) / (2 * a)`, where `s` is a square root of the discriminant.
- `quadratic_ne_zero_of_discrim_ne_sq`: if the discriminant has no square root,
  then the corresponding quadratic has no root.
- `discrim_le_zero`: if a quadratic is always non-negative, then its discriminant is non-positive.
- `discrim_le_zero_of_nonpos`, `discrim_lt_zero`, `discrim_lt_zero_of_neg`: versions of this
  statement with other inequalities.

## Tags

polynomial, quadratic, discriminant, root
-/


open Filter

section Ring

variable {R : Type*}

/-- Discriminant of a quadratic -/
/-- Discriminant of a quadratic -/
def discrim [Ring R] (a b c : R) : R := by sorry


@[target] lemma discrim_neg [Ring R] (a b c : R) : discrim (-a) (-b) (-c) = discrim a b c := by
  sorry


variable [CommRing R] {a b c : R}

@[target] lemma discrim_eq_sq_of_quadratic_eq_zero {x : R} (h : a * (x * x) + b * x + c = 0) :
    discrim a b c = (2 * a * x + b) ^ 2 := by
  sorry


/-- A quadratic has roots if and only if its discriminant equals some square.
-/
/-- A quadratic has roots if and only if its discriminant equals some square.
-/
@[target] theorem quadratic_eq_zero_iff_discrim_eq_sq [NeZero (2 : R)] [NoZeroDivisors R]
    (ha : a ≠ 0) (x : R) :
    a * (x * x) + b * x + c = 0 ↔ discrim a b c = (2 * a * x + b) ^ 2 := by
  sorry


/-- A quadratic has no root if its discriminant has no square root. -/
/-- A quadratic has no root if its discriminant has no square root. -/
@[target] theorem quadratic_ne_zero_of_discrim_ne_sq (h : ∀ s : R, discrim a b c ≠ s^2) (x : R) :
    a * (x * x) + b * x + c ≠ 0 := by sorry


end Ring

section Field

variable {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K}

/-- Roots of a quadratic equation. -/
theorem quadratic_eq_zero_iff (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [quadratic_eq_zero_iff_discrim_eq_sq ha, h, sq, mul_self_eq_mul_self_iff]
  field_simp
  apply or_congr
  · constructor <;> intro h' <;> linear_combination -h'
  · constructor <;> intro h' <;> linear_combination h'

/-- A quadratic has roots if its discriminant has square roots -/
theorem exists_quadratic_eq_zero (ha : a ≠ 0) (h : ∃ s, discrim a b c = s * s) :
    ∃ x, a * (x * x) + b * x + c = 0 := by
  rcases h with ⟨s, hs⟩
  use (-b + s) / (2 * a)
  rw [quadratic_eq_zero_iff ha hs]
  simp

/-- Root of a quadratic when its discriminant equals zero -/
/-- Root of a quadratic when its discriminant equals zero -/
@[target] theorem quadratic_eq_zero_iff_of_discrim_eq_zero (ha : a ≠ 0) (h : discrim a b c = 0) (x : K) :
    a * (x * x) + b * x + c = 0 ↔ x = -b / (2 * a) := by
  sorry


@[target] theorem discrim_eq_zero_of_existsUnique (ha : a ≠ 0) (h : ∃! x, a * (x * x) + b * x + c = 0) :
    discrim a b c = 0 := by
  sorry


@[target] theorem discrim_eq_zero_iff (ha : a ≠ 0) :
    discrim a b c = 0 ↔ (∃! x, a * (x * x) + b * x + c = 0) := by
  sorry


end Field

section LinearOrderedField

variable {K : Type*} [LinearOrderedField K] {a b c : K}

/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
/-- If a polynomial of degree 2 is always nonnegative, then its discriminant is nonpositive -/
@[target] theorem discrim_le_zero (h : ∀ x : K, 0 ≤ a * (x * x) + b * x + c) : discrim a b c ≤ 0 := by
  sorry


lemma discrim_le_zero_of_nonpos (h : ∀ x : K, a * (x * x) + b * x + c ≤ 0) : discrim a b c ≤ 0 :=
  discrim_neg a b c ▸ discrim_le_zero <| by simpa only [neg_mul, ← neg_add, neg_nonneg]

/-- If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
/-- If a polynomial of degree 2 is always positive, then its discriminant is negative,
at least when the coefficient of the quadratic term is nonzero.
-/
@[target] theorem discrim_lt_zero (ha : a ≠ 0) (h : ∀ x : K, 0 < a * (x * x) + b * x + c) :
    discrim a b c < 0 := by
  sorry


@[target] lemma discrim_lt_zero_of_neg (ha : a ≠ 0) (h : ∀ x : K, a * (x * x) + b * x + c < 0) :
    discrim a b c < 0 :=
  discrim_neg a b c ▸ discrim_lt_zero (neg_ne_zero.2 ha) <| by
    sorry


end LinearOrderedField
