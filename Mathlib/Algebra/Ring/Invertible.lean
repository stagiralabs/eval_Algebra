import VerifiedAgora.tagger
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.Ring.Defs
/-!
# Theorems about invertible elements in rings

-/

universe u

variable {α : Type u}

/-- `-⅟a` is the inverse of `-a` -/
/-- `-⅟a` is the inverse of `-a` -/
def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by sorry


@[target] theorem invOf_neg [Monoid α] [HasDistribNeg α] (a : α) [Invertible a] [Invertible (-a)] :
    ⅟ (-a) = -⅟ a :=
  invOf_eq_right_inv (by sorry


@[target] theorem one_sub_invOf_two [Ring α] [Invertible (2 : α)] : 1 - (⅟ 2 : α) = ⅟ 2 :=
  (isUnit_of_invertible (2 : α)).mul_right_inj.1 <| by
    sorry


@[target] theorem invOf_two_add_invOf_two [NonAssocSemiring α] [Invertible (2 : α)] :
    (⅟ 2 : α) + (⅟ 2 : α) = 1 := by sorry


theorem pos_of_invertible_cast [Semiring α] [Nontrivial α] (n : ℕ) [Invertible (n : α)] : 0 < n :=
  Nat.zero_lt_of_ne_zero fun h => Invertible.ne_zero (n : α) (h ▸ Nat.cast_zero)

@[target] theorem invOf_add_invOf [Semiring α] (a b : α) [Invertible a] [Invertible b] :
    ⅟a + ⅟b = ⅟a * (a + b) * ⅟b := by
  sorry


/-- A version of `inv_sub_inv'` for `invOf`. -/
/-- A version of `inv_sub_inv'` for `invOf`. -/
@[target] theorem invOf_sub_invOf [Ring α] (a b : α) [Invertible a] [Invertible b] :
    ⅟a - ⅟b = ⅟a * (b - a) * ⅟b := by
  sorry


/-- A version of `inv_add_inv'` for `Ring.inverse`. -/
theorem Ring.inverse_add_inverse [Semiring α] {a b : α} (h : IsUnit a ↔ IsUnit b) :
    Ring.inverse a + Ring.inverse b = Ring.inverse a * (a + b) * Ring.inverse b := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_add_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]

/-- A version of `inv_sub_inv'` for `Ring.inverse`. -/
theorem Ring.inverse_sub_inverse [Ring α] {a b : α} (h : IsUnit a ↔ IsUnit b) :
    Ring.inverse a - Ring.inverse b = Ring.inverse a * (b - a) * Ring.inverse b := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]
