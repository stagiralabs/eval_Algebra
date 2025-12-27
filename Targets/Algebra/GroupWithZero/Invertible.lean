import VerifiedAgora.tagger
/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Theorems about invertible elements in a `GroupWithZero`

We intentionally keep imports minimal here as this file is used by `Mathlib.Tactic.NormNum`.
-/

assert_not_exists DenselyOrdered

universe u

variable {α : Type u}

@[target]
theorem Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  sorry

@[deprecated (since := "2024-08-15")] alias nonzero_of_invertible := Invertible.ne_zero

instance (priority := 100) Invertible.toNeZero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨Invertible.ne_zero a⟩

section MonoidWithZero
variable [MonoidWithZero α]

/-- A variant of `Ring.inverse_unit`. -/
@[target, simp]
theorem Ring.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  sorry

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel₀ h, mul_inv_cancel₀ h⟩

@[target, simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  sorry

@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel₀ (Invertible.ne_zero a)

@[target, simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  sorry
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩

@[simp]
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel₀ a (Invertible.ne_zero b)

@[target, simp]
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  sorry

@[target, simp]
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  sorry
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩

@[target]
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟ (a / b) = b / a :=
  sorry

end GroupWithZero
