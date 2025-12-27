import VerifiedAgora.tagger
/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Semiconj
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about commuting elements in a `MonoidWithZero` or a `GroupWithZero`.

-/

assert_not_exists DenselyOrdered

variable {M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Ring

theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) :
    inverse (a * b) = inverse b * inverse a := by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.isUnit_mul_iff.mp hab
    rw [← Units.val_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.val_mul, mul_inv_rev]
  obtain ha | hb := not_and_or.mp (mt h.isUnit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]

@[target]
theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    Ring.inverse (a * b) = inverse b * inverse a :=
  sorry

@[target]
lemma inverse_pow (r : M₀) : ∀ n : ℕ, Ring.inverse r ^ n = Ring.inverse (r ^ n)
  | 0 => by rw [pow_zero, pow_zero, Ring.inverse_one]
  | n + 1 => by
    rw [pow_succ', pow_succ, Ring.mul_inverse_rev' ((Commute.refl r).pow_left n),
      Ring.inverse_pow r n]

end Ring

theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) :
    Commute (Ring.inverse a) (Ring.inverse b) :=
  sorry

namespace Commute

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

@[target, simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  sorry

variable [GroupWithZero G₀] {a b c : G₀}

@[target, simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  sorry

@[target]
theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  sorry

@[target, simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  sorry

@[target]
theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  sorry

@[target, simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  sorry

@[target, simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by sorry

end Commute

section GroupWithZero
variable [GroupWithZero G₀]

@[target]
theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  sorry

end GroupWithZero
