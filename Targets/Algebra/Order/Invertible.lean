import VerifiedAgora.tagger
/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Lemmas about `invOf` in ordered (semi)rings.
-/

variable {α : Type*} [LinearOrderedSemiring α] {a : α}

@[simp]
theorem invOf_pos [Invertible a] : 0 < ⅟ a ↔ 0 < a :=
  haveI : 0 < a * ⅟ a := by simp only [mul_invOf_self, zero_lt_one]
  ⟨fun h => pos_of_mul_pos_left this h.le, fun h => pos_of_mul_pos_right this h.le⟩

@[target, simp]
theorem invOf_nonpos [Invertible a] : ⅟ a ≤ 0 ↔ a ≤ 0 := by sorry

@[target, simp]
theorem invOf_nonneg [Invertible a] : 0 ≤ ⅟ a ↔ 0 ≤ a :=
  sorry

@[target, simp]
theorem invOf_lt_zero [Invertible a] : ⅟ a < 0 ↔ a < 0 := by sorry

@[simp]
theorem invOf_le_one [Invertible a] (h : 1 ≤ a) : ⅟ a ≤ 1 :=
  mul_invOf_self a ▸ le_mul_of_one_le_left (invOf_nonneg.2 <| zero_le_one.trans h) h

@[target]
theorem pos_invOf_of_invertible_cast [Nontrivial α] (n : ℕ)
    [Invertible (n : α)] : 0 < ⅟(n : α) :=
  sorry