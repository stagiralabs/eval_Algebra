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

@[target] theorem invOf_pos [Invertible a] : 0 < ⅟ a ↔ 0 < a :=
  haveI : 0 < a * ⅟ a := by sorry


@[simp]
theorem invOf_nonpos [Invertible a] : ⅟ a ≤ 0 ↔ a ≤ 0 := by simp only [← not_lt, invOf_pos]

@[target] theorem invOf_nonneg [Invertible a] : 0 ≤ ⅟ a ↔ 0 ≤ a :=
  haveI : 0 < a * ⅟ a := by sorry


@[simp]
theorem invOf_lt_zero [Invertible a] : ⅟ a < 0 ↔ a < 0 := by simp only [← not_le, invOf_nonneg]

@[target] theorem invOf_le_one [Invertible a] (h : 1 ≤ a) : ⅟ a ≤ 1 := by sorry


@[target] theorem pos_invOf_of_invertible_cast [Nontrivial α] (n : ℕ)
    [Invertible (n : α)] : 0 < ⅟(n : α) := by sorry
