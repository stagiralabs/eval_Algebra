import VerifiedAgora.tagger
/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
# Lemma about subtraction in ordered monoids with a top element adjoined.

This file introduces a subtraction on `WithTop α` when `α` has a subtraction and a bottom element,
given by `x - ⊤ = ⊥` and `⊤ - x = ⊤`. This will be instantiated mostly for `ℕ∞` and `ℝ≥0∞`, where
the bottom element is zero.

Note that there is another subtraction on objects of the form `WithTop α` in the file
`Mathlib.Algebra.Order.Group.WithTop`, setting `-⊤ = ⊤` as this corresponds to the additivization
of the usual convention `0⁻¹ = 0` and is relevant in valuation theory. Since this other instance
is only registered for `LinearOrderedAddCommGroup α` (which doesn't have a bottom element, unless
the group is trivial), this shouldn't create diamonds.
-/

variable {α β : Type*}

namespace WithTop

section

variable [Sub α] [Bot α]

/-- If `α` has a subtraction and a bottom element, we can extend the subtraction to `WithTop α`, by
setting `x - ⊤ = ⊥` and `⊤ - x = ⊤`. -/
protected def sub : ∀ _ _ : WithTop α, WithTop α
  | _, ⊤ => (⊥ : α)
  | ⊤, (x : α) => ⊤
  | (x : α), (y : α) => (x - y : α)

instance : Sub (WithTop α) :=
  ⟨WithTop.sub⟩

@[simp, norm_cast]
theorem coe_sub {a b : α} : (↑(a - b) : WithTop α) = ↑a - ↑b :=
  rfl

@[simp]
theorem top_sub_coe {a : α} : (⊤ : WithTop α) - a = ⊤ :=
  rfl

@[target] theorem sub_top {a : WithTop α} : a - ⊤ = ⊤ := by sorry


@[target] lemma sub_eq_top_iff {a b : WithTop α} : a - b = ⊤ ↔ (a = ⊤ ∨ b = ⊤) := by
  sorry


lemma sub_ne_top_iff {a b : WithTop α} : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := by simp [or_iff_not_imp_left]

protected theorem map_sub : f (x - y) = f x - f y := by sorry


end

variable [Add α] [LE α] [OrderBot α] [Sub α] [OrderedSub α]

instance : OrderedSub (WithTop α) := by
  constructor
  rintro x y z
  cases y
  · cases z <;> simp
  cases x
  · simp
  cases z
  · simp
  norm_cast
  exact tsub_le_iff_right

end WithTop
