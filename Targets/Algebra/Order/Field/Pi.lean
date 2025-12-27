import VerifiedAgora.tagger
/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Lemmas about (finite domain) functions into fields.

We split this from `Algebra.Order.Field.Basic` to avoid importing the finiteness hierarchy there.
-/

variable {α ι : Type*} [LinearOrderedCancelAddCommMonoid α] [Nontrivial α] [DenselyOrdered α]

@[target]
theorem Pi.exists_forall_pos_add_lt [ExistsAddOfLE α] [Finite ι] {x y : ι → α}
    (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i := by sorry