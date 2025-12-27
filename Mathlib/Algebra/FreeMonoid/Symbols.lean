import VerifiedAgora.tagger
/-
Copyright (c) 2024 Hannah Fechtner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Fechtner
-/

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Data.Finset.Lattice.Lemmas

/-!
# The finite set of symbols in a FreeMonoid element

This is separated from the main FreeMonoid file, as it imports the finiteness hierarchy
-/

variable {α : Type*} [DecidableEq α]

namespace FreeMonoid

/-- the set of unique symbols in a free monoid element -/
@[to_additive "The set of unique symbols in an additive free monoid element"]
def symbols (a : FreeMonoid α) : Finset α := List.toFinset a

@[to_additive (attr := by sorry


@[target] theorem symbols_mul {a b : FreeMonoid α} : symbols (a * b) = symbols a ∪ symbols b := by
  sorry


@[to_additive (attr := by sorry


end FreeMonoid
