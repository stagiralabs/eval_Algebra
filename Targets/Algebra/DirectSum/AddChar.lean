import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Group.AddChar

/-!
# Direct sum of additive characters

This file defines the direct sum of additive characters.
-/

open Function
open scoped DirectSum

variable {ι R : Type*} {G : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (G i)] [CommMonoid R]

namespace AddChar
section DirectSum

/-- Direct sum of additive characters. -/
@[simps!]
def directSum (ψ : ∀ i, AddChar (G i) R) : AddChar (⨁ i, G i) R :=
  toAddMonoidHomEquiv.symm <| DirectSum.toAddMonoid fun i ↦ toAddMonoidHomEquiv (ψ i)

@[target]
lemma directSum_injective :
    Injective (directSum : (∀ i, AddChar (G i) R) → AddChar (⨁ i, G i) R) := by sorry

end DirectSum
end AddChar
