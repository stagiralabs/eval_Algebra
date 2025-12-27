import VerifiedAgora.tagger
/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Regular.Basic

/-!
# Product of regular elements

## TODO

Move to `Mathlib.Algebra.BigOperators.Group.Finset.Basic`?
-/


variable {R : Type*} {a b : R}

section CommMonoid

variable {ι R : Type*} [CommMonoid R] {s : Finset ι} {f : ι → R}

@[target]
lemma IsLeftRegular.prod (h : ∀ i ∈ s, IsLeftRegular (f i)) :
    IsLeftRegular (∏ i ∈ s, f i) :=
  sorry

lemma IsRightRegular.prod (h : ∀ i ∈ s, IsRightRegular (f i)) :
    IsRightRegular (∏ i ∈ s, f i) :=
  s.prod_induction _ _ (@IsRightRegular.mul R _) isRegular_one.right h

@[target]
lemma IsRegular.prod (h : ∀ i ∈ s, IsRegular (f i)) :
    IsRegular (∏ i ∈ s, f i) :=
  sorry

end CommMonoid
