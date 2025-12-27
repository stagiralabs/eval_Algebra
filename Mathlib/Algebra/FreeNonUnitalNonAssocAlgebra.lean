import VerifiedAgora.tagger
/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Free
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Free algebras

Given a semiring `R` and a type `X`, we construct the free non-unital, non-associative algebra on
`X` with coefficients in `R`, together with its universal property. The construction is valuable
because it can be used to build free algebras with more structure, e.g., free Lie algebras.

Note that elsewhere we have a construction of the free unital, associative algebra. This is called
`FreeAlgebra`.

## Main definitions

  * `FreeNonUnitalNonAssocAlgebra`
  * `FreeNonUnitalNonAssocAlgebra.lift`
  * `FreeNonUnitalNonAssocAlgebra.of`

## Implementation details

We construct the free algebra as the magma algebra, with coefficients in `R`, of the free magma on
`X`. However we regard this as an implementation detail and thus deliberately omit the lemmas
`of_apply` and `lift_apply`, and we mark `FreeNonUnitalNonAssocAlgebra` and `lift` as
irreducible once we have established the universal property.

## Tags

free algebra, non-unital, non-associative, free magma, magma algebra, universal property,
forgetful functor, adjoint functor
-/


universe u v w

noncomputable section

variable (R : Type u) (X : Type v) [Semiring R]

/-- The free non-unital, non-associative algebra on the type `X` with coefficients in `R`. -/
/-- The free non-unital, non-associative algebra on the type `X` with coefficients in `R`. -/
abbrev FreeNonUnitalNonAssocAlgebra := by sorry


namespace FreeNonUnitalNonAssocAlgebra

variable {X}

/-- The embedding of `X` into the free algebra with coefficients in `R`. -/
/-- Embeds an element of `α` into `FreeMonoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `FreeAddMonoid α` as a singleton list."]
def of (x : α) : FreeMonoid α := by sorry


variable {A : Type w} [NonUnitalNonAssocSemiring A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- The functor `X ↦ FreeNonUnitalNonAssocAlgebra R X` from the category of types to the
category of non-unital, non-associative algebras over `R` is adjoint to the forgetful functor in the
other direction. -/
/-- Equivalence between maps `α → M` and monoid homomorphisms `FreeMonoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`FreeAddMonoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M) where
  toFun f :=
  { toFun := fun l ↦ prodAux ((toList l).map f)
    map_one' := rfl
    map_mul' := fun _ _ ↦ by sorry


@[simp]
theorem lift_symm_apply (F : FreeNonUnitalNonAssocAlgebra R X →ₙₐ[R] A) :
    (lift R).symm F = F ∘ of R := rfl

@[target] theorem of_comp_lift (f : X → A) : lift R f ∘ of R = f := by sorry


/-- Decomposition of a `k`-algebra homomorphism from `MonoidAlgebra k G` by
its values on `F (single a 1)`. -/
@[target] theorem lift_unique (F : MonoidAlgebra k G →ₐ[k] A) (f : MonoidAlgebra k G) :
    F f = f.sum fun a b => b • F (single a 1) := by
  sorry


@[simp]
theorem lift_of_apply (f : X → A) (x) : lift R f (of R x) = f x :=
  congr_fun (of_comp_lift _ f) x

@[target] theorem lift_comp_of (f : α → M) : lift f ∘ of = f := by sorry


@[target] lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := by sorry


end FreeNonUnitalNonAssocAlgebra
