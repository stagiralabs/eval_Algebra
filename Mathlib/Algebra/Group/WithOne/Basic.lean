import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.WithOne.Defs

/-!
# More operations on `WithOne` and `WithZero`

This file defines various bundled morphisms on `WithOne` and `WithZero`
that were not available in `Algebra/Group/WithOne/Defs`.

## Main definitions

* `WithOne.lift`, `WithZero.lift`
* `WithOne.map`, `WithZero.map`
-/

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

@[to_additive]
instance involutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) :=
  { WithOne.inv with
    inv_inv := fun a =>
      (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id] }

section

/-- `WithOne.coe` as a bundled morphism -/
@[to_additive (attr := simps apply) "`WithZero.coe` as a bundled morphism"]
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' _ _ := rfl

end

section lift

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homomorphism. -/
/-- Equivalence between maps `α → M` and monoid homomorphisms `FreeMonoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`FreeAddMonoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M) where
  toFun f :=
  { toFun := fun l ↦ prodAux ((toList l).map f)
    map_one' := rfl
    map_mul' := fun _ _ ↦ by sorry


variable (f : α →ₙ* β)

@[target] theorem Periodic.lift_coe [AddGroup α] (h : Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a := by sorry


@[target] theorem lift_one : q.lift (1 : ℍ[R,c₁,c₂,c₃]) = 1 := by sorry


/-- Decomposition of a `k`-algebra homomorphism from `MonoidAlgebra k G` by
its values on `F (single a 1)`. -/
@[target] theorem lift_unique (F : MonoidAlgebra k G →ₐ[k] A) (f : MonoidAlgebra k G) :
    F f = f.sum fun a b => b • F (single a 1) := by
  sorry


end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `WithOne α` to `WithOne β` -/
@[to_additive "Given an additive map from `α → β` returns an add monoid homomorphism from
`WithZero α` to `WithZero β`"]
def map (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)

@[to_additive (attr := simp)]
theorem map_coe (f : α →ₙ* β) (a : α) : map f (a : WithOne α) = f a :=
  rfl

@[target] theorem map_map {α₁ : Type*} {g : α₁ → α} {x : FreeMonoid α₁} :
    map f (map g x) = map (f ∘ g) x := by
  sorry


@[target] theorem map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) := by sorry


/-- A version of `Equiv.optionCongr` for `WithOne`. -/
@[to_additive (attr := simps apply) "A version of `Equiv.optionCongr` for `WithZero`."]
def _root_.MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { map e.toMulHom with
    toFun := map e.toMulHom, invFun := map e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective map_id

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_symm (e : α ≃* β) :
    e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl

@[to_additive (attr := simp)]
theorem _root_.MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (map_comp _ _).symm

end Map

end WithOne
