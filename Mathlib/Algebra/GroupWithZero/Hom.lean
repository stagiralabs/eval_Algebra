import VerifiedAgora.tagger
/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.NeZero

/-!
# Monoid with zero and group with zero homomorphisms

This file defines homomorphisms of monoids with zero.

We also define coercion to a function, and usual operations: composition, identity homomorphism,
pointwise multiplication and pointwise inversion.


## Notations

* `→*₀`: `MonoidWithZeroHom`, the type of bundled `MonoidWithZero` homs. Also use for
  `GroupWithZero` homs.

## Implementation notes

Implicit `{}` brackets are often used instead of type class `[]` brackets.  This is done when the
instances can be inferred because they are implicit arguments to the type `MonoidHom`.  When they
can be inferred from the type it is faster to use this method than to use type class inference.

## Tags

monoid homomorphism
-/

assert_not_exists DenselyOrdered

open Function

namespace NeZero
variable {F α β : Type*} [Zero α] [Zero β] [FunLike F α β] [ZeroHomClass F α β] {a : α}

@[target] lemma of_map (f : F) [neZero : NeZero (f a)] : NeZero a :=
  ⟨fun h ↦ ne (f a) <| by sorry


@[target] theorem of_injective : Function.Injective (@of α) := by sorry


end NeZero

variable {F α β γ δ M₀ : Type*} [MulZeroOneClass α] [MulZeroOneClass β] [MulZeroOneClass γ]
  [MulZeroOneClass δ]

/-- `MonoidWithZeroHomClass F α β` states that `F` is a type of
`MonoidWithZero`-preserving homomorphisms.

You should also extend this typeclass when you extend `MonoidWithZeroHom`. -/
class MonoidWithZeroHomClass (F : Type*) (α β : outParam Type*) [MulZeroOneClass α]
  [MulZeroOneClass β] [FunLike F α β] extends MonoidHomClass F α β, ZeroHomClass F α β : Prop

/-- `α →*₀ β` is the type of functions `α → β` that preserve
the `MonoidWithZero` structure.

`MonoidWithZeroHom` is also used for group homomorphisms.

When possible, instead of parametrizing results over `(f : α →*₀ β)`,
you should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `MonoidWithZeroHomClass`. -/
structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]
  extends ZeroHom α β, MonoidHom α β

/-- `α →*₀ β` denotes the type of zero-preserving monoid homomorphisms from `α` to `β`. -/
infixr:25 " →*₀ " => MonoidWithZeroHom

/-- Turn an element of a type `F` satisfying `MonoidWithZeroHomClass F α β` into an actual
`MonoidWithZeroHom`. This is declared as the default coercion from `F` to `α →*₀ β`. -/
@[coe]
def MonoidWithZeroHomClass.toMonoidWithZeroHom [FunLike F α β] [MonoidWithZeroHomClass F α β]
    (f : F) : α →*₀ β := { (f : α →* β), (f : ZeroHom α β) with }

/-- Any type satisfying `MonoidWithZeroHomClass` can be cast into `MonoidWithZeroHom` via
`MonoidWithZeroHomClass.toMonoidWithZeroHom`. -/
instance [FunLike F α β] [MonoidWithZeroHomClass F α β] : CoeTC F (α →*₀ β) :=
  ⟨MonoidWithZeroHomClass.toMonoidWithZeroHom⟩

namespace MonoidWithZeroHom

attribute [nolint docBlame] toMonoidHom
attribute [nolint docBlame] toZeroHom

instance funLike : FunLike (α →*₀ β) α β where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr

instance monoidWithZeroHomClass : MonoidWithZeroHomClass (α →*₀ β) α β where
  map_mul := MonoidWithZeroHom.map_mul'
  map_one := MonoidWithZeroHom.map_one'
  map_zero f := f.map_zero'

instance [Subsingleton α] : Subsingleton (α →*₀ β) := .of_oneHomClass

variable [FunLike F α β]

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f := by sorry

section Coes

/-! Bundled morphisms can be down-cast to weaker bundlings -/

attribute [coe] toMonoidHom

/-- `MonoidWithZeroHom` down-cast to a `MonoidHom`, forgetting the 0-preserving property. -/
instance coeToMonoidHom : Coe (α →*₀ β) (α →* β) :=
  ⟨toMonoidHom⟩

attribute [coe] toZeroHom

/-- `MonoidWithZeroHom` down-cast to a `ZeroHom`, forgetting the monoidal property. -/
instance coeToZeroHom :
  Coe (α →*₀ β) (ZeroHom α β) := ⟨toZeroHom⟩

-- This must come after the coe_toFun definitions
initialize_simps_projections MonoidWithZeroHom (toFun → apply)

@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


@[target] lemma toZeroHom_coe (f : α →*₀ β) : (f.toZeroHom : α → β) = f := by sorry


@[target] lemma toMonoidHom_coe (f : α →*₀ β) : f.toMonoidHom.toFun = f := by sorry


@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry


end Coes

/-- Copy of a `MonoidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →*₀ β) (f' : α → β) (h : f' = f) : α →* β :=
  { f.toZeroHom.copy f' h, f.toMonoidHom.copy f' h with }

@[target] theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' := by sorry


@[target] theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f := by sorry


protected lemma map_one (f : α →*₀ β) : f 1 = 1 := f.map_one'

protected lemma map_zero (f : α →*₀ β) : f 0 = 0 := f.map_zero'

protected lemma map_mul (f : α →*₀ β) (a b : α) : f (a * b) = f a * f b := f.map_mul' a b

/-- The identity map from a `MonoidWithZero` to itself. -/
/-- The identity map inducing an `Algebra` structure. -/
instance (priority := by sorry


/-- Composition of `MonoidWithZeroHom`s as a `MonoidWithZeroHom`. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


@[target] theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := by sorry


@[target] theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := by sorry


@[target] theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := by sorry


@[target] theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := by sorry


lemma cancel_left {g : β →*₀ γ} {f₁ f₂ : α →*₀ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun x ↦ hg <| by rw [← comp_apply, h,
    comp_apply], fun h ↦ h ▸ rfl⟩

@[target] lemma toMonoidHom_injective : Injective (toMonoidHom : (α →*₀ β) → α →* β) := by sorry


@[target] lemma toZeroHom_injective : Injective (toZeroHom : (α →*₀ β) → ZeroHom α β) := by sorry


@[target] theorem comp_id : φ.comp (AlgHom.id R A) = φ := by sorry


@[target] theorem id_comp : (AlgHom.id R B).comp φ = φ := by sorry

instance : Inhabited (α →*₀ α) := ⟨id α⟩

/-- Given two monoid with zero morphisms `f`, `g` to a commutative monoid with zero, `f * g` is the
monoid with zero morphism sending `x` to `f x * g x`. -/
instance {β} [CommMonoidWithZero β] : Mul (α →*₀ β) where
  mul f g :=
    { (f * g : α →* β) with
      map_zero' := by dsimp; rw [map_zero, zero_mul] }

end MonoidWithZeroHom

section CommMonoidWithZero
variable [CommMonoidWithZero M₀] {n : ℕ} (hn : n ≠ 0)

/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
/-- We define `x ↦ x^n` (for positive `n : ℕ`) as a `MonoidWithZeroHom` -/
def powMonoidWithZeroHom : M₀ →*₀ M₀ := by sorry


@[target] lemma coe_powMonoidWithZeroHom : (powMonoidWithZeroHom hn : M₀ → M₀) = fun x ↦ x ^ n := by sorry


@[target] lemma powMonoidWithZeroHom_apply (a : M₀) : powMonoidWithZeroHom hn a = a ^ n := by sorry


end CommMonoidWithZero

/-! ### Equivalences -/

namespace MulEquivClass
variable {F α β : Type*} [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) toZeroHomClass [MulZeroClass α] [MulZeroClass β] [MulEquivClass F α β] :
    ZeroHomClass F α β where
  map_zero f :=
    calc
      f 0 = f 0 * f (EquivLike.inv f 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass
    [MulZeroOneClass α] [MulZeroOneClass β] [MulEquivClass F α β] :
    MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass F, MulEquivClass.toZeroHomClass with }

end MulEquivClass
