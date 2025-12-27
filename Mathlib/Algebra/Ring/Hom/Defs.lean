import VerifiedAgora.tagger
/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `RingHom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

## Main definitions

* `NonUnitalRingHom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `RingHom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notations

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `SemiringHom` -- the idea is that `RingHom` is used.
  The constructor for a `RingHom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `RingHom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`RingHom`, `SemiringHom`
-/

assert_not_exists Function.Injective.mulZeroClass semigroupDvd Units.map Set.range

open Function

variable {F α β γ : Type*}

/-- Bundled non-unital semiring homomorphisms `α →ₙ+* β`; use this for bundled non-unital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : α →ₙ+* β)`,
you should parametrize over `(F : Type*) [NonUnitalRingHomClass F α β] (f : F)`.

When you extend this structure, make sure to extend `NonUnitalRingHomClass`. -/
structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β

/-- `α →ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →ₙ+* " => NonUnitalRingHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as a semigroup
homomorphism `α →ₙ* β`. The `simp`-normal form is `(f : α →ₙ* β)`. -/
add_decl_doc NonUnitalRingHom.toMulHom

/-- Reinterpret a non-unital ring homomorphism `f : α →ₙ+* β` as an additive
monoid homomorphism `α →+ β`. The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

/-- `NonUnitalRingHomClass F α β` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `NonUnitalRingHom`. -/
class NonUnitalRingHomClass (F : Type*) (α β : outParam Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] [FunLike F α β]
  extends MulHomClass F α β, AddMonoidHomClass F α β : Prop

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [FunLike F α β]
variable [NonUnitalRingHomClass F α β]

/-- Turn an element of a type `F` satisfying `NonUnitalRingHomClass F α β` into an actual
`NonUnitalRingHom`. This is declared as the default coercion from `F` to `α →ₙ+* β`. -/
@[coe]
def NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α →ₙ+* β :=
  { (f : α →ₙ* β), (f : α →+ β) with }

/-- Any type satisfying `NonUnitalRingHomClass` can be cast into `NonUnitalRingHom` via
`NonUnitalRingHomClass.toNonUnitalRingHom`. -/
instance : CoeTC F (α →ₙ+* β) :=
  ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

instance : FunLike (α →ₙ+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

initialize_simps_projections NonUnitalRingHom (toFun → apply)

@[simp]
theorem coe_toMulHom (f : α →ₙ+* β) : ⇑f.toMulHom = f :=
  rfl

@[target] theorem coe_mulHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  sorry


@[target] theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := by sorry


@[simp]
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨⟨f, h₂⟩, h₃⟩ :=
  rfl

/-- Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-- Copy of a `CentroidHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : CentroidHom α :=
  { f.toAddMonoidHom.copy f' <| h with
    toFun := f'
    map_mul_left' := fun a b ↦ by sorry


@[simp]
theorem coe_copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[target] theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f := by sorry


end coe

section

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry


@[target] theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) := by sorry


theorem coe_mulHom_injective : Injective fun f : α →ₙ+* β => (f : α →ₙ* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
/-- The identity map inducing an `Algebra` structure. -/
instance (priority := by sorry


instance : Zero (α →ₙ+* β) :=
  ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩

instance : Inhabited (α →ₙ+* β) :=
  ⟨0⟩

@[target] theorem coe_zero : (↑(0 : R) : A) = 0 := by sorry


@[target] theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 := by sorry


@[target] theorem id_apply (p : A) : AlgHom.id R A p = p := by sorry


@[simp]
theorem coe_addMonoidHom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_mulHom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α :=
  rfl

variable [NonUnitalNonAssocSemiring γ]

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


/-- Composition of non-unital ring homomorphisms is associative. -/
@[target] theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := by sorry


@[target] theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := by sorry


@[target] theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := by sorry


@[target] theorem coe_comp_addMonoidHom (g f : CentroidHom α) : (g.comp f : α →+ α) = (g : α →+ α).comp f := by sorry


@[simp]
theorem coe_comp_mulHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    MulHom.mk (g ∘ f) (g.comp f).map_mul' = (g : β →ₙ* γ).comp f :=
  rfl

@[simp]
theorem comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  rfl

@[target] theorem comp_id : φ.comp (AlgHom.id R A) = φ := by sorry


@[target] theorem id_comp : (AlgHom.id R B).comp φ = φ := by sorry


instance : MonoidWithZero (α →ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  zero := 0
  mul_zero := comp_zero
  zero_mul := zero_comp

@[target] theorem one_def : (1 : MonoidAlgebra k G) = single 1 1 := by sorry


@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry


@[target] theorem mul_def {f g : MonoidAlgebra k G} :
    f * g = f.sum fun a₁ b₁ => g.sum fun a₂ b₂ => single (a₁ * a₂) (b₁ * b₂) := by
  sorry


@[target] theorem coe_mul (a b : R) : (↑(a * b : R) : A) = ↑a * ↑b := by sorry


@[target] theorem cancel_right {g₁ g₂ f : CentroidHom α} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ := by sorry


@[target] theorem cancel_left {g f₁ f₂ : CentroidHom α} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h ↦ ext fun a ↦ hg <| by sorry


end NonUnitalRingHom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a
sensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`. -/
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β

/-- `α →+* β` denotes the type of ring homomorphisms from `α` to `β`. -/
infixr:25 " →+* " => RingHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid with zero homomorphism `α →*₀ β`.
The `simp`-normal form is `(f : α →*₀ β)`. -/
add_decl_doc RingHom.toMonoidWithZeroHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a monoid homomorphism `α →* β`.
The `simp`-normal form is `(f : α →* β)`. -/
add_decl_doc RingHom.toMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as an additive monoid homomorphism `α →+ β`.
The `simp`-normal form is `(f : α →+ β)`. -/
add_decl_doc RingHom.toAddMonoidHom

/-- Reinterpret a ring homomorphism `f : α →+* β` as a non-unital ring homomorphism `α →ₙ+* β`. The
`simp`-normal form is `(f : α →ₙ+* β)`. -/
add_decl_doc RingHom.toNonUnitalRingHom

section RingHomClass

/-- `RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `RingHom`.

This extends from both `MonoidHomClass` and `MonoidWithZeroHomClass` in
order to put the fields in a sensible order, even though
`MonoidWithZeroHomClass` already extends `MonoidHomClass`. -/
class RingHomClass (F : Type*) (α β : outParam Type*)
    [NonAssocSemiring α] [NonAssocSemiring β] [FunLike F α β]
  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β : Prop

variable [FunLike F α β]

-- See note [implicit instance arguments].
variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} [RingHomClass F α β]

/-- Turn an element of a type `F` satisfying `RingHomClass F α β` into an actual
`RingHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
@[coe]
def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

/-- Any type satisfying `RingHomClass` can be cast into `RingHom` via `RingHomClass.toRingHom`. -/
instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩

instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }

end RingHomClass

namespace RingHom

section coe

/-!
Throughout this section, some `Semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

instance instFunLike : FunLike (α →+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance instRingHomClass : RingHomClass (α →+* β) α β where
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections RingHom (toFun → apply)

@[target] theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f := by sorry


@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f := by sorry


attribute [coe] RingHom.toMonoidHom

instance coeToMonoidHom : Coe (α →+* β) (α →* β) :=
  ⟨RingHom.toMonoidHom⟩

@[simp]
theorem toMonoidHom_eq_coe (f : α →+* β) : f.toMonoidHom = f :=
  rfl

theorem toMonoidWithZeroHom_eq_coe (f : α →+* β) : (f.toMonoidWithZeroHom : α → β) = f := by
  rfl

@[simp]
theorem coe_monoidHom_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α →* β) = f :=
  rfl

@[target] theorem toAddMonoidHom_eq_coe (f : CentroidHom α) : f.toAddMonoidHom = f := by sorry


@[simp]
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨⟨f, h₃⟩, h₄⟩ :=
  rfl

/-- Copy of a `RingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
theorem coe_copy (f : α →+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : α →+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

protected theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

protected theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[target] theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b := by sorry


@[ext]
theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
theorem mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f :=
  ext fun _ => rfl

theorem coe_addMonoidHom_injective : Injective (fun f : α →+* β => (f : α →+ β)) := fun _ _ h =>
  ext <| DFunLike.congr_fun (F := α →+ β) h

@[target] theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →* B) := by sorry


/-- Ring homomorphisms map zero to zero. -/
protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
  map_zero f

/-- Ring homomorphisms map one to one. -/
protected theorem map_one (f : α →+* β) : f 1 = 1 :=
  map_one f

/-- Ring homomorphisms preserve addition. -/
protected theorem map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b :=
  map_add f

/-- Ring homomorphisms preserve multiplication. -/
protected theorem map_mul (f : α →+* β) : ∀ a b, f (a * b) = f a * f b :=
  map_mul f

@[simp]
theorem map_ite_zero_one {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp [h]

@[simp]
theorem map_ite_one_zero {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 1 0) = ite p 1 0 := by
  split_ifs with h <;> simp [h]

/-- `f : α →+* β` has a trivial codomain iff `f 1 = 0`. -/
theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by rw [map_one, eq_comm]

/-- `f : α →+* β` has a trivial codomain iff it has a trivial range. -/
theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩

/-- `f : α →+* β` doesn't map `1` to `0` if `β` is nontrivial -/
theorem map_one_ne_zero [Nontrivial β] : f 1 ≠ 0 :=
  mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

include f in
/-- If there is a homomorphism `f : α →+* β` and `β` is nontrivial, then `α` is nontrivial. -/
/-- Pullback a `Nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
@[target] theorem domain_nontrivial [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1, mt (congr_arg f) <| by
    sorry


theorem codomain_trivial (f : α →+* β) [h : Subsingleton α] : Subsingleton β :=
  (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial

end

/-- Ring homomorphisms preserve additive inverse. -/
protected theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x :=
  map_neg f x

/-- Ring homomorphisms preserve subtraction. -/
protected theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) :
    f (x - y) = f x - f y :=
  map_sub f x y

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `Subbimodule.baseChange`. -/
@[simps]
def mk (p : AddSubmonoid M) (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
    (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : Submodule (A ⊗[R] B) M :=
  { p with
    carrier := p
    smul_mem' := fun ab m =>
      TensorProduct.induction_on ab (fun _ => by sorry


variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type*) [NonAssocSemiring α] : α →+* α where
  toFun := _root_.id
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance : Inhabited (α →+* α) :=
  ⟨id α⟩

@[simp, norm_cast]
theorem coe_id : ⇑(RingHom.id α) = _root_.id := rfl

@[simp]
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl

@[simp]
theorem coe_addMonoidHom_id : (id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_monoidHom_id : (id α : α →* α) = MonoidHom.id α :=
  rfl

variable {_ : NonAssocSemiring γ}

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun := g ∘ f, map_one' := by simp }

/-- Composition of semiring homomorphisms is associative. -/
theorem comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn :=
  rfl

theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) :
    (hnp.comp hmn : α → γ) x = hnp (hmn x) :=
  rfl

@[simp]
theorem comp_id (f : α →+* β) : f.comp (id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : α →+* β) : (id β).comp f = f :=
  ext fun _ => rfl

instance instOne : One (α →+* α) where one := id _
instance instMul : Mul (α →+* α) where mul := comp

lemma one_def : (1 : α →+* α) = id α := rfl

lemma mul_def (f g : α →+* α) : f * g = f.comp g := rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : α →+* α) = _root_.id := rfl

@[simp, norm_cast] lemma coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g := rfl

instance instMonoid : Monoid (α →+* α) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *]
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _

@[target] theorem coe_pow (a : R) (n : ℕ) : (↑(a ^ n : R) : A) = (a : A) ^ n := by sorry


@[simp]
theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => RingHom.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end RingHom

section Semiring
variable [Semiring α] [Semiring β]

protected lemma RingHom.map_pow (f : α →+* β) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n := map_pow f a

end Semiring

namespace AddMonoidHom

variable [CommRing α] [IsDomain α] [CommRing β] (f : β →+ α)

/-- Make a ring homomorphism from an additive group homomorphism from a commutative ring to an
integral domain that commutes with self multiplication, assumes that two is nonzero and `1` is sent
to `1`. -/
def mkRingHomOfMulSelfOfTwoNeZero (h : ∀ x, f (x * x) = f x * f x) (h_two : (2 : α) ≠ 0)
    (h_one : f 1 = 1) : β →+* α :=
  { f with
    map_one' := h_one,
    map_mul' := fun x y => by
      have hxy := h (x + y)
      rw [mul_add, add_mul, add_mul, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mul,
        mul_add, mul_add, ← sub_eq_zero, add_comm (f x * f x + f (y * x)), ← sub_sub, ← sub_sub,
        ← sub_sub, mul_comm y x, mul_comm (f y) (f x)] at hxy
      simp only [add_assoc, add_sub_assoc, add_sub_cancel] at hxy
      rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero (M₀ := α),
        sub_eq_zero, or_iff_not_imp_left] at hxy
      exact hxy h_two }

@[simp]
theorem coe_fn_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β → α) = f :=
  rfl

@[simp]
theorem coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero (h h_two h_one) :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β →+ α) = f := by
  ext
  rfl

end AddMonoidHom
