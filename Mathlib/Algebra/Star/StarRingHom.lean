import VerifiedAgora.tagger
/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic

/-!
# Morphisms of star rings

This file defines a new type of morphism between (non-unital) rings `A` and `B` where both
`A` and `B` are equipped with a `star` operation. This morphism, namely `NonUnitalStarRingHom`, is
a direct extension of its non-`star`red counterpart with a field `map_star` which guarantees it
preserves the star operation.

As with `NonUnitalRingHom`, the multiplications are not assumed to be associative or unital.

## Main definitions

  * `NonUnitalStarRingHom`

## Implementation

This file is heavily inspired by `Mathlib.Algebra.Star.StarAlgHom`.

## Tags

non-unital, ring, morphism, star
-/

open EquivLike

/-! ### Non-unital star ring homomorphisms -/

/-- A *non-unital ⋆-ring homomorphism* is a non-unital ring homomorphism between non-unital
non-associative semirings `A` and `B` equipped with a `star` operation, and this homomorphism is
also `star`-preserving. -/
structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A →ₙ+* B where
  /-- By definition, a non-unital ⋆-ring homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

/-- `α →⋆ₙ+* β` denotes the type of non-unital ring homomorphisms from `α` to `β`. -/
infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom

/-- Reinterpret a non-unital star ring homomorphism as a non-unital ring homomorphism
by forgetting the interaction with the star operation.

Users should not make use of this, but instead utilize the coercion obtained through
the `NonUnitalRingHomClass` instance. -/
add_decl_doc NonUnitalStarRingHom.toNonUnitalRingHom

/-- `NonUnitalStarRingHomClass F A B` states that `F` is a type of non-unital ⋆-ring homomorphisms.
You should also extend this typeclass when you extend `NonUnitalStarRingHom`. -/
class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] extends StarHomClass F A B : Prop

namespace NonUnitalStarRingHomClass

variable {F A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B]

/-- Turn an element of a type `F` satisfying `NonUnitalStarRingHomClass F A B` into an actual
`NonUnitalStarRingHom`. This is declared as the default coercion from `F` to `A →⋆ₙ+ B`. -/
/-- Turn an element of a type `F` satisfying `NonUnitalStarRingHomClass F A B` into an actual
`NonUnitalStarRingHom`. This is declared as the default coercion from `F` to `A →⋆ₙ+ B`. -/
@[coe]
def toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A →⋆ₙ+* B := by sorry


instance [NonUnitalStarRingHomClass F A B] : CoeHead F (A →⋆ₙ+* B) :=
  ⟨toNonUnitalStarRingHom⟩

end NonUnitalStarRingHomClass

namespace NonUnitalStarRingHom

section Basic

variable {A B C D : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [NonUnitalNonAssocSemiring C] [Star C]
variable [NonUnitalNonAssocSemiring D] [Star D]

instance : FunLike (A →⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩,  _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

instance : NonUnitalRingHomClass (A →⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

instance : NonUnitalStarRingHomClass (A →⋆ₙ+* B) A B where
  map_star f := f.map_star'

/-- See Note [custom simps projection] -/
def Simps.apply (f : A →⋆ₙ+* B) : A → B := f

initialize_simps_projections NonUnitalStarRingHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [NonUnitalRingHomClass F A B]
    [NonUnitalStarRingHomClass F A B] (f : F) : ⇑(f : A →⋆ₙ+* B) = f :=
  rfl

@[target] theorem coe_toNonUnitalRingHom (f : R ≃+* S) : ⇑(f : R →ₙ+* S) = f := by sorry


@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


/-- Copy of a `NonUnitalStarRingHom` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : A →⋆ₙ+* B where
  toFun := f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

@[target] theorem coe_copy (f : CentroidHom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' := by sorry


@[target] theorem copy_eq (f : CentroidHom α) (f' : α → α) (h : f' = f) : f.copy f' h = f := by sorry


@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry


section

variable (A)

/-- The identity as a non-unital ⋆-ring homomorphism. -/
protected def id : A →⋆ₙ+* A :=
  { (1 : A →ₙ+* A) with map_star' := fun _ => rfl }

@[target] theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id := by sorry


end

/-- The composition of non-unital ⋆-ring homomorphisms, as a non-unital ⋆-ring homomorphism. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


@[target] theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := by sorry


@[simp]
theorem comp_apply (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) (a : A) : comp f g a = f (g a) :=
  rfl

@[target] theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := by sorry


@[target] theorem id_comp : (AlgHom.id R B).comp φ = φ := by sorry


@[target] theorem comp_id : φ.comp (AlgHom.id R A) = φ := by sorry


instance : Monoid (A →⋆ₙ+* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry


@[target] theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a := by sorry


end Basic

section Zero

-- the `zero` requires extra type class assumptions because we need `star_zero`
variable {A B C : Type*}
variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

instance : Zero (A →⋆ₙ+* B) :=
  ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩

instance : Inhabited (A →⋆ₙ+* B) :=
  ⟨0⟩

instance : MonoidWithZero (A →⋆ₙ+* A) where
  zero_mul := fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

@[simp]
theorem coe_zero : ((0 : A →⋆ₙ+* B) : A → B) = 0 :=
  rfl

@[target] theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 := by sorry


end Zero


end NonUnitalStarRingHom

/-! ### Star ring equivalences -/

/-- A *⋆-ring* equivalence is an equivalence preserving addition, multiplication, and the star
operation, which allows for considering both unital and non-unital equivalences with a single
structure. -/
structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B

/-- Reinterpret a star ring equivalence as a `RingEquiv` by forgetting the interaction with the star
operation. -/
add_decl_doc StarRingEquiv.toRingEquiv

/-- `StarRingEquivClass F A B` asserts `F` is a type of bundled ⋆-ring equivalences between `A` and
`B`.
You should also extend this typeclass when you extend `StarRingEquiv`. -/
class StarRingEquivClass (F : Type*) (A B : outParam Type*)
    [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B]
    extends RingEquivClass F A B : Prop where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)

namespace StarRingEquivClass

-- See note [lower instance priority]
instance (priority := 50) {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [hF : StarRingEquivClass F A B] :
    StarHomClass F A B :=
  { hF with }

-- See note [lower instance priority]
instance (priority := 100) {F A B : Type*} [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [EquivLike F A B] [RingEquivClass F A B]
    [StarRingEquivClass F A B] : NonUnitalStarRingHomClass F A B :=
  { }

/-- Turn an element of a type `F` satisfying `StarRingEquivClass F A B` into an actual
`StarRingEquiv`. This is declared as the default coercion from `F` to `A ≃⋆+* B`. -/
@[coe]
def toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [RingEquivClass F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B :=
  { (f : A ≃+* B) with
    map_star' := map_star f}

/-- Any type satisfying `StarRingEquivClass` can be cast into `StarRingEquiv` via
`StarRingEquivClass.toStarRingEquiv`. -/
instance instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [RingEquivClass F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B) :=
  ⟨toStarRingEquiv⟩

end StarRingEquivClass

namespace StarRingEquiv

section Basic

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

instance : EquivLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

instance : RingEquivClass (A ≃⋆+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

instance : StarRingEquivClass (A ≃⋆+* B) A B where
  map_star := map_star'

/-- Helper instance for cases where the inference via `EquivLike` is too hard. -/
instance : FunLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective

@[target] theorem toRingEquiv_eq_coe (e : A ≃⋆ₐ[R] B) : e.toRingEquiv = e := by sorry


@[ext]
theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- The identity map as a star ring isomorphism. -/
@[target] lemma refl (A : CSA K) : IsBrauerEquivalent A A := by sorry


instance : Inhabited (A ≃⋆+* A) :=
  ⟨refl⟩

@[target] theorem coe_refl (R : Type*) [Mul R] [Add R] : ⇑(RingEquiv.refl R) = id := by sorry


/-- The inverse of a star ring isomorphism is a star ring isomorphism. -/
@[symm]
nonrec def symm (e : A ≃⋆+* B) : B ≃⋆+* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_star e (inv e b)).symm }

/-- See Note [custom simps projection] -/
def Simps.apply (e : A ≃⋆+* B) : A → B := e

/-- See Note [custom simps projection] -/
def Simps.symm_apply (e : A ≃⋆+* B) : B → A :=
  e.symm

initialize_simps_projections StarRingEquiv (toFun → apply, invFun → symm_apply)

@[target] theorem invFun_eq_symm (f : R ≃+* S) : EquivLike.inv f = f.symm := by sorry


@[target] theorem symm_symm (e : R ≃+* S) : e.symm.symm = e := by sorry


theorem symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) → B ≃⋆+* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

theorem coe_mk (e h₁) : ⇑(⟨e, h₁⟩ : A ≃⋆+* B) = e := rfl

@[simp]
theorem mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B) = e := ext fun _ => rfl

/-- Auxiliary definition to avoid looping in `dsimp` with `StarRingEquiv.symm_mk`. -/
@[target] theorem symm_mk (f : R → S) (g h₁ h₂ h₃ h₄) :
    (mk ⟨f, g, h₁, h₂⟩ h₃ h₄).symm =
      { symm_mk.aux f g h₁ h₂ h₃ h₄ with
        toFun := by sorry


@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl

@[target] theorem refl_symm : (StarAlgEquiv.refl : A ≃⋆ₐ[R] A).symm = StarAlgEquiv.refl := by sorry


/-- Transitivity of `StarRingEquiv`. -/
open Matrix in
@[target] lemma trans {A B C : CSA K} (hAB : IsBrauerEquivalent A B) (hBC : IsBrauerEquivalent B C) :
    IsBrauerEquivalent A C := by
  sorry


@[target] theorem apply_symm_apply (e : R ≃+* S) : ∀ x, e (e.symm x) = x := by sorry


@[target] theorem symm_apply_apply (e : R ≃+* S) : ∀ x, e.symm (e x) = x := by sorry


@[simp]
theorem symm_trans_apply (e₁ : A ≃⋆+* B) (e₂ : B≃⋆+* C) (x : C) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[target] theorem coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.trans e₂ : R → S') = e₂ ∘ e₁ := by sorry


@[target] theorem trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* S') (a : R) : e₁.trans e₂ a = e₂ (e₁ a) := by sorry


@[target] theorem leftInverse_symm (e : A ≃⋆ₐ[R] B) : Function.LeftInverse e.symm e := by sorry


@[target] theorem rightInverse_symm (e : A ≃⋆ₐ[R] B) : Function.RightInverse e.symm e := by sorry


end Basic


section Bijective

variable {F G A B : Type*}
variable [NonUnitalNonAssocSemiring A] [Star A]
variable [NonUnitalNonAssocSemiring B] [Star B]
variable [FunLike F A B] [NonUnitalRingHomClass F A B] [NonUnitalStarRingHomClass F A B]
variable [FunLike G B A]

/-- If a (unital or non-unital) star ring morphism has an inverse, it is an isomorphism of
star rings. -/
/-- If a (unital or non-unital) star ring morphism has an inverse, it is an isomorphism of
star rings. -/
@[simps]
def ofStarRingHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆+* B where
  toFun := by sorry


/-- Promote a bijective star ring homomorphism to a star ring equivalence. -/
noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B :=
  { RingEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }

@[target] theorem coe_ofBijective [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f) :
    (ofBijective f hf : R → S) = f := by sorry


@[target] theorem ofBijective_apply [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Bijective f)
    (x : R) : ofBijective f hf x = f x := by sorry


end Bijective

end StarRingEquiv
