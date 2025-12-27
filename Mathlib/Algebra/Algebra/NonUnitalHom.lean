import VerifiedAgora.tagger
/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.GroupWithZero.Action.Prod

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
 * an addition,
 * an additive zero,
 * a multiplication,
 * a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `Mul` instead of `Group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `NonUnitalAlgHom`.

TODO: add `NonUnitalAlgEquiv` when needed.

## Main definitions

  * `NonUnitalAlgHom`
  * `AlgHom.toNonUnitalAlgHom`

## Tags

non-unital, algebra, morphism
-/

universe u u₁ v w w₁ w₂ w₃

variable {R : Type u} {S : Type u₁}

/-- A morphism respecting addition, multiplication, and scalar multiplication
(denoted as `A →ₛₙₐ[φ] B`, or `A →ₙₐ[R] B` when `φ` is the identity on `R`).
When these arise from algebra structures, this is the same
as a not-necessarily-unital morphism of algebras. -/
structure NonUnitalAlgHom [Monoid R] [Monoid S] (φ : R →* S) (A : Type v) (B : Type w)
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] extends A →ₑ+[φ] B, A →ₙ* B

@[inherit_doc NonUnitalAlgHom]
infixr:25 " →ₙₐ " => NonUnitalAlgHom _

@[inherit_doc]
notation:25 A " →ₛₙₐ[" φ "] " B => NonUnitalAlgHom φ A B

@[inherit_doc]
notation:25 A " →ₙₐ[" R "] " B => NonUnitalAlgHom (MonoidHom.id R) A B

attribute [nolint docBlame] NonUnitalAlgHom.toMulHom

/-- `NonUnitalAlgSemiHomClass F φ A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B` which are equivariant with respect to `φ`. -/
class NonUnitalAlgSemiHomClass (F : Type*) {R S : outParam Type*} [Monoid R] [Monoid S]
    (φ : outParam (R →* S)) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction S B] [FunLike F A B]
    extends DistribMulActionSemiHomClass F φ A B, MulHomClass F A B : Prop

/-- `NonUnitalAlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B` which are `R`-linear.

  This is an abbreviation to `NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B` -/
abbrev NonUnitalAlgHomClass (F : Type*) (R A B : outParam Type*)
    [Monoid R] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [DistribMulAction R A] [DistribMulAction R B] [FunLike F A B] :=
  NonUnitalAlgSemiHomClass F (MonoidHom.id R) A B

namespace NonUnitalAlgHomClass

-- See note [lower instance priority]
instance (priority := 100) toNonUnitalRingHomClass
  {F R S A B : Type*} {_ : Monoid R} {_ : Monoid S} {φ : outParam (R →* S)}
    {_ : NonUnitalNonAssocSemiring A} [DistribMulAction R A]
    {_ : NonUnitalNonAssocSemiring B} [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] : NonUnitalRingHomClass F A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with }

variable [Semiring R] [Semiring S] {φ : R →+* S}
  {A B : Type*} [NonUnitalNonAssocSemiring A] [Module R A]
  [NonUnitalNonAssocSemiring B] [Module S B]

-- see Note [lower instance priority]
instance (priority := 100) {F R S A B : Type*}
    {_ : Semiring R} {_ : Semiring S} {φ : R →+* S}
    {_ : NonUnitalSemiring A} {_ : NonUnitalSemiring B} [Module R A] [Module S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass (R := R) (S := S) F φ A B] :
    SemilinearMapClass F φ A B :=
  { ‹NonUnitalAlgSemiHomClass F φ A B› with map_smulₛₗ := map_smulₛₗ }

instance (priority := 100) {F : Type*} [FunLike F A B] [Module R B] [NonUnitalAlgHomClass F R A B] :
    LinearMapClass F R A B :=
  { ‹NonUnitalAlgHomClass F R A B› with map_smulₛₗ := map_smulₛₗ }

/-- Turn an element of a type `F` satisfying `NonUnitalAlgSemiHomClass F φ A B` into an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[φ] B`. -/
/-- Turn an element of a type `F` satisfying `NonUnitalAlgSemiHomClass F φ A B` into an actual
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[φ] B`. -/
@[coe]
def toNonUnitalAlgSemiHom {F R S : Type*} [Monoid R] [Monoid S] {φ : R →* S} {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) : A →ₛₙₐ[φ] B := by sorry


instance {F R S A B : Type*} [Monoid R] [Monoid S] {φ : R →* S}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction S B] [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] :
      CoeTC F (A →ₛₙₐ[φ] B) :=
  ⟨toNonUnitalAlgSemiHom⟩

/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an actual
@[coe]
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[R] B`. -/
/-- Turn an element of a type `F` satisfying `NonUnitalAlgHomClass F R A B` into an actual
@[coe]
`NonUnitalAlgHom`. This is declared as the default coercion from `F` to `A →ₛₙₐ[R] B`. -/
def toNonUnitalAlgHom {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (f : F) : A →ₙₐ[R] B := by sorry


instance {F R : Type*} [Monoid R] {A B : Type*}
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
    [NonUnitalNonAssocSemiring B] [DistribMulAction R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] :
    CoeTC F (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

end NonUnitalAlgHomClass

namespace NonUnitalAlgHom

variable {T : Type*} [Monoid R] [Monoid S] [Monoid T] (φ : R →* S)
variable (A : Type v) (B : Type w) (C : Type w₁)
variable [NonUnitalNonAssocSemiring A] [DistribMulAction R A]
variable [NonUnitalNonAssocSemiring B] [DistribMulAction S B]
variable [NonUnitalNonAssocSemiring C] [DistribMulAction T C]

instance : DFunLike (A →ₛₙₐ[φ] B) A fun _ => B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

@[target] theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f := by sorry


/-- See Note [custom simps projection] -/
def Simps.apply (f : A →ₛₙₐ[φ] B) : A → B := f

initialize_simps_projections NonUnitalAlgHom
  (toDistribMulActionHom_toMulActionHom_toFun → apply, -toDistribMulActionHom)

variable {φ A B C}
@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B]
    [NonUnitalAlgSemiHomClass F φ A B] (f : F) :
    ⇑(f : A →ₛₙₐ[φ] B) = f :=
  rfl

@[target] theorem coe_injective : @Function.Injective (A →ₛₙₐ[φ] B) (A → B) (↑) := by
  sorry

instance : FunLike (A →ₛₙₐ[φ] B) A B where
  coe f := f.toFun
  coe_injective' := coe_injective

instance : NonUnitalAlgSemiHomClass (A →ₛₙₐ[φ] B) φ A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_smulₛₗ f := f.map_smul'

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] theorem congr_fun {f g : A →ₛₙₐ[φ] B} (h : f = g) (x : A) : f x = g x := by sorry


@[simp]
theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f :=
  rfl

@[simp]
theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  rfl

@[target] theorem toDistribMulActionHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toDistribMulActionHom = ↑f := by sorry


@[target] theorem toMulHom_eq_coe (f : A →ₛₙₐ[φ] B) : f.toMulHom = ↑f := by sorry


@[target] theorem coe_to_distribMulActionHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₑ+[φ] B) = f := by sorry


@[target] theorem coe_to_mulHom (f : A →ₛₙₐ[φ] B) : ⇑(f : A →ₙ* B) = f := by sorry


theorem to_distribMulActionHom_injective {f g : A →ₛₙₐ[φ] B}
    (h : (f : A →ₑ+[φ] B) = (g : A →ₑ+[φ] B)) : f = g := by
  ext a
  exact DistribMulActionHom.congr_fun h a

@[target] theorem to_mulHom_injective {f g : A →ₛₙₐ[φ] B} (h : (f : A →ₙ* B) = (g : A →ₙ* B)) : f = g := by
  sorry


@[target] theorem coe_distribMulActionHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₑ+[φ] B) = ⟨⟨f, h₁⟩, h₂, h₃⟩ := by
  sorry


@[target] theorem coe_mulHom_mk (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) : A →ₙ* B) = ⟨f, h₄⟩ := by
  sorry


@[simp] -- Marked as `@[simp]` because `MulActionSemiHomClass.map_smulₛₗ` can't be.
protected theorem map_smul (f : A →ₛₙₐ[φ] B) (c : R) (x : A) : f (c • x) = (φ c) • f x :=
  map_smulₛₗ _ _ _

protected theorem map_add (f : A →ₛₙₐ[φ] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _

protected theorem map_mul (f : A →ₛₙₐ[φ] B) (x y : A) : f (x * y) = f x * f y :=
  map_mul _ _ _

protected theorem map_zero (f : A →ₛₙₐ[φ] B) : f 0 = 0 :=
  map_zero _

/-- The identity map as a `NonUnitalAlgHom`. -/
protected def id (R A : Type*) [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] : A →ₙₐ[R] A :=
  { NonUnitalRingHom.id A with
    toFun := id
    map_smul' := fun _ _ => rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id :=
  rfl

instance : Zero (A →ₛₙₐ[φ] B) :=
  ⟨{ (0 : A →ₑ+[φ] B) with map_mul' := by simp }⟩

instance : One (A →ₙₐ[R] A) :=
  ⟨NonUnitalAlgHom.id R A⟩

@[target] theorem coe_zero : (↑(0 : R) : A) = 0 := by sorry


@[target] theorem coe_one : (↑(1 : R) : A) = 1 := by sorry


@[target] theorem zero_apply (a : A) : (0 : A →ₛₙₐ[φ] B) a = 0 := by sorry


@[target] theorem one_apply (a : A) : (1 : A →ₙₐ[R] A) a = a := by sorry


instance : Inhabited (A →ₛₙₐ[φ] B) :=
  ⟨0⟩

variable {φ' : S →* R} {ψ : S →* T} {χ : R →* T}

set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


@[target] theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := by sorry


@[target] theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := by sorry


variable {B₁ : Type*} [NonUnitalNonAssocSemiring B₁] [DistribMulAction R B₁]

/-- The inverse of a bijective morphism is a morphism. -/
/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A)
    (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : B₁ →ₙₐ[R] A := by sorry


@[target] theorem coe_inverse (f : A →ₙₐ[R] B₁) (g : B₁ → A) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : (inverse f g h₁ h₂ : B₁ → A) = g := by sorry


/-- The inverse of a bijective morphism is a morphism. -/
def inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    B →ₛₙₐ[φ'] A :=
  { (f : A →ₙ* B).inverse g h₁ h₂, (f : A →ₑ+[φ] B).inverse' g k h₁ h₂ with
    map_zero' := by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← f.map_zero, h₁]
    map_add' := fun x y ↦ by
      simp only [MulHom.toFun_eq_coe, MulHom.inverse_apply]
      rw [← h₂ x, ← h₂ y, ← map_add, h₁, h₂, h₂] }

@[simp]
theorem coe_inverse' (f : A →ₛₙₐ[φ] B) (g : B → A)
    (k : Function.RightInverse φ' φ)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) :
    (inverse' f g k h₁ h₂ : B → A) = g :=
  rfl

/-! ### Operations on the product type

Note that much of this is copied from [`LinearAlgebra/Prod`](../../LinearAlgebra/Prod). -/


section Prod

variable (R A B)
variable  [DistribMulAction R B]

/-- The first projection of a product is a non-unital alg_hom. -/
/-- First projection as `AlgHom`. -/
def fst : A × B →ₐ[R] A := by sorry


/-- The second projection of a product is a non-unital alg_hom. -/
/-- Second projection as `AlgHom`. -/
def snd : A × B →ₐ[R] B := by sorry


variable {R A B}
variable [DistribMulAction R C]

/-- The prod of two morphisms is a morphism. -/
@[simps]
def prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : A →ₙₐ[R] B × C where
  toFun := Pi.prod f g
  map_zero' := by simp only [Pi.prod, Prod.mk_zero_zero, map_zero]
  map_add' x y := by simp only [Pi.prod, Prod.mk_add_mk, map_add]
  map_mul' x y := by simp only [Pi.prod, Prod.mk_mul_mk, map_mul]
  map_smul' c x := by simp only [Pi.prod, map_smul, MonoidHom.id_apply, id_eq, Prod.smul_mk]

@[target] theorem coe_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : ⇑(f.prod g) = Pi.prod f g := by sorry


@[target] theorem fst_prod (f : A →ₐ[R] B) (g : A →ₐ[R] C) : (fst R B C).comp (prod f g) = f := by sorry


@[simp]
theorem snd_prod (f : A →ₙₐ[R] B) (g : A →ₙₐ[R] C) : (snd R B C).comp (prod f g) = g := by
  rfl

@[target] theorem prod_fst_snd : prod (fst R A B) (snd R A B) = AlgHom.id R _ := by sorry


/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
/-- Taking the product of two maps with the same domain is equivalent to taking the product of
their codomains. -/
@[simps]
def prodEquiv : (A →ₐ[R] B) × (A →ₐ[R] C) ≃ (A →ₐ[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ((fst _ _ _).comp f, (snd _ _ _).comp f)
  left_inv f := by sorry


variable (R A B)

/-- The left injection into a product is a non-unital algebra homomorphism. -/
/-- The left injection into a product is a non-unital algebra homomorphism. -/
def inl : A →ₙₐ[R] A × B := by sorry


/-- The right injection into a product is a non-unital algebra homomorphism. -/
/-- The right injection into a product is a non-unital algebra homomorphism. -/
def inr : B →ₙₐ[R] A × B := by sorry


variable {R A B}

@[target] theorem coe_inl : (inl R A B : A → A × B) = fun x => (x, 0) := by sorry


@[target] theorem inl_apply (x : A) : inl R A B x = (x, 0) := by sorry


@[target] theorem coe_inr : (inr R A B : B → A × B) = Prod.mk 0 := by sorry


theorem inr_apply (x : B) : inr R A B x = (0, x) :=
  rfl

end Prod

end NonUnitalAlgHom

/-! ### Interaction with `AlgHom` -/

namespace AlgHom

variable {F R : Type*} [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A]
  [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) [FunLike F A B] [AlgHomClass F R A B] : NonUnitalAlgHomClass F R A B :=
  { ‹AlgHomClass F R A B› with map_smulₛₗ := map_smul }

/-- A unital morphism of algebras is a `NonUnitalAlgHom`. -/
@[coe]
def toNonUnitalAlgHom (f : A →ₐ[R] B) : A →ₙₐ[R] B :=
  { f with map_smul' := map_smul f }

instance NonUnitalAlgHom.hasCoe : CoeOut (A →ₐ[R] B) (A →ₙₐ[R] B) :=
  ⟨toNonUnitalAlgHom⟩

@[target] theorem toNonUnitalAlgHom_eq_coe (f : A →ₐ[R] B) : f.toNonUnitalAlgHom = f := by sorry


end AlgHom

section RestrictScalars

namespace NonUnitalAlgHom

variable (R : Type*) {S A B : Type*} [Monoid R] [Monoid S]
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [MulAction R S]
    [DistribMulAction S A] [DistribMulAction S B] [DistribMulAction R A] [DistribMulAction R B]
    [IsScalarTower R S A] [IsScalarTower R S B]

/-- If a monoid `R` acts on another monoid `S`, then a non-unital algebra homomorphism
over `S` can be viewed as a non-unital algebra homomorphism over `R`. -/
/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      sorry


@[target] theorem restrictScalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x := by sorry


@[target] theorem coe_restrictScalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f := by sorry


lemma coe_restrictScalars' (f : A →ₙₐ[S] B) : (f.restrictScalars R : A → B) = f := rfl

@[target] theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := by sorry


end NonUnitalAlgHom

end RestrictScalars
