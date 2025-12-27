import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Basic

/-!
# Homomorphisms of `R`-algebras

This file defines bundled homomorphisms of `R`-algebras.

## Main definitions

* `AlgHom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `Algebra.ofId R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as an `AlgHom`.

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
-/

universe u v w u₁ v₁

/-- Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`. -/
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r

/-- Reinterpret an `AlgHom` as a `RingHom` -/
add_decl_doc AlgHom.toRingHom

@[inherit_doc AlgHom]
infixr:25 " →ₐ " => AlgHom _

@[inherit_doc]
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

/-- `AlgHomClass F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`. -/
class AlgHomClass (F : Type*) (R A B : outParam Type*)
  [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [FunLike F A B] extends RingHomClass F A B : Prop where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

-- For now, don't replace `AlgHom.commutes` and `AlgHomClass.commutes` with the more generic lemma.
-- The file `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone` slows down by
-- 15% if we would do so (see benchmark on PR https://github.com/leanprover-community/mathlib4/pull/18040).
-- attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R A B F : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B] [FunLike F A B]

-- see Note [lower instance priority]
instance (priority := 100) linearMapClass [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [Algebra.smul_def, map_mul, commutes, RingHom.id_apply] }

/-- Turn an element of a type `F` satisfying `AlgHomClass F α β` into an actual
`AlgHom`. This is declared as the default coercion from `F` to `α →+* β`. -/
/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def toAlgHom : S →ₐ[R] A := by sorry


instance coeTC {F : Type*} [FunLike F A B] [AlgHomClass F R A B] : CoeTC F (A →ₐ[R] B) :=
  ⟨AlgHomClass.toAlgHom⟩

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

instance funLike : FunLike (A →ₐ[R] B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩
    congr

instance algHomClass : AlgHomClass (A →ₐ[R] B) R A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  commutes f := f.commutes'

/-- See Note [custom simps projection] -/
def Simps.apply {R : Type u} {α : Type v} {β : Type w} [CommSemiring R]
    [Semiring α] [Semiring β] [Algebra R α] [Algebra R β] (f : α →ₐ[R] β) : α → β := f

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    ⇑(f : A →ₐ[R] B) = f :=
  rfl

@[target] theorem toFun_eq_coe (f : A →ₛₙₐ[φ] B) : f.toFun = ⇑f := by sorry


/-- Reinterpret a ring equivalence as a monoid homomorphism. -/
abbrev toMonoidHom (e : R ≃+* S) : R →* S := by sorry


instance coeOutMonoidHom : CoeOut (A →ₐ[R] B) (A →* B) :=
  ⟨AlgHom.toMonoidHom'⟩

/-- Reinterpret a ring equivalence as an `AddMonoid` homomorphism. -/
abbrev toAddMonoidHom (e : R ≃+* S) : R →+ S := by sorry


instance coeOutAddMonoidHom : CoeOut (A →ₐ[R] B) (A →+ B) :=
  ⟨AlgHom.toAddMonoidHom'⟩

@[target] theorem coe_mk (f : A → B) (h₁ h₂ h₃ h₄) : ⇑(⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by sorry


@[target] theorem coe_mks {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩, h₅⟩ : A →ₐ[R] B) = f := by sorry


@[target] theorem coe_ringHom_mk {f : A →+* B} (h) : ((⟨f, h⟩ : A →ₐ[R] B) : A →+* B) = f := by sorry

@[target] theorem toRingHom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f := by sorry


@[target] theorem coe_toRingHom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f := by sorry


@[target] theorem coe_toMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f := by sorry


@[target] theorem coe_toAddMonoidHom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f := by sorry


variable (φ : A →ₐ[R] B)

@[target] theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) (↑) := by sorry


@[target] theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ := by sorry


@[target] theorem coe_ringHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+* B) := by sorry


@[target] theorem coe_monoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →* B) := by sorry


@[target] theorem coe_addMonoidHom_injective : Function.Injective ((↑) : (A →ₐ[R] B) → A →+ B) := by sorry


protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  DFunLike.congr_fun H x

protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  DFunLike.congr_arg φ h

@[target] theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiring S] [Semiring A] (h1 h2 : Algebra S A)
    (h : ∀ (r : S) (x : A), (by sorry


@[target] theorem mk_coe (f : A →ₛₙₐ[φ] B) (h₁ h₂ h₃ h₄) : (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →ₛₙₐ[φ] B) = f := by
  sorry


/-- `mul_comm` for `Algebra`s when one element is from the base ring. -/
@[target] theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r := by sorry


@[target] theorem comp_algebraMap : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B := by sorry


/-- If a `RingHom` is `R`-linear, then it is an `AlgHom`. -/
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


@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl

section

variable (R A)

/-- Identity map as an `AlgHom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }

@[target] theorem coe_id : ⇑(NonUnitalAlgHom.id R A) = id := by sorry


@[target] theorem id_toRingHom : (AlgHom.id R A : A →+* A) = RingHom.id _ := by sorry


end

@[target] theorem id_apply (p : A) : AlgHom.id R A p = p := by sorry


/-- Composition of algebra homeomorphisms. -/
set_option linter.unusedVariables false in
/-- The composition of morphisms is a morphism. -/
def comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [κ : MonoidHom.CompTriple φ ψ χ] :
    A →ₛₙₐ[χ] C := by sorry


@[target] theorem coe_comp (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] :
    ⇑(f.comp g) = (⇑f) ∘ (⇑g) := by sorry


@[target] theorem comp_apply (f : B →ₛₙₐ[ψ] C) (g : A →ₛₙₐ[φ] B) [MonoidHom.CompTriple φ ψ χ] (x : A) :
    f.comp g x = f (g x) := by sorry


@[target] theorem comp_toRingHom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) :
    (φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ := by sorry


@[target] theorem comp_id : φ.comp (AlgHom.id R A) = φ := by sorry


@[target] theorem id_comp : (AlgHom.id R B).comp φ = φ := by sorry


@[target] theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := by sorry


/-- R-Alg ⥤ R-Mod -/
/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₗ[R] B where
  toFun := by sorry


@[target] theorem toLinearMap_apply (p : A) : φ.toLinearMap p = φ p := by sorry


@[target] theorem toLinearMap_injective :
    Function.Injective (toLinearMap : _ → A →ₗ[R] B) := by sorry


@[target] theorem comp_toLinearMap (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap := by sorry


@[target] theorem toLinearMap_id : toLinearMap (AlgHom.id R A) = LinearMap.id := by sorry


/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
/-- Promote a `LinearMap` to an `AlgHom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) :
    A →ₐ[R] B :=
  { f.toAddMonoidHom with
    toFun := f
    map_one' := map_one
    map_mul' := map_mul
    commutes' := fun c => by sorry


@[target] theorem ofLinearMap_toLinearMap (map_one) (map_mul) :
    ofLinearMap φ.toLinearMap map_one map_mul = φ := by sorry


@[target] theorem toLinearMap_ofLinearMap (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f := by sorry


@[target] theorem ofLinearMap_id (map_one) (map_mul) :
    ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A := by sorry


@[target] theorem map_smul_of_tower {R'} [SMul R' A] [SMul R' B] [LinearMap.CompatibleSMul A B R' R] (r : R')
    (x : A) : φ (r • x) = r • φ x := by sorry


@[simps (config := .lemmasOnly) toSemigroup_toMul_mul toOne_one]
instance End : Monoid (A →ₐ[R] A) where
  mul := comp
  mul_assoc _ _ _ := rfl
  one := AlgHom.id R A
  one_mul _ := rfl
  mul_one _ := rfl

@[simp]
theorem one_apply (x : A) : (1 : A →ₐ[R] A) x = x :=
  rfl

@[target] theorem mul_apply (φ ψ : A →ₐ[R] A) (x : A) : (φ * ψ) x = φ (ψ x) := by sorry


@[target] theorem algebraMap_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) :
    algebraMap R B y = f x := by sorry


end Semiring
end AlgHom

namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
/-- Reinterpret a `RingHom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiring R] [Semiring S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with
    toFun := f
    commutes' := fun n => by sorry


@[target] lemma toNatAlgHom_coe [Semiring R] [Semiring S] (f : R →+* S) :
    ⇑f.toNatAlgHom = ⇑f := by sorry


lemma toNatAlgHom_apply [Semiring R] [Semiring S] (f : R →+* S) (x : R) :
    f.toNatAlgHom x = f x := rfl

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by sorry


@[target] lemma toIntAlgHom_coe [Ring R] [Ring S] (f : R →+* S) :
    ⇑f.toIntAlgHom = ⇑f := by sorry


@[target] lemma toIntAlgHom_apply [Ring R] [Ring S] (f : R →+* S) (x : R) :
    f.toIntAlgHom x = f x := by sorry


@[target] lemma toIntAlgHom_injective [Ring R] [Ring S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) := by sorry


end RingHom

namespace Algebra

variable (R : Type u) (A : Type v) (B : Type w)
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- `AlgebraMap` as an `AlgHom`. -/
/-- `AlgebraMap` as an `AlgHom`. -/
def ofId : R →ₐ[R] A := by sorry


variable {R}

@[target] theorem ofId_apply (r) : ofId R A r = algebraMap R A r := by sorry


/-- This is a special case of a more general instance that we define in a later file. -/
instance subsingleton_id : Subsingleton (R →ₐ[R] A) :=
  ⟨fun f g => AlgHom.ext fun _ => (f.commutes _).trans (g.commutes _).symm⟩

/-- This ext lemma closes trivial subgoals create when chaining heterobasic ext lemmas. -/
/-- This ext lemma closes trivial subgoals create when chaining heterobasic ext lemmas. -/
@[target] theorem ext_id (f g : R →ₐ[R] A) : f = g := by sorry


@[target] theorem comp_ofId (φ : A →ₐ[R] B) : φ.comp (Algebra.ofId R A) = Algebra.ofId R B := by sorry


section MulDistribMulAction

instance : MulDistribMulAction (A →ₐ[R] A) Aˣ where
  smul f := Units.map f
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl
  smul_mul _ _ _ := by ext; exact map_mul _ _ _
  smul_one _ := by ext; exact map_one _

@[target] theorem smul_units_def (f : A →ₐ[R] A) (x : Aˣ) :
    f • x = Units.map (f : A →* A) x := by sorry


end MulDistribMulAction

variable (M : Submonoid R) {B : Type w} [CommRing B] [Algebra R B] {A}

@[target] lemma algebraMapSubmonoid_map_eq (f : A →ₐ[R] B) :
    (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M := by
  sorry


@[target] lemma algebraMapSubmonoid_le_comap (f : A →ₐ[R] B) :
    algebraMapSubmonoid A M ≤ (algebraMapSubmonoid B M).comap f.toRingHom := by
  sorry


end Algebra

namespace MulSemiringAction

variable {M G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Monoid M] [MulSemiringAction M A] [SMulCommClass M R A]

/-- Each element of the monoid defines an algebra homomorphism.

This is a stronger version of `MulSemiringAction.toRingHom` and
`DistribMulAction.toLinearMap`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  { MulSemiringAction.toRingHom _ _ m with
    toFun := fun a => m • a
    commutes' := smul_algebraMap _ }

@[target] theorem toAlgHom_injective [FaithfulSMul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := by sorry


end MulSemiringAction
