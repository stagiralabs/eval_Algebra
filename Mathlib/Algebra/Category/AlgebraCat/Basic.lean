import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# Category instance for algebras over a commutative ring

We introduce the bundled category `AlgebraCat` of algebras over a fixed commutative ring `R` along
with the forgetful functors to `RingCat` and `ModuleCat`. We furthermore show that the functor
associating to a type the free `R`-algebra on that type is left adjoint to the forgetful functor.
-/

open CategoryTheory Limits

universe v u

variable (R : Type u) [CommRing R]

/-- The category of R-algebras and their morphisms. -/
structure AlgebraCat where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [isRing : Ring carrier]
  [isAlgebra : Algebra R carrier]

attribute [instance] AlgebraCat.isRing AlgebraCat.isAlgebra

initialize_simps_projections AlgebraCat (-isRing, -isAlgebra)

namespace AlgebraCat

instance : CoeSort (AlgebraCat R) (Type v) :=
  ⟨AlgebraCat.carrier⟩

attribute [coe] AlgebraCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `AlgebraCat R`. -/
abbrev of (X : Type v) [Ring X] [Algebra R X] : AlgebraCat.{v} R :=
  ⟨X⟩

@[target] theorem coe_of (α : Type*) [BooleanRing α] : ↥(of α) = α := by sorry


variable {R} in
/-- The type of morphisms in `AlgebraCat R`. -/
@[ext]
structure Hom (A B : AlgebraCat.{v} R) where
  private mk ::
  /-- The underlying algebra map. -/
  hom' : A →ₐ[R] B

instance : Category (AlgebraCat.{v} R) where
  Hom A B := Hom A B
  id A := ⟨AlgHom.id R A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory (AlgebraCat.{v} R) (· →ₐ[R] ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

variable {R} in
/-- Turn a morphism in `AlgebraCat` back into an `AlgHom`. -/
abbrev Hom.hom {A B : AlgebraCat.{v} R} (f : Hom A B) :=
  ConcreteCategory.hom (C := AlgebraCat R) f

variable {R} in
/-- Typecheck an `AlgHom` as a morphism in `AlgebraCat`. -/
/-- Typecheck a `MonoidWithZeroHom` as a morphism in `GrpWithZero`. -/
abbrev ofHom {X Y : Type u} [GroupWithZero X] [GroupWithZero Y]
    (f : MonoidWithZeroHom X Y) : of X ⟶ of Y := by sorry


variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
def Hom.Simps.hom (A B : AlgebraCat.{v} R) (f : Hom A B) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[target] lemma hom_id {X : GrpWithZero} : ConcreteCategory.hom (𝟙 X : X ⟶ X) = MonoidWithZeroHom.id X := by sorry

@[target] theorem id_apply (p : A) : AlgHom.id R A p = p := by sorry


@[simp]
lemma hom_comp {A B C : AlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
lemma comp_apply {A B C : AlgebraCat.{v} R} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by simp

@[target] lemma hom_ext {R S : BoolRing} {f g : R ⟶ S} (hf : f.hom = g.hom) : f = g := by sorry


@[simp]
lemma hom_ofHom {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) : (ofHom f).hom = f := rfl

@[simp]
lemma ofHom_hom {A B : AlgebraCat.{v} R} (f : A ⟶ B) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
lemma ofHom_id {X : Type v} [Ring X] [Algebra R X] : ofHom (AlgHom.id R X) = 𝟙 (of R X) := rfl

@[simp]
lemma ofHom_comp {X Y Z : Type v} [Ring X] [Ring Y] [Ring Z] [Algebra R X] [Algebra R Y]
    [Algebra R Z] (f : X →ₐ[R] Y) (g : Y →ₐ[R] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

lemma ofHom_apply {R : Type u} [CommRing R] {X Y : Type v} [Ring X] [Algebra R X] [Ring Y]
    [Algebra R Y] (f : X →ₐ[R] Y) (x : X) : ofHom f x = f x := rfl

lemma inv_hom_apply {A B : AlgebraCat.{v} R} (e : A ≅ B) (x : A) : e.inv (e.hom x) = x := by
  rw [← comp_apply]
  simp

lemma hom_inv_apply {A B : AlgebraCat.{v} R} (e : A ≅ B) (x : B) : e.hom (e.inv x) = x := by
  rw [← comp_apply]
  simp

instance : Inhabited (AlgebraCat R) :=
  ⟨of R R⟩

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps]
def forget : HomologicalComplex V c ⥤ GradedObject ι V where
  obj C := by sorry


lemma forget_map {A B : AlgebraCat.{v} R} (f : A ⟶ B) :
    (forget (AlgebraCat.{v} R)).map f = f :=
  rfl

instance {S : AlgebraCat.{v} R} : Ring ((forget (AlgebraCat R)).obj S) :=
  (inferInstance : Ring S.carrier)

instance {S : AlgebraCat.{v} R} : Algebra R ((forget (AlgebraCat R)).obj S) :=
  (inferInstance : Algebra R S.carrier)

instance hasForgetToRing : HasForget₂ (AlgebraCat.{v} R) RingCat.{v} where
  forget₂ :=
    { obj := fun A => RingCat.of A
      map := fun f => RingCat.ofHom f.hom.toRingHom }

instance hasForgetToModule : HasForget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R) where
  forget₂ :=
    { obj := fun M => ModuleCat.of R M
      map := fun f => ModuleCat.ofHom f.hom.toLinearMap }

@[simp]
lemma forget₂_module_obj (X : AlgebraCat.{v} R) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R)).obj X = ModuleCat.of R X :=
  rfl

@[simp]
lemma forget₂_module_map {X Y : AlgebraCat.{v} R} (f : X ⟶ Y) :
    (forget₂ (AlgebraCat.{v} R) (ModuleCat.{v} R)).map f = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

variable {R} in
/-- Forgetting to the underlying type and then building the bundled object returns the original
algebra. -/
@[simps]
def ofSelfIso (M : AlgebraCat.{v} R) : AlgebraCat.of R M ≅ M where
  hom := 𝟙 M
  inv := 𝟙 M

/-- The "free algebra" functor, sending a type `S` to the free algebra on `S`. -/
/-- Any lattice over a PID is a free `R`-module.
Note that under our conditions, `NoZeroSMulDivisors R K` simply says that `algebraMap R K` is
injective. -/
instance free [NoZeroSMulDivisors R K] (M : Submodule R V) [IsLattice K M] : Module.Free R M := by
  sorry


/-- The free/forget adjunction for `R`-algebras. -/
def adj : free.{u} R ⊣ forget (AlgebraCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ =>
        { toFun := fun f ↦ (FreeAlgebra.lift _).symm f.hom
          invFun := fun f ↦ ofHom <| (FreeAlgebra.lift _) f
          left_inv := fun f ↦ by aesop
          right_inv := fun f ↦ by simp [forget_obj, forget_map] } }

instance : (forget (AlgebraCat.{u} R)).IsRightAdjoint := (adj R).isRightAdjoint

end AlgebraCat

variable {R}
variable {X₁ X₂ : Type u}

/-- Build an isomorphism in the category `AlgebraCat R` from a `AlgEquiv` between `Algebra`s. -/
@[simps]
def AlgEquiv.toAlgebraIso {g₁ : Ring X₁} {g₂ : Ring X₂} {m₁ : Algebra R X₁} {m₂ : Algebra R X₂}
    (e : X₁ ≃ₐ[R] X₂) : AlgebraCat.of R X₁ ≅ AlgebraCat.of R X₂ where
  hom := AlgebraCat.ofHom (e : X₁ →ₐ[R] X₂)
  inv := AlgebraCat.ofHom (e.symm : X₂ →ₐ[R] X₁)

namespace CategoryTheory.Iso

/-- Build a `AlgEquiv` from an isomorphism in the category `AlgebraCat R`. -/
@[simps]
def toAlgEquiv {X Y : AlgebraCat R} (i : X ≅ Y) : X ≃ₐ[R] Y :=
  { i.hom.hom with
    toFun := i.hom
    invFun := i.inv
    left_inv := fun x ↦ by simp
    right_inv := fun x ↦ by simp }

end CategoryTheory.Iso

/-- Algebra equivalences between `Algebra`s are the same as (isomorphic to) isomorphisms in
`AlgebraCat`. -/
@[simps]
def algEquivIsoAlgebraIso {X Y : Type u} [Ring X] [Ring Y] [Algebra R X] [Algebra R Y] :
    (X ≃ₐ[R] Y) ≅ AlgebraCat.of R X ≅ AlgebraCat.of R Y where
  hom e := e.toAlgebraIso
  inv i := i.toAlgEquiv

instance AlgebraCat.forget_reflects_isos : (forget (AlgebraCat.{u} R)).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    let i := asIso ((forget (AlgebraCat.{u} R)).map f)
    let e : X ≃ₐ[R] Y := { f.hom, i.toEquiv with }
    exact e.toAlgebraIso.isIso_hom
