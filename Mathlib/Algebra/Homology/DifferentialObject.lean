import VerifiedAgora.tagger
/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.DifferentialObject

/-!
# Homological complexes are differential graded objects.

We verify that a `HomologicalComplex` indexed by an `AddCommGroup` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-!
We first prove some results about differential graded objects.

Porting note: after the port, move these to their own file.
-/
namespace CategoryTheory.DifferentialObject

variable {β : Type*} [AddCommGroup β] {b : β}
variable {V : Type*} [Category V] [HasZeroMorphisms V]
variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

/-- Since `eqToHom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
/-- Since `eqToHom` only preserves the fact that `X.X i = X.X j` but not `i = j`, this definition
is used to aid the simplifier. -/
abbrev objEqToHom {i j : β} (h : i = j) :
    X.obj i ⟶ X.obj j := by sorry


@[target] theorem objEqToHom_refl (i : β) : X.objEqToHom (refl i) = 𝟙 _ := by sorry


@[target] theorem objEqToHom_d {x y : β} (h : x = y) :
    X.objEqToHom h ≫ X.d y = X.d x ≫ X.objEqToHom (by sorry


@[reassoc (attr := by sorry


@[target] theorem eqToHom_f {C₁ C₂ : HomologicalComplex V c} (h : C₁ = C₂) (n : ι) :
    HomologicalComplex.Hom.f (eqToHom h) n =
      eqToHom (congr_fun (congr_arg HomologicalComplex.X h) n) := by
  sorry


end CategoryTheory.DifferentialObject

open CategoryTheory.DifferentialObject

namespace HomologicalComplex

variable {β : Type*} [AddCommGroup β] (b : β)
variable (V : Type*) [Category V] [HasZeroMorphisms V]

@[target] theorem d_eqToHom (X : HomologicalComplex V (ComplexShape.up' b)) {x y z : β} (h : y = z) :
    X.d x y ≫ eqToHom (congr_arg X.X h) = X.d x z := by sorry


open Classical in
/-- The functor from differential graded objects to homological complexes.
-/
open Classical in
/-- The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgoToHomologicalComplex :
    DifferentialObject ℤ (GradedObjectWithShift b V) ⥤
      HomologicalComplex V (ComplexShape.up' b) where
  obj X :=
    { X := fun i => X.obj i
      d := fun i j =>
        if h : i + b = j then X.d i ≫ X.objEqToHom (show i + (1 : ℤ) • b = j by sorry


/-- The functor from homological complexes to differential graded objects.
-/
@[simps]
def homologicalComplexToDGO :
    HomologicalComplex V (ComplexShape.up' b) ⥤
      DifferentialObject ℤ (GradedObjectWithShift b V) where
  obj X :=
    { obj := fun i => X.X i
      d := fun i => X.d i _ }
  map {X Y} f := { f := f.f }

/-- The unit isomorphism for `dgoEquivHomologicalComplex`.
-/
@[simps!]
def dgoEquivHomologicalComplexUnitIso :
    𝟭 (DifferentialObject ℤ (GradedObjectWithShift b V)) ≅
      dgoToHomologicalComplex b V ⋙ homologicalComplexToDGO b V :=
  NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.obj i) }
      inv := { f := fun i => 𝟙 (X.obj i) } })

/-- The counit isomorphism for `dgoEquivHomologicalComplex`.
-/
@[simps!]
def dgoEquivHomologicalComplexCounitIso :
    homologicalComplexToDGO b V ⋙ dgoToHomologicalComplex b V ≅
      𝟭 (HomologicalComplex V (ComplexShape.up' b)) :=
  NatIso.ofComponents (fun X =>
    { hom := { f := fun i => 𝟙 (X.X i) }
      inv := { f := fun i => 𝟙 (X.X i) } })

/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
/-- The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgoEquivHomologicalComplex :
    DifferentialObject ℤ (GradedObjectWithShift b V) ≌
      HomologicalComplex V (ComplexShape.up' b) where
  functor := by sorry


end HomologicalComplex
