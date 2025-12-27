import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.Homotopy

/-!
# The action of a bifunctor on homological complexes factors through homotopies

Given a `TotalComplexShape c₁ c₂ c`, a functor `F : C₁ ⥤ C₂ ⥤ D`,
we shall show in this file that up to homotopy the morphism
`mapBifunctorMap f₁ f₂ F c` only depends on the homotopy classes of
the morphism `f₁` in `HomologicalComplex C c₁` and of
the morphism `f₂` in `HomologicalComplex C c₂` (TODO).

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category C₁] [Category C₂] [Category D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace HomologicalComplex

variable {K₁ L₁ : HomologicalComplex C₁ c₁} {f₁ f₁' : K₁ ⟶ L₁} (h₁ : Homotopy f₁ f₁')
  {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ : K₂ ⟶ L₂)
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [HasMapBifunctor K₁ K₂ F c]
  [HasMapBifunctor L₁ L₂ F c]

namespace mapBifunctorMapHomotopy

/-- Auxiliary definition for `mapBifunctorMapHomotopy₁`. -/
noncomputable def hom₁ (j j' : J) :
    (mapBifunctor K₁ K₂ F c).X j ⟶ (mapBifunctor L₁ L₂ F c).X j' :=
  HomologicalComplex₂.totalDesc _
    (fun i₁ i₂ _ => ComplexShape.ε₁ c₁ c₂ c (c₁.prev i₁, i₂) •
      (F.map (h₁.hom i₁ (c₁.prev i₁))).app (K₂.X i₂) ≫
      (F.obj (L₁.X (c₁.prev i₁))).map (f₂.f i₂) ≫ ιMapBifunctorOrZero L₁ L₂ F c _ _ j')

@[reassoc]
lemma ιMapBifunctor_hom₁ (i₁ i₁' : I₁) (i₂ : I₂) (j j' : J)
    (h : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) (h' : c₁.prev i₁' = i₁) :
    ιMapBifunctor K₁ K₂ F c i₁' i₂ j h ≫ hom₁ h₁ f₂ F c j j' = ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) •
      (F.map (h₁.hom i₁' i₁)).app (K₂.X i₂) ≫ (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        ιMapBifunctorOrZero L₁ L₂ F c _ _ j' := by
  subst h'
  simp [hom₁]

lemma zero₁ (j j' : J) (h : ¬ c.Rel j' j) :
    hom₁ h₁ f₂ F c j j' = 0 := by
  ext i₁ i₂ h'
  dsimp [hom₁]
  rw [comp_zero, HomologicalComplex₂.ι_totalDesc]
  by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
  · rw [ιMapBifunctorOrZero_eq_zero, comp_zero, comp_zero, smul_zero]
    intro h₄
    apply h
    rw [← h', ← h₄]
    exact ComplexShape.rel_π₁ c₂ c h₃ i₂
  · dsimp
    rw [h₁.zero _ _ h₃, Functor.map_zero, zero_app, zero_comp, smul_zero]

@[target]
lemma comm₁_aux {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁') {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') (j : J)
    (hj : ComplexShape.π c₁ c₂ c (i₁', i₂) = j) :
    ComplexShape.ε₁ c₁ c₂ c (i₁, i₂) • (F.map (h₁.hom i₁' i₁)).app (K₂.X i₂) ≫
      (F.obj (L₁.X i₁)).map (f₂.f i₂) ≫
        (((F.mapBifunctorHomologicalComplex c₁ c₂).obj L₁).obj L₂).d₂ c i₁ i₂ j =
    -(((F.mapBifunctorHomologicalComplex c₁ c₂).obj K₁).obj K₂).d₂ c i₁' i₂ (c.next j) ≫
      hom₁ h₁ f₂ F c (c.next j) j := by sorry

@[target]
lemma comm₁ (j : J) :
    (mapBifunctorMap f₁ f₂ F c).f j =
    (mapBifunctor K₁ K₂ F c).d j (c.next j) ≫
          mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c (c.next j) j +
        mapBifunctorMapHomotopy.hom₁ h₁ f₂ F c j (c.prev j) ≫
          (mapBifunctor L₁ L₂ F c).d (c.prev j) j +
      (mapBifunctorMap f₁' f₂ F c).f j := by sorry

end mapBifunctorMapHomotopy

open mapBifunctorMapHomotopy in
/-- The homotopy between `mapBifunctorMap f₁ f₂ F c` and `mapBifunctorMap f₁' f₂ F c` that
is induced by an homotopy between `f₁` and `f₁'`. -/
noncomputable def mapBifunctorMapHomotopy₁ :
    Homotopy (mapBifunctorMap f₁ f₂ F c) (mapBifunctorMap f₁' f₂ F c) where
  hom := hom₁ h₁ f₂ F c
  zero := zero₁ h₁ f₂ F c
  comm := comm₁ h₁ f₂ F c

end HomologicalComplex
