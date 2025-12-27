import VerifiedAgora.tagger
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.ComposableArrows

/-! The triangulated structure on the homotopy category of complexes

In this file, we show that for any additive category `C`,
the pretriangulated category `HomotopyCategory C (ComplexShape.up ℤ)` is triangulated.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated ComposableArrows

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

namespace CochainComplex

open HomComplex mappingCone

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`. -/
@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
noncomputable def mappingConeCompTriangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    ((triangle g).mor₃ ≫ (inr f)⟦1⟧')

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`
in the homotopy category. It is a distinguished triangle,
see `HomotopyCategory.mappingConeCompTriangleh_distinguished`. -/
noncomputable def mappingConeCompTriangleh :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (mappingConeCompTriangle f g)

@[reassoc]
lemma mappingConeCompTriangle_mor₃_naturality {Y₁ Y₂ Y₃ : CochainComplex C ℤ} (f' : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) (φ : mk₂ f g ⟶ mk₂ f' g') :
    map g g' (φ.app 1) (φ.app 2) (naturality' φ 1 2) ≫ (mappingConeCompTriangle f' g').mor₃ =
      (mappingConeCompTriangle f g).mor₃ ≫
        (map f f' (φ.app 0) (φ.app 1) (naturality' φ 0 1))⟦1⟧' := by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    inl_v_triangle_mor₃_f_assoc, triangle_obj₁, shiftFunctor_obj_X', shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.neg_comp,
    id_comp, Preadditive.comp_neg, inr_f_desc_f_assoc, inr_f_triangle_mor₃_f_assoc, zero_comp,
    comp_zero, and_self]

namespace MappingConeCompHomotopyEquiv

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes, this
is the canonical morphism (which is an homotopy equivalence) from `mappingCone g` to
the mapping cone of the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
noncomputable def hom :
    mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁ :=
  lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by dsimp; simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      ext p _ rfl
      dsimp [mappingConeCompTriangle, map]
      simp [ext_from_iff _ _ _ rfl, inl_v_d_assoc _ (p+1) p (p+2) (by omega) (by omega)])

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes, this
is the canonical morphism (which is an homotopy equivalence) from the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)` to `mappingCone g`. -/
noncomputable def inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g :=
  desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      rw [ext_from_iff _ (p + 1) _ rfl, ext_to_iff _ _ (p + 1) rfl]
      simp [map, δ_zero_cochain_comp,
        Cochain.comp_v _ _ (add_neg_cancel 1) p (p+1) p (by omega) (by omega)])
@[reassoc (attr := simp)]
lemma hom_inv_id : hom f g ≫ inv f g = 𝟙 _ := by
  ext n
  simp [hom, inv, lift_desc_f _ _ _ _ _ _ _ n (n+1) rfl, ext_from_iff _ (n + 1) _ rfl]

set_option maxHeartbeats 400000 in
/-- Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the `homotopyInvHomId` field of the homotopy equivalence
`mappingConeCompHomotopyEquiv f g` between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
noncomputable def homotopyInvHomId : Homotopy (inv f g ≫ hom f g) (𝟙 _) :=
  (Cochain.equivHomotopy _ _).symm ⟨-((snd _).comp ((fst (f ≫ g)).1.comp
    ((inl f).comp (inl _) (by decide)) (show 1 + (-2) = -1 by decide)) (zero_add (-1))), by
      rw [δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
        Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
        δ_comp _ _ (show 1 + (-2) = -1 by decide) 2 (-1) 0 (by decide)
          (by decide) (by decide),
        δ_comp _ _ (show (-1) + (-1) = -2 by decide) 0 0 (-1) (by decide)
          (by decide) (by decide), Int.negOnePow_neg, Int.negOnePow_neg,
        Int.negOnePow_even 2 ⟨1, by decide⟩, Int.negOnePow_one, Units.neg_smul,
        one_smul, one_smul, δ_inl, δ_inl, δ_snd, Cocycle.δ_eq_zero, Cochain.zero_comp, add_zero,
        Cochain.neg_comp, neg_neg]
      ext n
      rw [ext_from_iff _ (n + 1) n rfl, ext_from_iff _ (n + 1) n rfl,
        ext_from_iff _ (n + 2) (n + 1) (by omega)]
      dsimp [hom, inv]
      simp [ext_to_iff _ n (n + 1) rfl, map, Cochain.comp_v _ _
          (add_neg_cancel 1) n (n + 1) n (by omega) (by omega),
        Cochain.comp_v _ _ (show 1 + -2 = -1 by decide) (n + 1) (n + 2) n
          (by omega) (by omega),
        Cochain.comp_v _ _ (show (-1) + -1 = -2 by decide) (n + 2) (n + 1) n
          (by omega) (by omega)]⟩

end MappingConeCompHomotopyEquiv

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the homotopy equivalence `mappingConeCompHomotopyEquiv f g`
between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
noncomputable def mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g)
    (mappingCone (mappingConeCompTriangle f g).mor₁) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[reassoc (attr := simp)]
lemma mappingConeCompHomotopyEquiv_hom_inv_id :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (mappingConeCompHomotopyEquiv f g).inv = 𝟙 _ := by
  simp [mappingConeCompHomotopyEquiv]

@[target, reassoc]
lemma mappingConeCompHomotopyEquiv_comm₁ :
    inr (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp])) ≫
      (mappingConeCompHomotopyEquiv f g).inv = (mappingConeCompTriangle f g).mor₂ := by sorry

@[target, reassoc]
lemma mappingConeCompHomotopyEquiv_comm₂ :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (triangle (mappingConeCompTriangle f g).mor₁).mor₃ =
      (mappingConeCompTriangle f g).mor₃ := by sorry

@[target, reassoc (attr := by sorry

end CochainComplex

namespace HomotopyCategory

open CochainComplex

variable [HasZeroObject C]

@[target]
lemma mappingConeCompTriangleh_distinguished :
    (mappingConeCompTriangleh f g) ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by sorry

end HomotopyCategory
