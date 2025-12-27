import VerifiedAgora.tagger
/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.TruncGE
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! # The homology of a canonical truncation

Given an embedding of complex shapes `e : Embedding c c'`,
we relate the homology of `K : HomologicalComplex C c'` and of
`K.truncGE e : HomologicalComplex C c'`.

The main result is that `K.πTruncGE e : K ⟶ K.truncGE e` induces a
quasi-isomorphism in degree `e.f i` for all `i`. (Note that the complex
`K.truncGE e` is exact in degrees that are not in the image of `e.f`.)

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category C] [HasZeroMorphisms C]
  (K L : HomologicalComplex C c') (φ : K ⟶ L) (e : c.Embedding c') [e.IsTruncGE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i']

namespace truncGE'

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)

include hi hk in
lemma hasHomology_sc'_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    ((K.truncGE' e).sc' i j k).HasHomology := by
  have : (K.restriction e).HasHomology j :=
    restriction.hasHomology K e i j k hi hk rfl rfl rfl
      (e.prev_f_of_not_boundaryGE hi hj) (e.next_f hk)
  have := ShortComplex.hasHomology_of_iso ((K.restriction e).isoSc' i j k hi hk)
  let φ := (shortComplexFunctor' C c i j k).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e k (e.not_boundaryGE_next' hj hk)
  exact ShortComplex.hasHomology_of_epi_of_isIso_of_mono φ

lemma hasHomology_of_not_mem_boundary (hj : ¬ e.BoundaryGE j) :
    (K.truncGE' e).HasHomology j :=
  hasHomology_sc'_of_not_mem_boundary K e _ j _ rfl rfl hj

/-- `K.restrictionToTruncGE' e` is a quasi-isomorphism in degrees that are not at the boundary. -/
lemma quasiIsoAt_restrictionToTruncGE' (hj : ¬ e.BoundaryGE j)
    [(K.restriction e).HasHomology j] [(K.truncGE' e).HasHomology j] :
    QuasiIsoAt (K.restrictionToTruncGE' e) j := by
  rw [quasiIsoAt_iff]
  let φ := (shortComplexFunctor C c j).map (K.restrictionToTruncGE' e)
  have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
  have : IsIso φ.τ₂ := K.isIso_restrictionToTruncGE' e j hj
  have : IsIso φ.τ₃ := K.isIso_restrictionToTruncGE' e _ (e.not_boundaryGE_next' hj rfl)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

section

variable {j' : ι'} (hj' : e.f j = j') (hj : e.BoundaryGE j)

@[target]
lemma homologyι_truncGE'XIsoOpcycles_inv_d :
    (K.homologyι j' ≫ (K.truncGE'XIsoOpcycles e hj' hj).inv) ≫ (K.truncGE' e).d j k = 0 := by sorry
@[target, simp]
lemma homologyData_right_g' :
    (homologyData K e i j k hk hj' hj).right.g' = (K.truncGE' e).d j k := sorry

instance truncGE'_hasHomology (i : ι) : (K.truncGE' e).HasHomology i := by
  by_cases hi : e.BoundaryGE i
  · exact ShortComplex.HasHomology.mk' (homologyData K e _ _ _ rfl rfl hi)
  · exact hasHomology_of_not_mem_boundary K e i hi

end truncGE'

variable [HasZeroObject C]

namespace truncGE

instance (i' : ι') : (K.truncGE e).HasHomology i' := by
  dsimp [truncGE]
  infer_instance

/-- The right homology data which allows to show that `K.πTruncGE e`
induces an isomorphism in homology in degrees `j'` such that `e.f j = j'` for some `j`. -/
@[simps]
noncomputable def rightHomologyMapData {i j k : ι} {j' : ι'} (hj' : e.f j = j')
    (hi : c.prev j = i) (hk : c.next j = k) (hj : e.BoundaryGE j) :
    ShortComplex.RightHomologyMapData ((shortComplexFunctor C c' j').map (K.πTruncGE e))
    (ShortComplex.RightHomologyData.canonical (K.sc j'))
    (extend.rightHomologyData (K.truncGE' e) e hj' hi rfl hk rfl
      (truncGE'.homologyData K e i j k hk hj' hj).right) where
  φQ := (K.truncGE'XIsoOpcycles e hj' hj).inv
  φH := 𝟙 _
  commp := by
    change K.pOpcycles j' ≫ _ = _
    simp [truncGE'.homologyData, πTruncGE, e.liftExtend_f _ _ hj',
      K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hj' hj]
  commg' := by
    have hk' : e.f k = c'.next j' := by rw [← hj', e.next_f hk]
    dsimp
    rw [extend.rightHomologyData_g' _ _ _ _ _ _ _ _ hk', πTruncGE,
        e.liftExtend_f _ _ hk', truncGE'.homologyData_right_g']
    by_cases hjk : c.Rel j k
    · simp [K.truncGE'_d_eq_fromOpcycles e hjk hj' hk' hj,
        K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e hk' (e.not_boundaryGE_next hjk)]
      rfl
    · obtain rfl : k = j := by rw [← c.next_eq_self j  (by simpa only [hk] using hjk), hk]
      rw [shape _ _ _ hjk, zero_comp, comp_zero,
        K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e hk' hj]
      simp only [restriction_X, restrictionXIso, eqToIso.inv, eqToIso.hom, assoc,
        eqToHom_trans_assoc, eqToHom_refl, id_comp]
      change 0 = K.fromOpcycles _ _ ≫ _
      rw [← cancel_epi (K.pOpcycles _), comp_zero, p_fromOpcycles_assoc,
        d_pOpcycles_assoc, zero_comp]

end truncGE

@[target]
lemma quasiIsoAt_πTruncGE {j : ι} {j' : ι'} (hj' : e.f j = j') :
    QuasiIsoAt (K.πTruncGE e) j' := by sorry

instance (i : ι) : QuasiIsoAt (K.πTruncGE e) (e.f i) := K.quasiIsoAt_πTruncGE e rfl

@[target]
lemma quasiIso_πTruncGE_iff_isSupported :
    QuasiIso (K.πTruncGE e) ↔ K.IsSupported e := by sorry

lemma acyclic_truncGE_iff_isSupportedOutside :
    (K.truncGE e).Acyclic ↔ K.IsSupportedOutside e := by
  constructor
  · intro hK
    exact ⟨fun i =>
      by simpa only [exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK (e.f i)⟩
  · intro hK i'
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, rfl⟩ := hi'
      simpa only [← exactAt_iff_of_quasiIsoAt (K.πTruncGE e)] using hK.exactAt i
    · exact exactAt_of_isSupported _ e i' (by simpa using hi')

variable {K L}

@[target]
lemma quasiIso_truncGEMap_iff :
    QuasiIso (truncGEMap φ e) ↔ ∀ (i : ι) (i' : ι') (_ : e.f i = i'), QuasiIsoAt φ i' := by sorry

end HomologicalComplex
