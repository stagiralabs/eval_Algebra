import VerifiedAgora.tagger
/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston, Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.ImageToKernel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Opposite categories of complexes
Given a preadditive category `V`, the opposite of its category of chain complexes is equivalent to
the category of cochain complexes of objects in `Vᵒᵖ`. We define this equivalence, and another
analogous equivalence (for a general category of homological complexes with a general
complex shape).

We then show that when `V` is abelian, if `C` is a homological complex, then the homology of
`op(C)` is isomorphic to `op` of the homology of `C` (and the analogous result for `unop`).

## Implementation notes
It is convenient to define both `op` and `opSymm`; this is because given a complex shape `c`,
`c.symm.symm` is not defeq to `c`.

## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/


noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

section

variable {V : Type*} [Category V] [Abelian V]

@[target]
theorem imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.op f.op (by rw [← op_comp, w, op_zero]) =
      (imageSubobjectIso _ ≪≫ (imageOpOp _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).op ≫
          (kernelSubobjectIso _ ≪≫ kernelOpOp _).inv := by sorry

@[target]
theorem imageToKernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.unop f.unop (by rw [← unop_comp, w, unop_zero]) =
      (imageSubobjectIso _ ≪≫ (imageUnopUnop _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).unop ≫
          (kernelSubobjectIso _ ≪≫ kernelUnopUnop _).inv := by sorry

namespace HomologicalComplex

variable {ι V : Type*} [Category V] {c : ComplexShape ι}

section

variable [HasZeroMorphisms V]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
protected def op (X : HomologicalComplex V c) : HomologicalComplex Vᵒᵖ c.symm where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by simp only; rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
protected def opSymm (X : HomologicalComplex V c.symm) : HomologicalComplex Vᵒᵖ c where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by simp only; rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
protected def unop (X : HomologicalComplex Vᵒᵖ c) : HomologicalComplex V c.symm where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by simp only; rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
protected def unopSymm (X : HomologicalComplex Vᵒᵖ c.symm) : HomologicalComplex V c where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by simp only; rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

variable (V c)

/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
def opFunctor : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm where
  obj X := (unop X).op
  map f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j _ => by simp only [op_d, ← op_comp, f.unop.comm] }

/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
def opInverse : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ where
  obj X := op X.unopSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).unop
      comm' := fun i j _ => by simp only [unopSymm_d, ← unop_comp, f.comm] }

/-- Auxiliary definition for `opEquivalence`. -/
def opUnitIso : 𝟭 (HomologicalComplex V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

/-- Auxiliary definition for `opEquivalence`. -/
def opCounitIso : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

/-- Given a category of complexes with objects in `V`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `Vᵒᵖ`. -/
@[simps]
def opEquivalence : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm where
  functor := opFunctor V c
  inverse := opInverse V c
  unitIso := opUnitIso V c
  counitIso := opCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Quiver.Hom.unop_op, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _

/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
def unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm where
  obj X := (unop X).unop
  map f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j _ => by simp only [unop_d, ← unop_comp, f.unop.comm] }

/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
def unopInverse : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ where
  obj X := op X.opSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).op
      comm' := fun i j _ => by simp only [opSymm_d, ← op_comp, f.comm] }

/-- Auxiliary definition for `unopEquivalence`. -/
def unopUnitIso : 𝟭 (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

/-- Auxiliary definition for `unopEquivalence`. -/
def unopCounitIso : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex V c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

/-- Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `V`. -/
@[simps]
def unopEquivalence : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≌ HomologicalComplex V c.symm where
  functor := unopFunctor V c
  inverse := unopInverse V c
  unitIso := unopUnitIso V c
  counitIso := unopCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Quiver.Hom.unop_op, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _

instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.HasHomology i :=
  (inferInstance : (K.sc i).op.HasHomology)

instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.HasHomology i :=
  (inferInstance : (K.sc i).unop.HasHomology)

instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    ((opFunctor _ _).obj (op K)).HasHomology i := by
  dsimp
  infer_instance

instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    ((unopFunctor _ _).obj (op K)).HasHomology i := by
  dsimp
  infer_instance

variable {V c}

@[target, simp]
lemma quasiIsoAt_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((opFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by sorry

@[simp]
lemma quasiIsoAt_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((unopFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  rw [← quasiIsoAt_opFunctor_map_iff]
  rfl

instance {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt φ i] :
    QuasiIsoAt ((opFunctor _ _).map φ.op) i := by
  rw [quasiIsoAt_opFunctor_map_iff]
  infer_instance

instance {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt φ i] :
    QuasiIsoAt ((unopFunctor _ _).map φ.op) i := by
  rw [quasiIsoAt_unopFunctor_map_iff]
  infer_instance

@[target, simp]
lemma quasiIso_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso ((opFunctor _ _).map φ.op) ↔ QuasiIso φ := by sorry

@[target, simp]
lemma quasiIso_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso ((unopFunctor _ _).map φ.op) ↔ QuasiIso φ := by sorry

instance {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] [QuasiIso φ] :
    QuasiIso ((opFunctor _ _).map φ.op) := by
  rw [quasiIso_opFunctor_map_iff]
  infer_instance

instance {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] [QuasiIso φ] :
    QuasiIso ((unopFunctor _ _).map φ.op) := by
  rw [quasiIso_unopFunctor_map_iff]
  infer_instance

lemma ExactAt.op {K : HomologicalComplex V c} {i : ι} (h : K.ExactAt i) :
    K.op.ExactAt i :=
  ShortComplex.Exact.op h

lemma ExactAt.unop {K : HomologicalComplex Vᵒᵖ c} {i : ι} (h : K.ExactAt i) :
    K.unop.ExactAt i :=
  ShortComplex.Exact.unop h

@[target, simp]
lemma exactAt_op_iff (K : HomologicalComplex V c) {i : ι} :
    K.op.ExactAt i ↔ K.ExactAt i :=
  sorry

lemma Acyclic.op {K : HomologicalComplex V c} (h : K.Acyclic) :
    K.op.Acyclic :=
  fun i ↦ (h i).op

@[target]
lemma Acyclic.unop {K : HomologicalComplex Vᵒᵖ c} (h : K.Acyclic) :
    K.unop.Acyclic :=
  sorry

@[target, simp]
lemma acyclic_op_iff (K : HomologicalComplex V c) :
    K.op.Acyclic ↔ K.Acyclic :=
  sorry
def homologyOp (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.homology i ≅ op (K.homology i) :=
  (K.sc i).homologyOpIso

/-- If `K` is a homological complex in the opposite category,
then the homology of `K.unop` identifies to the opposite of the homology of `K`. -/
def homologyUnop (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.homology i ≅ unop (K.homology i) :=
  (K.unop.homologyOp i).unop

section

variable (K : HomologicalComplex V c) (i : ι) [K.HasHomology i]

/-- The canonical isomorphism `K.op.cycles i ≅ op (K.opcycles i)`. -/
def cyclesOpIso : K.op.cycles i ≅ op (K.opcycles i) :=
  (K.sc i).cyclesOpIso

/-- The canonical isomorphism `K.op.opcycles i ≅ op (K.cycles i)`. -/
def opcyclesOpIso : K.op.opcycles i ≅ op (K.cycles i) :=
  (K.sc i).opcyclesOpIso

variable (j : ι)

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

@[target, reassoc]
lemma homologyOp_hom_naturality :
    homologyMap ((opFunctor _ _).map φ.op) _ ≫ (K.homologyOp i).hom =
      (L.homologyOp i).hom ≫ (homologyMap φ i).op :=
  sorry

@[target, reassoc]
lemma opcyclesOpIso_hom_naturality :
    opcyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.opcyclesOpIso i).hom =
      (L.opcyclesOpIso i).hom ≫ (cyclesMap φ i).op :=
  sorry

@[reassoc]
lemma opcyclesOpIso_inv_naturality :
    (cyclesMap φ i).op ≫ (K.opcyclesOpIso i).inv =
      (L.opcyclesOpIso i).inv ≫ opcyclesMap ((opFunctor _ _).map φ.op) _ :=
  ShortComplex.opcyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

@[reassoc]
lemma cyclesOpIso_hom_naturality :
    cyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.cyclesOpIso i).hom =
      (L.cyclesOpIso i).hom ≫ (opcyclesMap φ i).op :=
  ShortComplex.cyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

@[reassoc]
lemma cyclesOpIso_inv_naturality :
    (opcyclesMap φ i).op ≫ (K.cyclesOpIso i).inv =
      (L.cyclesOpIso i).inv ≫ cyclesMap ((opFunctor _ _).map φ.op) _ :=
  ShortComplex.cyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

end

section

variable (V c) [CategoryWithHomology V] (i : ι)

/-- The natural isomorphism `K.op.cycles i ≅ op (K.opcycles i)`. -/
@[simps!]
def cyclesOpNatIso :
    opFunctor V c ⋙ cyclesFunctor Vᵒᵖ c.symm i ≅ (opcyclesFunctor V c i).op :=
  NatIso.ofComponents (fun K ↦ (unop K).cyclesOpIso i)
    (fun _ ↦ cyclesOpIso_hom_naturality _ _)

/-- The natural isomorphism `K.op.opcycles i ≅ op (K.cycles i)`. -/
def opcyclesOpNatIso :
    opFunctor V c ⋙ opcyclesFunctor Vᵒᵖ c.symm i ≅ (cyclesFunctor V c i).op :=
  NatIso.ofComponents (fun K ↦ (unop K).opcyclesOpIso i)
    (fun _ ↦ opcyclesOpIso_hom_naturality _ _)

/-- The natural isomorphism `K.op.homology i ≅ op (K.homology i)`. -/
def homologyOpNatIso :
    opFunctor V c ⋙ homologyFunctor Vᵒᵖ c.symm i ≅ (homologyFunctor V c i).op :=
  NatIso.ofComponents (fun K ↦ (unop K).homologyOp i)
    (fun _ ↦ homologyOp_hom_naturality _ _)

end

end

section

variable [Preadditive V]

instance opFunctor_additive : (@opFunctor ι V _ c _).Additive where

instance unopFunctor_additive : (@unopFunctor ι V _ c _).Additive where

end

end HomologicalComplex
