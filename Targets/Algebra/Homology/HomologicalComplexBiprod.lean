import VerifiedAgora.tagger
/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.Additive

/-! Binary biproducts of homological complexes

In this file, it is shown that if two homological complex `K` and `L` in
a preadditive category are such that for all `i : ι`, the binary biproduct
`K.X i ⊞ L.X i` exists, then `K ⊞ L` exists, and there is an isomorphism
`biprodXIso K L i : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`.

-/
open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [∀ i, HasBinaryBiproduct (K.X i) (L.X i)]

instance (i : ι) : HasBinaryBiproduct ((eval C c i).obj K) ((eval C c i).obj L) := by
  dsimp [eval]
  infer_instance

instance (i : ι) : HasLimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasLimitOfIso e.symm

instance (i : ι) : HasColimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasColimitOfIso e

instance : HasBinaryBiproduct K L := HasBinaryBiproduct.of_hasBinaryProduct _ _

instance (i : ι) : PreservesBinaryBiproduct K L (eval C c i) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

/-- The canonical isomorphism `(K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`. -/
noncomputable def biprodXIso (i : ι) : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i) :=
  (eval C c i).mapBiprod K L

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

@[reassoc (attr := simp)]
lemma biprodXIso_hom_fst (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.fst = (biprod.fst : K ⊞ L ⟶ K).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
lemma biprodXIso_hom_snd (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.snd = (biprod.snd : K ⊞ L ⟶ L).f i := by
  simp [biprodXIso]

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

variable {K L}
variable {M : HomologicalComplex C c}

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

@[target, reassoc (attr := by sorry

end HomologicalComplex
