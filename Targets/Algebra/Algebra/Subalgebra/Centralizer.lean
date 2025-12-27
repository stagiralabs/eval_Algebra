import VerifiedAgora.tagger
/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Properties of centers and centralizers

This file contains theorems about the center and centralizer of a subalgebra.

## Main results

Let `R` be a commutative ring and `A` and `B` two `R`-algebras.
- `Subalgebra.centralizer_sup`: if `S` and `T` are subalgebras of `A`, then the centralizer of
  `S ⊔ T` is the intersection of the centralizer of `S` and the centralizer of `T`.
- `Subalgebra.centralizer_range_includeLeft_eq_center_tensorProduct`: if `B` is free as a module,
  then the centralizer of `A ⊗ 1` in `A ⊗ B` is `C(A) ⊗ B` where `C(A)` is the center of `A`.
- `Subalgebra.centralizer_range_includeRight_eq_center_tensorProduct`: if `A` is free as a module,
  then the centralizer of `1 ⊗ B` in `A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/

namespace Subalgebra

open Algebra.TensorProduct

section CommSemiring

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [Semiring A] [Algebra R A]

lemma le_centralizer_iff (S T : Subalgebra R A) : S ≤ centralizer R T ↔ T ≤ centralizer R S :=
  ⟨fun h t ht _ hs ↦ (h hs t ht).symm, fun h s hs _ ht ↦ (h ht s hs).symm⟩

lemma centralizer_coe_sup (S T : Subalgebra R A) :
    centralizer R ((S ⊔ T : Subalgebra R A) : Set A) = centralizer R S ⊓ centralizer R T :=
  eq_of_forall_le_iff fun K ↦ by
    simp_rw [le_centralizer_iff, sup_le_iff, le_inf_iff, K.le_centralizer_iff]

lemma centralizer_coe_iSup {ι : Sort*} (S : ι → Subalgebra R A) :
    centralizer R ((⨆ i, S i : Subalgebra R A) : Set A) = ⨅ i, centralizer R (S i) :=
  eq_of_forall_le_iff fun K ↦ by
    simp_rw [le_centralizer_iff, iSup_le_iff, le_iInf_iff, K.le_centralizer_iff]

end CommSemiring

section Free

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A]
variable (B : Type*) [Semiring B] [Algebra R B]

open Finsupp TensorProduct

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
For any subset `S ⊆ A`, the centralizer of `S ⊗ 1 ⊆ A ⊗ B` is `C_A(S) ⊗ B` where `C_A(S)` is the
centralizer of `S` in `A`.
-/
@[target]
lemma centralizer_coe_image_includeLeft_eq_center_tensorProduct
    (S : Set A) [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft (S := sorry
lemma centralizer_coe_image_includeRight_eq_center_tensorProduct
    (S : Set B) [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight '' S) =
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (Subalgebra.centralizer R (S : Set B)).val).range := by
  have eq1 := centralizer_coe_image_includeLeft_eq_center_tensorProduct R B A S
  apply_fun Subalgebra.comap (Algebra.TensorProduct.comm R A B).toAlgHom at eq1
  convert eq1
  · ext x
    simpa [mem_centralizer_iff] using
      ⟨fun h b hb ↦ (Algebra.TensorProduct.comm R A B).symm.injective <| by aesop, fun h b hb ↦
        (Algebra.TensorProduct.comm R A B).injective <| by aesop⟩
  · ext x
    simp only [AlgHom.mem_range, AlgEquiv.toAlgHom_eq_coe, mem_comap, AlgHom.coe_coe]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(Algebra.TensorProduct.comm R _ _) x,
        by rw [Algebra.TensorProduct.comm_comp_map_apply]⟩
    · rintro ⟨y, hy⟩
      refine ⟨(Algebra.TensorProduct.comm R _ _) y, (Algebra.TensorProduct.comm R A B).injective ?_⟩
      rw [← hy, comm_comp_map_apply, ← comm_symm, AlgEquiv.symm_apply_apply]

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `B` is free as `R`-module.
For any subalgebra `S` of `A`, the centralizer of `S ⊗ 1 ⊆ A ⊗ B` is `C_A(S) ⊗ B` where `C_A(S)` is
the centralizer of `S` in `A`.
-/
@[target]
lemma centralizer_coe_map_includeLeft_eq_center_tensorProduct
    (S : Subalgebra R A) [Module.Free R B] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeLeft (R := sorry
@[target]
lemma centralizer_coe_map_includeRight_eq_center_tensorProduct
    (S : Subalgebra R B) [Module.Free R A] :
    Subalgebra.centralizer R
      (S.map (Algebra.TensorProduct.includeRight (R := sorry
lemma centralizer_coe_range_includeLeft_eq_center_tensorProduct [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_univ, ← Algebra.coe_top (R := R) (A := A),
    ← centralizer_coe_map_includeLeft_eq_center_tensorProduct R A B ⊤]
  ext
  simp [includeLeft, includeLeftRingHom, Set.range_comp]

/--
Let `R` be a commutative ring and `A, B` be `R`-algebras where `A` is free as `R`-module.
Then the centralizer of `1 ⊗ B ⊆ A ⊗ B` is `A ⊗ C(B)` where `C(B)` is the center of `B`.
-/
@[target]
lemma centralizer_range_includeRight_eq_center_tensorProduct [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by sorry

lemma centralizer_tensorProduct_eq_center_tensorProduct_left [Module.Free R B] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (AlgHom.id R A) (Algebra.ofId R B)).range =
    (Algebra.TensorProduct.map (Subalgebra.center R A).val (AlgHom.id R B)).range := by
  rw [← centralizer_coe_range_includeLeft_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

lemma centralizer_tensorProduct_eq_center_tensorProduct_right [Module.Free R A] :
    Subalgebra.centralizer R
      (Algebra.TensorProduct.map (Algebra.ofId R A) (AlgHom.id R B)).range =
    (Algebra.TensorProduct.map (AlgHom.id R A) (center R B).val).range := by
  rw [← centralizer_range_includeRight_eq_center_tensorProduct]
  simp [Algebra.TensorProduct.map_range]

end Free

end Subalgebra
