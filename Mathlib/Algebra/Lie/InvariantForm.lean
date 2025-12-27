import VerifiedAgora.tagger
/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Lie algebras with non-degenerate invariant bilinear forms are semisimple

In this file we prove that a finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it invariant under the Lie bracket
in the sense that `⁅x, Φ⁆ = 0` for all `x` or equivalently, `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.

## Main results

* `LieAlgebra.InvariantForm.orthogonal`: given a Lie submodule `N` of a Lie module `M`,
  we define its orthogonal complement with respect to a non-degenerate invariant bilinear form `Φ`
  as the Lie ideal of elements `x` such that `Φ n x = 0` for all `n ∈ N`.
* `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate`: the main result of this file;
  a finite-dimensional Lie algebra over a field is semisimple
  if it does not have non-trivial abelian ideals and admits
  a non-degenerate invariant reflexive bilinear form.

## References

We follow the short and excellent paper [dieudonne1953].
-/

namespace LieAlgebra

namespace InvariantForm

section ring

variable {R L M : Type*}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (L) in
/--
A bilinear form on a Lie module `M` of a Lie algebra `L` is *invariant* if
for all `x : L` and `y z : M` the condition `Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆` holds.
-/
def _root_.LinearMap.BilinForm.lieInvariant : Prop :=
  ∀ (x : L) (y z : M), Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆

lemma _root_.LinearMap.BilinForm.lieInvariant_iff [LieAlgebra R L] [LieModule R L M] :
    Φ.lieInvariant L ↔ Φ ∈ LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M) := by
  refine ⟨fun h x ↦ ?_, fun h x y z ↦ ?_⟩
  · ext y z
    rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, h, sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]

/--
The orthogonal complement of a Lie submodule `N` with respect to an invariant bilinear form `Φ` is
the Lie submodule of elements `y` such that `Φ x y = 0` for all `x ∈ N`.
-/
/--
The orthogonal complement of a Lie submodule `N` with respect to an invariant bilinear form `Φ` is
the Lie submodule of elements `y` such that `Φ x y = 0` for all `x ∈ N`.
-/
@[simps!]
def orthogonal (hΦ_inv : Φ.lieInvariant L) (N : LieSubmodule R L M) : LieSubmodule R L M where
  __ := Φ.orthogonal N
  lie_mem {x y} := by
    sorry


variable (hΦ_inv : Φ.lieInvariant L)

@[target] lemma orthogonal_toSubmodule (N : LieSubmodule R L M) :
    (orthogonal Φ hΦ_inv N).toSubmodule = Φ.orthogonal N.toSubmodule := by sorry


@[target] lemma mem_orthogonal (N : LieSubmodule R L M) (y : M) :
    y ∈ orthogonal Φ hΦ_inv N ↔ ∀ x ∈ N, Φ x y = 0 := by
  sorry


variable [LieAlgebra R L]

@[target] lemma orthogonal_disjoint
    (Φ : LinearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L)
    -- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
    (hL : ∀ I : LieIdeal R L, IsAtom I → ¬IsLieAbelian I)
    (I : LieIdeal R L) (hI : IsAtom I) :
    Disjoint I (orthogonal Φ hΦ_inv I) := by
  sorry


end ring

section field

variable {K L M : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)
variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)
-- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)
include hΦ_nondeg hΦ_refl hL

open Module Submodule in
open Module Submodule in
@[target] lemma orthogonal_isCompl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I.toSubmodule (orthogonal Φ hΦ_inv I).toSubmodule := by
  sorry


@[deprecated (since := "2024-12-30")]
alias orthogonal_isCompl_coe_submodule := orthogonal_isCompl_toSubmodule

open Module Submodule in
open Module Submodule in
@[target] lemma orthogonal_isCompl (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I (orthogonal Φ hΦ_inv I) := by
  sorry


@[target] lemma restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict I).Nondegenerate := by
  sorry


lemma restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict (orthogonal Φ hΦ_inv I)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, orthogonal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

open Module Submodule in
open Module Submodule in
@[target] lemma atomistic : ∀ I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J ≤ I} = I := by
  sorry


open LieSubmodule in
/--
A finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is compatible with the Lie bracket: `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.
-/
open LieSubmodule in
/--
A finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is compatible with the Lie bracket: `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.
-/
@[target] theorem isSemisimple_of_nondegenerate : IsSemisimple K L := by
  sorry


end field

end InvariantForm

end LieAlgebra
