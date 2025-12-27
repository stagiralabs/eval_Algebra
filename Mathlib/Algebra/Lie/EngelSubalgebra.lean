import VerifiedAgora.tagger
/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Engel subalgebras

This file defines Engel subalgebras of a Lie algebra and provides basic related properties.

The Engel subalgebra `LieSubalgebra.Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

## Main results

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent (TODO), hence Cartan subalgebras.

* `LieSubalgebra.normalizer_eq_self_of_engel_le`:
  Lie subalgebras containing an Engel subalgebra are self-normalizing,
  provided the ambient Lie algebra is Artinian.
* `LieSubalgebra.isNilpotent_of_forall_le_engel`:
  A Lie subalgebra of a Noetherian Lie algebra is nilpotent
  if it is contained in the Engel subalgebra of all its elements.
-/

open LieAlgebra LieModule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubalgebra

variable (R)

/-- The Engel subalgebra `Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent, hence Cartan subalgebras. -/
/-- The Engel subalgebra `Engel R x` consists of
all `y : L` such that `(ad R L x)^n` kills `y` for some `n`.

Engel subalgebras are self-normalizing (`LieSubalgebra.normalizer_engel`),
and minimal ones are nilpotent, hence Cartan subalgebras. -/
@[simps!]
def engel (x : L) : LieSubalgebra R L :=
  { (ad R L x).maxGenEigenspace 0 with
    lie_mem' := by
      sorry


@[target] lemma mem_engel_iff (x y : L) :
    y ∈ engel R x ↔ ∃ n : ℕ, ((ad R L x) ^ n) y = 0 :=
  (Module.End.mem_maxGenEigenspace _ _ _).trans <| by sorry


@[target] lemma self_mem_engel (x : L) : x ∈ engel R x := by
  sorry


@[target] lemma engel_zero : engel R (0 : L) = ⊤ := by
  sorry


/-- Engel subalgebras are self-normalizing.
See `LieSubalgebra.normalizer_eq_self_of_engel_le` for a proof that Lie-subalgebras
containing an Engel subalgebra are also self-normalizing,
provided that the ambient Lie algebra is artinina. -/
/-- Engel subalgebras are self-normalizing.
See `LieSubalgebra.normalizer_eq_self_of_engel_le` for a proof that Lie-subalgebras
containing an Engel subalgebra are also self-normalizing,
provided that the ambient Lie algebra is artinina. -/
@[target] lemma normalizer_engel (x : L) : normalizer (engel R x) = engel R x := by
  sorry


variable {R}

open Filter in
/-- A Lie-subalgebra of an Artinian Lie algebra is self-normalizing
if it contains an Engel subalgebra.
See `LieSubalgebra.normalizer_engel` for a proof that Engel subalgebras are self-normalizing,
avoiding the Artinian condition. -/
lemma normalizer_eq_self_of_engel_le [IsArtinian R L]
    (H : LieSubalgebra R L) (x : L) (h : engel R x ≤ H) :
    normalizer H = H := by
  set N := normalizer H
  apply le_antisymm _ (le_normalizer H)
  calc N.toSubmodule ≤ (engel R x).toSubmodule ⊔ H.toSubmodule := ?_
       _ = H := by rwa [sup_eq_right]
  have aux₁ : ∀ n ∈ N, ⁅x, n⁆ ∈ H := by
    intro n hn
    rw [mem_normalizer_iff] at hn
    specialize hn x (h (self_mem_engel R x))
    rwa [← lie_skew, neg_mem_iff (G := L)]
  have aux₂ : ∀ n ∈ N, ⁅x, n⁆ ∈ N := fun n hn ↦ le_normalizer H (aux₁ _ hn)
  let dx : N →ₗ[R] N := (ad R L x).restrict aux₂
  obtain ⟨k, hk⟩ : ∃ a, ∀ b ≥ a, Codisjoint (LinearMap.ker (dx ^ b)) (LinearMap.range (dx ^ b)) :=
    eventually_atTop.mp <| dx.eventually_codisjoint_ker_pow_range_pow
  specialize hk (k+1) (Nat.le_add_right k 1)
  rw [← Submodule.map_subtype_top N.toSubmodule, Submodule.map_le_iff_le_comap]
  apply hk
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_left
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    simp only [Submodule.mem_comap, mem_engel_iff, mem_toSubmodule]
    use k+1
    clear hk; revert hy
    generalize k+1 = k
    induction k generalizing y with
    | zero =>
      cases y; intro hy; simp only [pow_zero, LinearMap.one_apply]
      exact (AddSubmonoid.mk_eq_zero N.toAddSubmonoid).mp hy
    | succ k ih => simp only [pow_succ, LinearMap.mem_ker, LinearMap.mul_apply] at ih ⊢; apply ih
  · rw [← Submodule.map_le_iff_le_comap]
    apply le_sup_of_le_right
    rw [Submodule.map_le_iff_le_comap]
    rintro _ ⟨y, rfl⟩
    simp only [pow_succ', LinearMap.mul_apply, Submodule.mem_comap, mem_toSubmodule]
    apply aux₁
    simp only [Submodule.coe_subtype, SetLike.coe_mem]

/-- A Lie subalgebra of a Noetherian Lie algebra is nilpotent
if it is contained in the Engel subalgebra of all its elements. -/
/-- A Lie subalgebra of a Noetherian Lie algebra is nilpotent
if it is contained in the Engel subalgebra of all its elements. -/
@[target] lemma isNilpotent_of_forall_le_engel [IsNoetherian R L]
    (H : LieSubalgebra R L) (h : ∀ x ∈ H, H ≤ engel R x) :
    LieRing.IsNilpotent H := by
  sorry


end LieSubalgebra
