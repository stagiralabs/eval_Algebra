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
@[simps!]
def engel (x : L) : LieSubalgebra R L :=
  { (ad R L x).maxGenEigenspace 0 with
    lie_mem' := by
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, Module.End.mem_maxGenEigenspace, zero_smul,
        sub_zero, forall_exists_index]
      intro y z m hm n hn
      refine ⟨m + n, ?_⟩
      rw [ad_pow_lie]
      apply Finset.sum_eq_zero
      intro ij hij
      obtain (h|h) : m ≤ ij.1 ∨ n ≤ ij.2 := by rw [Finset.mem_antidiagonal] at hij; omega
      all_goals simp [LinearMap.pow_map_zero_of_le h, hm, hn] }

@[target]
lemma mem_engel_iff (x y : L) :
    y ∈ engel R x ↔ ∃ n : ℕ, ((ad R L x) ^ n) y = 0 :=
  sorry

@[target]
lemma self_mem_engel (x : L) : x ∈ engel R x := by sorry

@[target, simp]
lemma engel_zero : engel R (0 : L) = ⊤ := by sorry
@[simp]
lemma normalizer_engel (x : L) : normalizer (engel R x) = engel R x := by
  apply le_antisymm _ (le_normalizer _)
  intro y hy
  rw [mem_normalizer_iff] at hy
  specialize hy x (self_mem_engel R x)
  rw [← lie_skew, neg_mem_iff (G := L), mem_engel_iff] at hy
  rcases hy with ⟨n, hn⟩
  rw [mem_engel_iff]
  use n+1
  rw [pow_succ, LinearMap.mul_apply]
  exact hn

variable {R}

open Filter in
/-- A Lie-subalgebra of an Artinian Lie algebra is self-normalizing
if it contains an Engel subalgebra.
See `LieSubalgebra.normalizer_engel` for a proof that Engel subalgebras are self-normalizing,
avoiding the Artinian condition. -/
@[target]
lemma normalizer_eq_self_of_engel_le [IsArtinian R L]
    (H : LieSubalgebra R L) (x : L) (h : engel R x ≤ H) :
    normalizer H = H := by sorry
@[target]
lemma isNilpotent_of_forall_le_engel [IsNoetherian R L]
    (H : LieSubalgebra R L) (h : ∀ x ∈ H, H ≤ engel R x) :
    LieRing.IsNilpotent H := by sorry

end LieSubalgebra
