import VerifiedAgora.tagger
/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Normalizer

/-!
# Cartan subalgebras

Cartan subalgebras are one of the most important concepts in Lie theory. We define them here.
The standard example is the set of diagonal matrices in the Lie algebra of matrices.

## Main definitions

  * `LieSubmodule.IsUcsLimit`
  * `LieSubalgebra.IsCartanSubalgebra`
  * `LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit`

## Tags

lie subalgebra, normalizer, idealizer, cartan subalgebra
-/


universe u v w w₁ w₂

variable {R : Type u} {L : Type v}
variable [CommRing R] [LieRing L] [LieAlgebra R L] (H : LieSubalgebra R L)

/-- Given a Lie module `M` of a Lie algebra `L`, `LieSubmodule.IsUcsLimit` is the proposition
that a Lie submodule `N ⊆ M` is the limiting value for the upper central series.

This is a characteristic property of Cartan subalgebras with the roles of `L`, `M`, `N` played by
`H`, `L`, `H`, respectively. See `LieSubalgebra.isCartanSubalgebra_iff_isUcsLimit`. -/
def LieSubmodule.IsUcsLimit {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M]
    [LieModule R L M] (N : LieSubmodule R L M) : Prop :=
  ∃ k, ∀ l, k ≤ l → (⊥ : LieSubmodule R L M).ucs l = N

namespace LieSubalgebra

/-- A Cartan subalgebra is a nilpotent, self-normalizing subalgebra.

A _splitting_ Cartan subalgebra can be defined by mixing in `LieModule.IsTriangularizable R H L`. -/
class IsCartanSubalgebra : Prop where
  nilpotent : LieRing.IsNilpotent H
  self_normalizing : H.normalizer = H

instance [H.IsCartanSubalgebra] : LieRing.IsNilpotent H :=
  IsCartanSubalgebra.nilpotent

@[simp]
theorem normalizer_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H.toLieSubmodule.normalizer = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj, coe_normalizer_eq_normalizer,
    IsCartanSubalgebra.self_normalizing, coe_toLieSubmodule]

@[target, simp]
theorem ucs_eq_self_of_isCartanSubalgebra (H : LieSubalgebra R L) [H.IsCartanSubalgebra] (k : ℕ) :
    H.toLieSubmodule.ucs k = H.toLieSubmodule := by sorry

@[target]
theorem isCartanSubalgebra_iff_isUcsLimit : H.IsCartanSubalgebra ↔ H.toLieSubmodule.IsUcsLimit := by sorry

lemma ne_bot_of_isCartanSubalgebra [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    H ≠ ⊥ := by
  intro e
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  have : x ∈ H.normalizer := by simp [LieSubalgebra.mem_normalizer_iff, e]
  exact hx (by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing, e] at this)

instance (priority := 500) [Nontrivial L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    Nontrivial H := by
  refine (subsingleton_or_nontrivial H).elim (fun inst ↦ False.elim ?_) id
  apply ne_bot_of_isCartanSubalgebra H
  rw [eq_bot_iff]
  exact fun x hx ↦ congr_arg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : H) 0)

end LieSubalgebra

@[simp]
theorem LieIdeal.normalizer_eq_top {R : Type u} {L : Type v} [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) : (I : LieSubalgebra R L).normalizer = ⊤ := by
  ext x
  simpa only [LieSubalgebra.mem_normalizer_iff, LieSubalgebra.mem_top, iff_true] using
    fun y hy => I.lie_mem hy

open LieIdeal

/-- A nilpotent Lie algebra is its own Cartan subalgebra. -/
instance LieAlgebra.top_isCartanSubalgebra_of_nilpotent [LieRing.IsNilpotent L] :
    LieSubalgebra.IsCartanSubalgebra (⊤ : LieSubalgebra R L) where
  nilpotent := inferInstance
  self_normalizing := by rw [← top_toLieSubalgebra, normalizer_eq_top, top_toLieSubalgebra]
