import VerifiedAgora.tagger
/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Module.Torsion
import Mathlib.RingTheory.DedekindDomain.Ideal

/-!
# Modules over a Dedekind domain

Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-torsion
submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.
Therefore, as any finitely generated torsion module is `I`-torsion for some `I`, it is an internal
direct sum of its `p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/


universe u v

variable {R : Type u} [CommRing R] [IsDomain R] {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

namespace Submodule

variable [IsDedekindDomain R]

open UniqueFactorizationMonoid

/-- Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-
torsion submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals. -/
@[target]
theorem isInternal_prime_power_torsion_of_is_torsion_by_ideal [DecidableEq (Ideal R)]
    {I : Ideal R} (hI : I ≠ ⊥) (hM : Module.IsTorsionBySet R M I) :
    DirectSum.IsInternal fun p : (factors I).toFinset =>
      torsionBySet R M (p ^ (factors I).count ↑p : Ideal R) := by sorry
theorem isInternal_prime_power_torsion [DecidableEq (Ideal R)] [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBySet R M (p ^ (factors (⊤ : Submodule R M).annihilator).count ↑p : Ideal R) := by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [← Set.nonempty_iff_ne_empty] at hI; rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`. -/
@[target]
theorem exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsionBySet R M (p ^ e p : Ideal R) := by sorry

end Submodule
