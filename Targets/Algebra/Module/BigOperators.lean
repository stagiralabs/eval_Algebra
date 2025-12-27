import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov, Yaël Dillies
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite sums over modules over a ring
-/

variable {ι κ α β R M : Type*}

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

@[target]
theorem List.sum_smul {l : List R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum :=
  sorry

theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.sum • x = (l.map fun r ↦ r • x).sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l

@[target]
theorem Multiset.sum_smul_sum {s : Multiset R} {t : Multiset M} :
    s.sum • t.sum = ((s ×ˢ t).map fun p : R × M ↦ p.fst • p.snd).sum := by sorry

theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} :
    (∑ i ∈ s, f i) • x = ∑ i ∈ s, f i • x := map_sum ((smulAddHom R M).flip x) f s

lemma Finset.sum_smul_sum (s : Finset α) (t : Finset β) {f : α → R} {g : β → M} :
    (∑ i ∈ s, f i) • ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i • g j := by
  simp_rw [sum_smul, ← smul_sum]

@[target]
lemma Fintype.sum_smul_sum [Fintype α] [Fintype β] (f : α → R) (g : β → M) :
    (∑ i, f i) • ∑ j, g j = ∑ i, ∑ j, f i • g j := sorry

end AddCommMonoid

open Finset

@[target]
theorem Finset.cast_card [CommSemiring R] (s : Finset α) : (#s : R) = ∑ _ ∈ s, 1 := by sorry

namespace Fintype
variable [DecidableEq ι] [Fintype ι] [AddCommMonoid α]

@[target]
lemma sum_piFinset_apply (f : κ → α) (s : Finset κ) (i : ι) :
    ∑ g ∈ piFinset fun _ : ι ↦ s, f (g i) = #s ^ (card ι - 1) • ∑ b ∈ s, f b := by sorry

end Fintype
