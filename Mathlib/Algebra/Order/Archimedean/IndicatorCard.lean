import VerifiedAgora.tagger
/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Order.LiminfLimsup
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality and limit of sum of indicators
This file contains results relating the cardinality of subsets of ℕ and limits,
limsups of sums of indicators.

## Tags
finite, indicator, limsup, tendsto
-/

namespace Set

open Filter Finset

@[target] lemma sum_indicator_eventually_eq_card {α : Type*} [AddCommMonoid α] (a : α) {s : Set ℕ}
    (hs : s.Finite) :
    ∀ᶠ n in atTop, ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ a) k = (Nat.card s) • a := by
  sorry


lemma infinite_iff_tendsto_sum_indicator_atTop {R : Type*} [OrderedAddCommMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) {s : Set ℕ} :
    s.Infinite ↔ atTop.Tendsto (fun n ↦ ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ r) k) atTop := by
  constructor
  · have h_mono : Monotone fun n ↦ ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ r) k := by
      refine (sum_mono_set_of_nonneg ?_).comp range_mono
      exact (fun _ ↦ indicator_nonneg (fun _ _ ↦ h.le) _)
    rw [h_mono.tendsto_atTop_atTop_iff]
    intro hs n
    obtain ⟨n', hn'⟩ := exists_lt_nsmul h n
    obtain ⟨t, t_s, t_card⟩ := hs.exists_subset_card_eq n'
    obtain ⟨m, hm⟩ := t.bddAbove
    refine ⟨m + 1, hn'.le.trans ?_⟩
    apply (sum_le_sum fun i _ ↦ (indicator_le_indicator_of_subset t_s (fun _ ↦ h.le)) i).trans_eq'
    have h : t ⊆ Finset.range (m + 1) := by
      intro i i_t
      rw [Finset.mem_range]
      exact (hm i_t).trans_lt (lt_add_one m)
    rw [sum_indicator_subset (fun _ ↦ r) h, sum_eq_card_nsmul (fun _ _ ↦ rfl), t_card]
  · contrapose
    intro hs
    rw [not_infinite] at hs
    rw [tendsto_congr' (sum_indicator_eventually_eq_card r hs), tendsto_atTop_atTop]
    push_neg
    obtain ⟨m, hm⟩ := exists_lt_nsmul h (Nat.card s • r)
    exact ⟨m • r, fun n ↦ ⟨n, le_refl n, not_le_of_lt hm⟩⟩

@[target] lemma limsup_eq_tendsto_sum_indicator_atTop {α R : Type*} [OrderedAddCommMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) (s : ℕ → Set α) :
    atTop.limsup s = { ω | atTop.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, (s k).indicator (fun _ ↦ r) ω) atTop } := by
  sorry


end Set
