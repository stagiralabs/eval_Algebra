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

@[target]
lemma sum_indicator_eventually_eq_card {α : Type*} [AddCommMonoid α] (a : α) {s : Set ℕ}
    (hs : s.Finite) :
    ∀ᶠ n in atTop, ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ a) k = (Nat.card s) • a := by sorry

@[target]
lemma infinite_iff_tendsto_sum_indicator_atTop {R : Type*} [OrderedAddCommMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) {s : Set ℕ} :
    s.Infinite ↔ atTop.Tendsto (fun n ↦ ∑ k ∈ Finset.range n, s.indicator (fun _ ↦ r) k) atTop := by sorry

lemma limsup_eq_tendsto_sum_indicator_atTop {α R : Type*} [OrderedAddCommMonoid R]
    [AddLeftStrictMono R] [Archimedean R] {r : R} (h : 0 < r) (s : ℕ → Set α) :
    atTop.limsup s = { ω | atTop.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, (s k).indicator (fun _ ↦ r) ω) atTop } := by
  nth_rw 1 [← Nat.cofinite_eq_atTop, cofinite.limsup_set_eq]
  ext ω
  rw [mem_setOf_eq, mem_setOf_eq, infinite_iff_tendsto_sum_indicator_atTop h, iff_eq_eq]
  congr

end Set
