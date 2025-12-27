import VerifiedAgora.tagger
/-
Copyright (c) 2024 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Big operators on a finset in the natural numbers

This file contains the results concerning the interaction of finset big operators with natural
numbers.
-/

variable {ι : Type*}

namespace Finset

@[target]
lemma even_sum_iff_even_card_odd {s : Finset ι} (f : ι → ℕ) :
    Even (∑ i ∈ s, f i) ↔ Even (s.filter fun x ↦ Odd (f x)).card := by sorry

lemma odd_sum_iff_odd_card_odd {s : Finset ι} (f : ι → ℕ) :
    Odd (∑ i ∈ s, f i) ↔ Odd (s.filter fun x ↦ Odd (f x)).card := by
  simp only [← Nat.not_even_iff_odd, even_sum_iff_even_card_odd]

end Finset
