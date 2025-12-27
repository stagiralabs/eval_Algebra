import VerifiedAgora.tagger
/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Algebra.BigOperators.Finsupp

/-! # Connection between `Submonoid.closure` and `Finsupp.prod` -/

assert_not_exists Field

namespace Submonoid

variable {M : Type*} [CommMonoid M] {ι : Type*} (f : ι → M) (x : M)

@[target, to_additive]
theorem exists_finsupp_of_mem_closure_range (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι →₀ ℕ, x = a.prod (f · ^ ·) := by sorry

variable {f x} in
@[to_additive]
theorem mem_closure_range_iff :
    x ∈ closure (Set.range f) ↔ ∃ a : ι →₀ ℕ, x = a.prod (f · ^ ·) := by
  refine ⟨exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact prod_mem _ fun i hi ↦ pow_mem (subset_closure (Set.mem_range_self i)) _

@[to_additive]
theorem exists_of_mem_closure_range [Fintype ι] (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι → ℕ, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

variable {f x} in
@[target, to_additive]
theorem mem_closure_range_iff_of_fintype [Fintype ι] :
    x ∈ closure (Set.range f) ↔ ∃ a : ι → ℕ, x = ∏ i, f i ^ a i := by sorry

end Submonoid
