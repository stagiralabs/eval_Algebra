import VerifiedAgora.tagger
/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell, Daniel Weber
-/
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Big operators on a list in ordered groups with zeros

This file contains the results concerning the interaction of list big operators with ordered
groups with zeros.
-/

namespace List
variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

@[target]
lemma prod_nonneg {s : List R} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by sorry


lemma one_le_prod {s : List R} (h : ∀ a ∈ s, 1 ≤ a) : 1 ≤ s.prod := by
  induction s with
  | nil => simp
  | cons head tail hind =>
    simp only [prod_cons]
    simp only [mem_cons, forall_eq_or_imp] at h
    exact one_le_mul_of_one_le_of_one_le h.1 (hind h.2)

@[target]
theorem prod_map_le_prod_map₀ {ι : Type*} {s : List ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by sorry
variable [PosMulStrictMono R] [NeZero (1 : R)]

@[target]
lemma prod_pos {s : List R} (h : ∀ a ∈ s, 0 < a) : 0 < s.prod := by sorry

@[target]
theorem prod_map_lt_prod_map {ι : Type*} {s : List ι} (hs : s ≠ [])
    (f : ι → R) (g : ι → R) (h0 : ∀ i ∈ s, 0 < f i) (h : ∀ i ∈ s, f i < g i) :
    (map f s).prod < (map g s).prod := by sorry

end List
