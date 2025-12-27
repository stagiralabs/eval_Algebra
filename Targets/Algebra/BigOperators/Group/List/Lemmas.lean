import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.ProdSigma
import Mathlib.Algebra.Group.Opposite

/-!
# Sums and products from lists

This file provides further results about `List.prod`, `List.sum`,
which calculate the product and sum of elements of a list
and `List.alternatingProd`, `List.alternatingSum`, their alternating counterparts.
-/
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

@[target, to_additive]
theorem prod_isUnit : ∀ {L : List M}, (∀ m ∈ L, IsUnit m) → IsUnit L.prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))

@[to_additive]
theorem prod_isUnit_iff {α : Type*} [CommMonoid α] {L : List α} :
    IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m := by sorry
@[to_additive "If elements of a list additively commute with each other, then their sum does not
depend on the order of elements."]
lemma Perm.prod_eq' (h : l₁ ~ l₂) (hc : l₁.Pairwise Commute) : l₁.prod = l₂.prod := by
  refine h.foldr_eq' ?_ _
  apply Pairwise.forall_of_forall
  · intro x y h z
    exact (h z).symm
  · intros; rfl
  · apply hc.imp
    intro a b h z
    rw [← mul_assoc, ← mul_assoc, h]

end Monoid

section Group

variable [Group G]

@[target]
lemma prod_rotate_eq_one_of_prod_eq_one :
    ∀ {l : List G} (_ : l.prod = 1) (n : ℕ), (l.rotate n).prod = 1
  | [], _, _ => by simp
  | a :: l, hl, n => by
    have : n % List.length (a :: l) ≤ List.length (a :: l) := sorry

end Group

variable [DecidableEq α]

/-- Summing the count of `x` over a list filtered by some `p` is just `countP` applied to `p` -/
@[target]
theorem sum_map_count_dedup_filter_eq_countP (p : α → Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countP p := by sorry

@[target]
theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by sorry

end List

namespace List

lemma length_sigma {σ : α → Type*} (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.sigma l₂) = (l₁.map fun a ↦ length (l₂ a)).sum := by
  induction' l₁ with x l₁ IH
  · rfl
  · simp only [sigma_cons, length_append, length_map, IH, map, sum_cons]

@[target]
lemma ranges_flatten : ∀ (l : List ℕ), l.ranges.flatten = range l.sum
  | [] => rfl
  | a :: l => by simp [ranges, ← map_flatten, ranges_flatten, range_add]

/-- The members of `l.ranges` have no duplicate -/
theorem ranges_nodup {l s : List ℕ} (hs : s ∈ ranges l) : s.Nodup :=
  sorry

@[deprecated (since := "2024-10-15")] alias ranges_join := ranges_flatten

/-- Any entry of any member of `l.ranges` is strictly smaller than `l.sum`. -/
lemma mem_mem_ranges_iff_lt_sum (l : List ℕ) {n : ℕ} :
    (∃ s ∈ l.ranges, n ∈ s) ↔ n < l.sum := by
  rw [← mem_range, ← ranges_flatten, mem_flatten]

/-- In a flatten of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lengths of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
@[target]
lemma drop_take_succ_flatten_eq_getElem (L : List (List α)) (i : Nat) (h : i < L.length) :
    (L.flatten.take ((L.map length).take (i + 1)).sum).drop ((L.map length).take i).sum = L[i] := by sorry

end List


namespace List

/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.prod = -1) : (-1 : ℤ) ∈ l := by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact Or.resolve_left
    (Int.isUnit_iff.mp (prod_isUnit_iff.mp
      (h.symm ▸ ⟨⟨-1, -1, by decide, by decide⟩, rfl⟩ : IsUnit l.prod) x h₁)) h₂ ▸ h₁

@[target]
theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.prod := by sorry

@[target]
theorem Sublist.prod_dvd_prod [CommMonoid M] {l₁ l₂ : List M} (h : l₁ <+ l₂) :
    l₁.prod ∣ l₂.prod := by sorry

section Alternating

variable [CommGroup α]

@[target, to_additive]
theorem alternatingProd_append :
    ∀ l₁ l₂ : List α,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternatingProd_cons, alternatingProd_append, length_cons, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]

@[to_additive]
theorem alternatingProd_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternatingProd_nil, one_zpow, reverse_nil]
  | a :: l => by
    simp_rw [reverse_cons, alternatingProd_append, alternatingProd_reverse,
      alternatingProd_singleton, alternatingProd_cons, length_reverse, length, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]

end Alternating

end List

open List

namespace MulOpposite
variable [Monoid M]

lemma op_list_prod : ∀ l : List M, op l.prod = (l.map op).reverse.prod := by sorry

@[target]
lemma unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop = (l.map unop).reverse.prod := by sorry

end MulOpposite

section MonoidHom
variable [Monoid M] [Monoid N]

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
lemma unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
    (f : F) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]

end MonoidHom
