import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Piecewise
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Prod

/-!
# Big operators

In this file we prove theorems about products and sums indexed by a `Finset`.

-/

-- TODO
-- assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction OrderedCommMonoid
assert_not_exists Finset.preimage Finset.sigma Fintype.piFinset

variable {ι κ α β γ : Type*}

open Fin Function

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

@[target, to_additive]
theorem prod_eq_fold [CommMonoid β] (s : Finset α) (f : α → β) :
    ∏ x ∈ s, f x = s.fold ((· * ·) : β → β → β) 1 f :=
  sorry

end Finset

@[to_additive]
theorem MonoidHom.coe_finset_prod [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α) :
    ⇑(∏ x ∈ s, f x) = ∏ x ∈ s, ⇑(f x) :=
  map_prod (MonoidHom.coeFn β γ) _ _

/-- See also `Finset.prod_apply`, with the same conclusion but with the weaker hypothesis
`f : α → β → γ` -/
@[to_additive (attr := simp)
  "See also `Finset.sum_apply`, with the same conclusion but with the weaker hypothesis
  `f : α → β → γ`"]
@[target]
theorem MonoidHom.finset_prod_apply [MulOneClass β] [CommMonoid γ] (f : α → β →* γ) (s : Finset α)
    (b : β) : (∏ x ∈ s, f x) b = ∏ x ∈ s, f x b :=
  sorry

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry
@[to_additive (attr := simp) "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`."]
@[target]
theorem prod_insert_of_eq_one_if_not_mem [DecidableEq α] (h : a ∉ s → f a = 1) :
    ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by sorry
@[to_additive (attr := simp) "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`."]
@[target]
theorem prod_insert_one [DecidableEq α] (h : f a = 1) : ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x :=
  sorry

@[target, to_additive]
theorem prod_insert_div {M : Type*} [CommGroup M] [DecidableEq α] (ha : a ∉ s) {f : α → M} :
    (∏ x ∈ insert a s, f x) / f a = ∏ x ∈ s, f x := by sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem prod_pair [DecidableEq α] {a b : α} (h : a ≠ b) :
    (∏ x ∈ ({a, b} : Finset α), f x) = f a * f b := by sorry

@[to_additive (attr := simp)]
theorem prod_image [DecidableEq α] {s : Finset γ} {g : γ → α} :
    (∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x) :=
  fold_image

@[to_additive]
lemma prod_attach (s : Finset α) (f : α → β) : ∏ x ∈ s.attach, f x = ∏ x ∈ s, f x := by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[target, to_additive (attr := by sorry

@[target, to_additive]
theorem prod_eq_one {f : α → β} {s : Finset α} (h : ∀ x ∈ s, f x = 1) : ∏ x ∈ s, f x = 1 :=
  sorry

@[target, to_additive]
theorem prod_disjUnion (h) :
    ∏ x ∈ s₁.disjUnion s₂ h, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by sorry

@[target, to_additive]
theorem prod_disjiUnion (s : Finset ι) (t : ι → Finset α) (h) :
    ∏ x ∈ s.disjiUnion t h, f x = ∏ i ∈ s, ∏ x ∈ t i, f x := by sorry

@[to_additive]
theorem prod_union_inter [DecidableEq α] :
    (∏ x ∈ s₁ ∪ s₂, f x) * ∏ x ∈ s₁ ∩ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x :=
  fold_union_inter

@[to_additive]
theorem prod_union [DecidableEq α] (h : Disjoint s₁ s₂) :
    ∏ x ∈ s₁ ∪ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]
theorem prod_filter_mul_prod_filter_not
    (s : Finset α) (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] (f : α → β) :
    (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, f x = ∏ x ∈ s, f x := by
  have := Classical.decEq α
  rw [← prod_union (disjoint_filter_filter_neg s s p), filter_union_filter_neg_eq]

@[to_additive]
lemma prod_filter_not_mul_prod_filter (s : Finset α) (p : α → Prop) [DecidablePred p]
    [∀ x, Decidable (¬p x)] (f : α → β) :
    (∏ x ∈ s.filter fun x ↦ ¬p x, f x) * ∏ x ∈ s.filter p, f x = ∏ x ∈ s, f x := by
  rw [mul_comm, prod_filter_mul_prod_filter_not]

@[to_additive]
theorem prod_filter_xor (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (∏ x ∈ s with (Xor' (p x) (q x)), f x) =
      (∏ x ∈ s with (p x ∧ ¬ q x), f x) * (∏ x ∈ s with (q x ∧ ¬ p x), f x) := by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor']

end CommMonoid

end Finset

section

open Finset

variable [Fintype α] [CommMonoid β]

@[target, to_additive]
theorem IsCompl.prod_mul_prod {s t : Finset α} (h : IsCompl s t) (f : α → β) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i, f i :=
  sorry

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. "]
theorem prod_mul_prod_compl [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
theorem prod_compl_mul_prod [Fintype α] [DecidableEq α] (s : Finset α) (f : α → β) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f

@[target, to_additive]
theorem prod_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) :
    (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x := by sorry

@[to_additive]
theorem prod_subset_one_on_sdiff [DecidableEq α] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i ∈ s₁, f i = ∏ i ∈ s₂, g i := by
  rw [← prod_sdiff h, prod_eq_one hg, one_mul]
  exact prod_congr rfl hfg

@[to_additive]
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x :=
  haveI := Classical.decEq α
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]
theorem prod_disj_sum (s : Finset α) (t : Finset γ) (f : α ⊕ γ → β) :
    ∏ x ∈ s.disjSum t, f x = (∏ x ∈ s, f (Sum.inl x)) * ∏ x ∈ t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr, prod_disjUnion, prod_map, prod_map]
  rfl

@[target, to_additive]
lemma prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (α ⊕ γ)) (f : α ⊕ γ → β) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by sorry

@[target, to_additive]
theorem prod_sumElim (s : Finset α) (t : Finset γ) (f : α → β) (g : γ → β) :
    ∏ x ∈ s.disjSum t, Sum.elim f g x = (∏ x ∈ s, f x) * ∏ x ∈ t, g x := by sorry

@[deprecated (since := "2025-02-20")] alias prod_sum_elim := prod_sumElim
@[deprecated (since := "2025-02-20")] alias sum_sum_elim := sum_sumElim

@[target, to_additive]
theorem prod_biUnion [DecidableEq α] {s : Finset γ} {t : γ → Finset α}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by sorry

section bij
variable {ι κ α : Type*} [CommMonoid α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α}

@[to_additive]
lemma prod_of_injOn (e : ι → κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
    (h' : ∀ i ∈ t, i ∉ e '' s → g i = 1) (h : ∀ i ∈ s, f i = g (e i))  :
    ∏ i ∈ s, f i = ∏ j ∈ t, g j := by
  classical
  exact (prod_nbij e (fun a ↦ mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans <|
    prod_subset (image_subset_iff.2 hest) <| by simpa using h'

variable [DecidableEq κ]

@[to_additive]
lemma prod_fiberwise_eq_prod_filter (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s with g i ∈ t, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq]

@[target, to_additive]
lemma prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : κ → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s with g i ∈ t, f (g i) := by sorry

@[to_additive]
lemma prod_fiberwise_of_maps_to {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : ι → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq_of_maps_to h]

@[target, to_additive]
lemma prod_fiberwise_of_maps_to' {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : κ → α) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) := by sorry

variable [Fintype κ]

@[to_additive]
lemma prod_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → α) :
    ∏ j, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i :=
  prod_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _

@[to_additive]
lemma prod_fiberwise' (s : Finset ι) (g : ι → κ) (f : κ → α) :
    ∏ j, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) :=
  prod_fiberwise_of_maps_to' (fun _ _ ↦ mem_univ _) _

end bij

@[to_additive (attr := simp)]
lemma prod_diag [DecidableEq α] (s : Finset α) (f : α × α → β) :
    ∏ i ∈ s.diag, f i = ∏ i ∈ s, f (i, i) := by
  apply prod_nbij' Prod.fst (fun i ↦ (i, i)) <;> simp

@[target, to_additive]
theorem prod_image' [DecidableEq α] {s : Finset ι} {g : ι → α} (h : ι → β)
    (eq : ∀ i ∈ s, f (g i) = ∏ j ∈ s with g j = g i, h j) :
    ∏ a ∈ s.image g, f a = ∏ i ∈ s, h i :=
  sorry

@[target, to_additive]
theorem prod_mul_distrib : ∏ x ∈ s, f x * g x = (∏ x ∈ s, f x) * ∏ x ∈ s, g x :=
  sorry

@[to_additive]
lemma prod_mul_prod_comm (f g h i : α → β) :
    (∏ a ∈ s, f a * g a) * ∏ a ∈ s, h a * i a = (∏ a ∈ s, f a * h a) * ∏ a ∈ s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[target, to_additive]
theorem prod_filter_of_ne {p : α → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x :=
  sorry

-- If we use `[DecidableEq β]` here, some rewrites fail because they find a wrong `Decidable`
-- instance first; `{∀ x, Decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
theorem prod_filter_ne_one (s : Finset α) [∀ x, Decidable (f x ≠ 1)] :
    ∏ x ∈ s with f x ≠ 1, f x = ∏ x ∈ s, f x :=
  prod_filter_of_ne fun _ _ => id

@[target, to_additive]
theorem prod_filter (p : α → Prop) [DecidablePred p] (f : α → β) :
    ∏ a ∈ s with p a, f a = ∏ a ∈ s, if p a then f a else 1 :=
  sorry

@[target, to_additive]
theorem prod_eq_single_of_mem {s : Finset α} {f : α → β} (a : α) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : ∏ x ∈ s, f x = f a := by sorry

@[target, to_additive]
theorem prod_eq_single {s : Finset α} {f : α → β} (a : α) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1)
    (h₁ : a ∉ s → f a = 1) : ∏ x ∈ s, f x = f a :=
  sorry

@[target, to_additive]
lemma prod_union_eq_left [DecidableEq α] (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₁, f a :=
  sorry

@[target, to_additive]
lemma prod_union_eq_right [DecidableEq α] (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₂, f a := by sorry

@[to_additive]
theorem prod_eq_mul_of_mem {s : Finset α} {f : α → β} (a b : α) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq α; let s' := ({a, b} : Finset α)
  have hu : s' ⊆ s := by
    refine insert_subset_iff.mpr ?_
    apply And.intro ha
    apply singleton_subset_iff.mpr hb
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by
    intro c hc hcs
    apply h₀ c hc
    apply not_or.mp
    intro hab
    apply hcs
    rw [mem_insert, mem_singleton]
    exact hab
  rw [← prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
theorem prod_eq_mul {s : Finset α} {f : α → β} (a b : α) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    ∏ x ∈ s, f x = f a * f b := by
  haveI := Classical.decEq α; by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      _root_.trans
        (prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one

/-- A product over `s.subtype p` equals one over `{x ∈ s | p x}`. -/
@[to_additive (attr := simp)
"A sum over `s.subtype p` equals one over `{x ∈ s | p x}`."]
@[target]
theorem prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [DecidablePred p] :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s with p x, f x := by sorry
@[to_additive "If all elements of a `Finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`."]
@[target]
theorem prod_subtype_of_mem (f : α → β) {p : α → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s, f x := by sorry
@[to_additive "A sum of a function over a `Finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `Finset`."]
theorem prod_subtype_map_embedding {p : α → Prop} {s : Finset { x // p x }} {f : { x // p x } → β}
    {g : α → β} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x ∈ s.map (Function.Embedding.subtype _), g x) = ∏ x ∈ s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
theorem prod_coe_sort : ∏ i : s, f i = ∏ i ∈ s, f i := prod_attach _ _

@[target, to_additive]
theorem prod_finset_coe (f : α → β) (s : Finset α) : (∏ i : (s : Set α), f i) = ∏ i ∈ s, f i :=
  sorry

variable {f s}

@[to_additive]
theorem prod_subtype {p : α → Prop} {F : Fintype (Subtype p)} (s : Finset α) (h : ∀ x, x ∈ s ↔ p x)
    (f : α → β) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  have : (· ∈ s) = p := Set.ext h
  subst p
  rw [← prod_coe_sort]
  congr!

@[to_additive]
theorem prod_set_coe (s : Set α) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i :=
(Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive "The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`."]
@[target]
theorem prod_congr_set {α : Type*} [CommMonoid α] {β : Type*} [Fintype β] (s : Set β)
    [DecidablePred (· ∈ s)] (f : β → α) (g : s → α) (w : ∀ (x : β) (h : x ∈ s), f x = g ⟨x, h⟩)
    (w' : ∀ x : β, x ∉ s → f x = 1) : Finset.univ.prod f = Finset.univ.prod g := by sorry

@[target, to_additive]
theorem prod_apply_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p}
    [DecidablePred fun x => ¬p x] (f : ∀ x : α, p x → γ) (g : ∀ x : α, ¬p x → γ) (h : γ → β) :
    (∏ x ∈ s, h (if hx : p x then f x hx else g x hx)) =
      (∏ x : {x ∈ s | p x}, h (f x.1 <| by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, h (g x.1 <| by simpa using (mem_filter.mp x.2).2) :=
  sorry

@[target, to_additive]
theorem prod_apply_ite {s : Finset α} {p : α → Prop} {_hp : DecidablePred p} (f g : α → γ)
    (h : γ → β) :
    (∏ x ∈ s, h (if p x then f x else g x)) =
      (∏ x ∈ s with p x, h (f x)) * ∏ x ∈ s with ¬p x, h (g x) :=
  sorry

@[to_additive]
theorem prod_dite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f : ∀ x : α, p x → β)
    (g : ∀ x : α, ¬p x → β) :
    ∏ x ∈ s, (if hx : p x then f x hx else g x hx) =
      (∏ x : {x ∈ s | p x}, f x.1 (by simpa using (mem_filter.mp x.2).2)) *
        ∏ x : {x ∈ s | ¬p x}, g x.1 (by simpa using (mem_filter.mp x.2).2) := by
  simp [prod_apply_dite _ _ fun x => x]

@[to_additive]
theorem prod_ite {s : Finset α} {p : α → Prop} {hp : DecidablePred p} (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  simp [prod_apply_ite _ _ fun x => x]

@[to_additive]
lemma prod_dite_of_false {p : α → Prop} {_ : DecidablePred p} (h : ∀ i ∈ s, ¬ p i)
    (f : ∀ i, p i → β) (g : ∀ i, ¬ p i → β) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, g i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> aesop

@[target, to_additive]
lemma prod_ite_of_false {p : α → Prop} {_ : DecidablePred p} (h : ∀ x ∈ s, ¬p x) (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, g x :=
  sorry

@[target, to_additive]
lemma prod_dite_of_true {p : α → Prop} {_ : DecidablePred p} (h : ∀ i ∈ s, p i) (f : ∀ i, p i → β)
    (g : ∀ i, ¬ p i → β) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2) := by sorry

@[target, to_additive]
lemma prod_ite_of_true {p : α → Prop} {_ : DecidablePred p} (h : ∀ x ∈ s, p x) (f g : α → β) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, f x :=
  sorry

@[target, to_additive]
theorem prod_apply_ite_of_false {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by sorry

@[target, to_additive]
theorem prod_apply_ite_of_true {p : α → Prop} {hp : DecidablePred p} (f g : α → γ) (k : γ → β)
    (h : ∀ x ∈ s, p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (f x) := by sorry

@[target, to_additive]
theorem prod_extend_by_one [DecidableEq α] (s : Finset α) (f : α → β) :
    ∏ i ∈ s, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i :=
  sorry

@[to_additive (attr := simp)]
theorem prod_ite_mem [DecidableEq α] (s t : Finset α) (f : α → β) :
    ∏ i ∈ s, (if i ∈ t then f i else 1) = ∏ i ∈ s ∩ t, f i := by
  rw [← Finset.prod_filter, Finset.filter_mem_eq_inter]

@[target, to_additive]
lemma prod_attach_eq_prod_dite [Fintype α] (s : Finset α) (f : s → β) [DecidablePred (· ∈ s)] :
    ∏ i ∈ s.attach, f i = ∏ i, if h : i ∈ s then f ⟨i, h⟩ else 1 := by sorry

@[to_additive (attr := simp)]
theorem prod_dite_eq [DecidableEq α] (s : Finset α) (a : α) (b : ∀ x : α, a = x → β) :
    ∏ x ∈ s, (if h : a = x then b x h else 1) = ite (a ∈ s) (b a rfl) 1 := by
  split_ifs with h
  · rw [Finset.prod_eq_single a, dif_pos rfl]
    · intros _ _ h
      rw [dif_neg]
      exact h.symm
    · simp [h]
  · rw [Finset.prod_eq_one]
    intros
    rw [dif_neg]
    rintro rfl
    contradiction

@[target, to_additive (attr := by sorry

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x ∈ s, ite (a = x) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq s a fun x _ => b x

/-- A product taken over a conditional whose condition is an equality test on the index and whose
alternative is `1` has value either the term at that index or `1`.

The difference with `Finset.prod_ite_eq` is that the arguments to `Eq` are swapped. -/
@[to_additive (attr := simp) "A sum taken over a conditional whose condition is an equality
test on the index and whose alternative is `0` has value either the term at that index or `0`.

The difference with `Finset.sum_ite_eq` is that the arguments to `Eq` are swapped."]
theorem prod_ite_eq' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) :
    (∏ x ∈ s, ite (x = a) (b x) 1) = ite (a ∈ s) (b a) 1 :=
  prod_dite_eq' s a fun x _ => b x

@[to_additive]
theorem prod_ite_eq_of_mem [DecidableEq α] (s : Finset α) (a : α) (b : α → β) (h : a ∈ s) :
    (∏ x ∈ s, if a = x then b x else 1) = b a := by
  simp only [prod_ite_eq, if_pos h]

/-- The difference with `Finset.prod_ite_eq_of_mem` is that the arguments to `Eq` are swapped. -/
@[to_additive]
theorem prod_ite_eq_of_mem' [DecidableEq α] (s : Finset α) (a : α) (b : α → β) (h : a ∈ s) :
    (∏ x ∈ s, if x = a then b x else 1) = b a := by
  simp only [prod_ite_eq', if_pos h]

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle' [DecidableEq α] (a : α) (x : β) (s : Finset α) :
    ∏ a' ∈ s, Pi.mulSingle a x a' = if a ∈ s then x else 1 :=
  prod_dite_eq' _ _ _

@[to_additive (attr := simp)]
theorem prod_pi_mulSingle {β : α → Type*} [DecidableEq α] [∀ a, CommMonoid (β a)] (a : α)
    (f : ∀ a, β a) (s : Finset α) :
    (∏ a' ∈ s, Pi.mulSingle a' (f a') a) = if a ∈ s then f a else 1 :=
  prod_dite_eq _ _ _

@[to_additive]
lemma mulSupport_prod (s : Finset ι) (f : ι → α → β) :
    mulSupport (fun x ↦ ∏ i ∈ s, f i x) ⊆ ⋃ i ∈ s, mulSupport (f i) := by
  simp only [mulSupport_subset_iff', Set.mem_iUnion, not_exists, nmem_mulSupport]
  exact fun x ↦ prod_eq_one

section indicator
open Set
variable {κ : Type*}

/-- Consider a product of `g i (f i)` over a finset.  Suppose `g` is a function such as
`n ↦ (· ^ n)`, which maps a second argument of `1` to `1`. Then if `f` is replaced by the
corresponding multiplicative indicator function, the finset may be replaced by a possibly larger
finset without changing the value of the product. -/
@[to_additive "Consider a sum of `g i (f i)` over a finset.  Suppose `g` is a function such as
`n ↦ (n • ·)`, which maps a second argument of `0` to `0` (or a weighted sum of `f i * h i` or
`f i • h i`, where `f` gives the weights that are multiplied by some other function `h`). Then if
`f` is replaced by the corresponding indicator function, the finset may be replaced by a possibly
larger finset without changing the value of the sum."]
@[target]
lemma prod_mulIndicator_subset_of_eq_one [One α] (f : ι → α) (g : ι → α → β) {s t : Finset ι}
    (h : s ⊆ t) (hg : ∀ a, g a 1 = 1) :
    ∏ i ∈ t, g i (mulIndicator ↑s f i) = ∏ i ∈ s, g i (f i) := by sorry
@[to_additive "Summing an indicator function over a possibly larger `Finset` is the same as summing
  the original function over the original finset."]
@[target]
lemma prod_mulIndicator_subset (f : ι → β) {s t : Finset ι} (h : s ⊆ t) :
    ∏ i ∈ t, mulIndicator (↑s) f i = ∏ i ∈ s, f i :=
  sorry

@[target, to_additive]
lemma prod_mulIndicator_eq_prod_filter (s : Finset ι) (f : ι → κ → β) (t : ι → Set κ) (g : ι → κ)
    [DecidablePred fun i ↦ g i ∈ t i] :
    ∏ i ∈ s, mulIndicator (t i) (f i) (g i) = ∏ i ∈ s with g i ∈ t i, f i (g i) := by sorry

@[to_additive]
lemma prod_mulIndicator_eq_prod_inter [DecidableEq ι] (s t : Finset ι) (f : ι → β) :
    ∏ i ∈ s, (t : Set ι).mulIndicator f i = ∏ i ∈ s ∩ t, f i := by
  rw [← filter_mem_eq_inter, prod_mulIndicator_eq_prod_filter]; rfl

@[target, to_additive]
lemma mulIndicator_prod (s : Finset ι) (t : Set κ) (f : ι → κ → β) :
    mulIndicator t (∏ i ∈ s, f i) = ∏ i ∈ s, mulIndicator t (f i) :=
  sorry

variable {κ : Type*}
@[target, to_additive]
lemma mulIndicator_biUnion (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (hs : (s : Set ι).PairwiseDisjoint t) :
    mulIndicator (⋃ i ∈ s, t i) f = fun a ↦ ∏ i ∈ s, mulIndicator (t i) f a := by sorry

@[target, to_additive]
lemma mulIndicator_biUnion_apply (s : Finset ι) (t : ι → Set κ) {f : κ → β}
    (h : (s : Set ι).PairwiseDisjoint t) (x : κ) :
    mulIndicator (⋃ i ∈ s, t i) f x = ∏ i ∈ s, mulIndicator (t i) f x := by sorry

end indicator

@[target, to_additive]
theorem prod_bij_ne_one {s : Finset α} {t : Finset γ} {f : α → β} {g : γ → β}
    (i : ∀ a ∈ s, f a ≠ 1 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
    (i_inj : ∀ a₁ h₁₁ h₁₂ a₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, i a h₁ h₂ = b) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by sorry

@[target, to_additive]
theorem exists_ne_one_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by sorry

@[target, to_additive]
theorem prod_range_succ_comm (f : ℕ → β) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = f n * ∏ x ∈ range n, f x := by sorry

@[to_additive]
theorem prod_range_succ (f : ℕ → β) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = (∏ x ∈ range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[target, to_additive]
theorem prod_range_succ' (f : ℕ → β) :
    ∀ n : ℕ, (∏ k ∈ range (n + 1), f k) = (∏ k ∈ range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]

@[to_additive]
theorem eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k ∈ range n, u k) = ∏ k ∈ range N, u k := by sorry

@[to_additive]
theorem prod_range_add (f : ℕ → β) (n m : ℕ) :
    (∏ x ∈ range (n + m), f x) = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive]
theorem prod_range_add_div_prod_range {α : Type*} [CommGroup α] (f : ℕ → α) (n m : ℕ) :
    (∏ k ∈ range (n + m), f k) / ∏ k ∈ range n, f k = ∏ k ∈ Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[target, to_additive sum_range_one]
theorem prod_range_one (f : ℕ → β) : ∏ k ∈ range 1, f k = f 0 := by sorry

open List

@[to_additive]
theorem prod_list_map_count [DecidableEq α] (l : List α) {M : Type*} [CommMonoid M] (f : α → M) :
    (l.map f).prod = ∏ m ∈ l.toFinset, f m ^ l.count m := by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a ∈ s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (not_mem_erase _ _),
      prod_insert (not_mem_erase _ _), ← mul_assoc, count_cons_self, pow_succ']
    congr 1
    refine prod_congr rfl fun x hx => ?_
    rw [count_cons_of_ne (ne_of_mem_erase hx)]
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_toFinset.2 has), pow_one]
  congr 1
  refine prod_congr rfl fun x hx => ?_
  rw [count_cons_of_ne]
  rintro rfl
  exact has hx

@[target, to_additive]
theorem prod_list_count [DecidableEq α] [CommMonoid α] (s : List α) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by sorry

@[to_additive]
theorem prod_list_count_of_subset [DecidableEq α] [CommMonoid α] (m : List α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]

open Multiset

@[to_additive]
theorem prod_multiset_map_count [DecidableEq α] (s : Multiset α) {M : Type*} [CommMonoid M]
    (f : α → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]
theorem prod_multiset_count [DecidableEq α] [CommMonoid α] (s : Multiset α) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  convert prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
theorem prod_multiset_count_of_subset [DecidableEq α] [CommMonoid α] (m : Multiset α) (s : Finset α)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive "For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can
verify that it's equal to a different function just by checking differences of adjacent terms.

This is a discrete analogue of the fundamental theorem of calculus."]
@[target]
theorem prod_range_induction (f s : ℕ → β) (base : s 0 = 1)
    (step : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
    ∏ k ∈ Finset.range n, f k = s n := by sorry
@[to_additive "A telescoping sum along `{0, ..., n - 1}` of an additive commutative group valued
function reduces to the difference of the last and first terms."]
theorem prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ range n, f (i + 1) / f i) = f n / f 0 := by apply prod_range_induction <;> simp

@[target, to_additive]
theorem prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ range n, f i / f (i + 1)) = f 0 / f n := by sorry

@[to_additive]
theorem eq_prod_range_div {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = f 0 * ∏ i ∈ range n, f (i + 1) / f i := by rw [prod_range_div, mul_div_cancel]

@[target, to_additive]
theorem eq_prod_range_div' {M : Type*} [CommGroup M] (f : ℕ → M) (n : ℕ) :
    f n = ∏ i ∈ range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by sorry
@[target]
theorem sum_range_tsub [AddCommMonoid α] [PartialOrder α] [Sub α] [OrderedSub α]
    [AddLeftMono α] [AddLeftReflectLE α] [ExistsAddOfLE α]
    {f : ℕ → α} (h : Monotone f) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by sorry

@[target]
theorem sum_tsub_distrib [AddCommMonoid α] [PartialOrder α] [ExistsAddOfLE α]
    [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)] [Sub α]
    [OrderedSub α] (s : Finset ι) {f g : ι → α} (hfg : ∀ x ∈ s, g x ≤ f x) :
    ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := sorry

@[target, to_additive (attr := sorry

@[target, to_additive sum_eq_card_nsmul]
theorem prod_eq_pow_card {b : β} (hf : ∀ a ∈ s, f a = b) : ∏ a ∈ s, f a = b ^ #s :=
  sorry

@[target, to_additive card_nsmul_add_sum]
theorem pow_card_mul_prod {b : β} : b ^ #s * ∏ a ∈ s, f a = ∏ a ∈ s, b * f a :=
  sorry

@[target, to_additive sum_add_card_nsmul]
theorem prod_mul_pow_card {b : β} : (∏ a ∈ s, f a) * b ^ #s = ∏ a ∈ s, f a * b :=
  sorry

@[target, to_additive]
theorem pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏ _k ∈ range n, b := by sorry

@[target, to_additive sum_nsmul_assoc]
lemma prod_pow_eq_pow_sum (s : Finset ι) (f : ι → ℕ) (a : β) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
  sorry

@[target, to_additive]
theorem prod_flip {n : ℕ} (f : ℕ → β) :
    (∏ r ∈ range (n + 1), f (n - r)) = ∏ k ∈ range (n + 1), f k := by sorry
@[to_additive "The difference with `Finset.sum_ninvolution` is that the involution is allowed to use
membership of the domain of the sum, rather than being a non-dependent function."]
@[target]
lemma prod_involution (g : ∀ a ∈ s, α) (hg₁ : ∀ a ha, f a * f (g a ha) = 1)
    (hg₃ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
    (g_mem : ∀ a ha, g a ha ∈ s) (hg₄ : ∀ a ha, g (g a ha) (g_mem a ha) = a) :
    ∏ x ∈ s, f x = 1 := by sorry
@[to_additive "The difference with `Finset.sum_involution` is that the involution is a non-dependent
function, rather than being allowed to use membership of the domain of the sum."]
@[target]
lemma prod_ninvolution (g : α → α) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 :=
  sorry
@[to_additive "The sum of the composition of functions `f` and `g`, is the sum over `b ∈ s.image g`
of `f b` times of the cardinality of the fibre of `b`. See also `Finset.sum_image`."]
theorem prod_comp [DecidableEq γ] (f : γ → β) (g : α → γ) :
    ∏ a ∈ s, f (g a) = ∏ b ∈ s.image g, f b ^ #{a ∈ s | g a = b} := by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ ↦ mem_image_of_mem _]

@[to_additive]
theorem prod_piecewise [DecidableEq α] (s t : Finset α) (f g : α → β) :
    (∏ x ∈ s, (t.piecewise f g) x) = (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, g x := by
  simp only [piecewise]
  rw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter]

@[target, to_additive]
theorem prod_inter_mul_prod_diff [DecidableEq α] (s t : Finset α) (f : α → β) :
    (∏ x ∈ s ∩ t, f x) * ∏ x ∈ s \ t, f x = ∏ x ∈ s, f x := by sorry

@[to_additive]
theorem prod_eq_mul_prod_diff_singleton [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x ∈ s, f x = f i * ∏ x ∈ s \ {i}, f x := by
  convert (s.prod_inter_mul_prod_diff {i} f).symm
  simp [h]

@[to_additive]
theorem prod_eq_prod_diff_singleton_mul [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s)
    (f : α → β) : ∏ x ∈ s, f x = (∏ x ∈ s \ {i}, f x) * f i := by
  rw [prod_eq_mul_prod_diff_singleton h, mul_comm]

@[to_additive]
theorem _root_.Fintype.prod_eq_mul_prod_compl [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = f a * ∏ i ∈ {a}ᶜ, f i :=
  prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[target, to_additive]
theorem _root_.Fintype.prod_eq_prod_compl_mul [DecidableEq α] [Fintype α] (a : α) (f : α → β) :
    ∏ i, f i = (∏ i ∈ {a}ᶜ, f i) * f a :=
  sorry

theorem dvd_prod_of_mem (f : α → β) {a : α} {s : Finset α} (ha : a ∈ s) : f a ∣ ∏ i ∈ s, f i := by
  classical
    rw [Finset.prod_eq_mul_prod_diff_singleton ha]
    exact dvd_mul_right _ _

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
theorem prod_partition (R : Setoid α) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[target, to_additive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
theorem prod_cancels_of_partition_cancels (R : Setoid α) [DecidableRel R]
    (h : ∀ x ∈ s, ∏ a ∈ s with R a x, f a = 1) : ∏ x ∈ s, f x = 1 := by sorry

@[target, to_additive]
theorem prod_update_of_not_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∉ s) (f : α → β)
    (b : β) : ∏ x ∈ s, Function.update f i b x = ∏ x ∈ s, f x := by sorry

@[target, to_additive]
theorem prod_update_of_mem [DecidableEq α] {s : Finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
    ∏ x ∈ s, Function.update f i b x = b * ∏ x ∈ s \ singleton i, f x := by sorry
@[to_additive eq_of_card_le_one_of_sum_eq "If a sum of a `Finset` of size at most 1 has a given
value, so do the terms in that sum."]
@[target]
theorem eq_of_card_le_one_of_prod_eq {s : Finset α} (hc : #s ≤ 1) {f : α → β} {b : β}
    (h : ∏ x ∈ s, f x = b) : ∀ x ∈ s, f x = b := by sorry
@[to_additive "Taking a sum over `s : Finset α` is the same as adding the value on a single element
`f a` to the sum over `s.erase a`.

See `Multiset.sum_map_erase` for the `Multiset` version."]
@[target]
theorem mul_prod_erase [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by sorry
@[to_additive "A variant of `Finset.add_sum_erase` with the addition swapped."]
theorem prod_erase_mul [DecidableEq α] (s : Finset α) (f : α → β) {a : α} (h : a ∈ s) :
    (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `Finset`. -/
@[to_additive "If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `Finset`."]
@[target]
theorem prod_erase [DecidableEq α] (s : Finset α) {f : α → β} {a : α} (h : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by sorry
@[to_additive "See also `Finset.sum_boole`."]
theorem prod_ite_one (s : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : β) :
    ∏ i ∈ s, ite (p i) a 1 = ite (∃ i ∈ s, p i) a 1 := by
  split_ifs with h
  · obtain ⟨i, hi, hpi⟩ := h
    rw [prod_eq_single_of_mem _ hi, if_pos hpi]
    exact fun j hj hji ↦ if_neg fun hpj ↦ hji <| h _ hj _ hi hpj hpi
  · push_neg at h
    rw [prod_eq_one]
    exact fun i hi => if_neg (h i hi)

@[target, to_additive]
theorem prod_erase_lt_of_one_lt {γ : Type*} [DecidableEq α] [CommMonoid γ] [Preorder γ]
    [MulLeftStrictMono γ] {s : Finset α} {d : α} (hd : d ∈ s) {f : α → γ}
    (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by sorry
@[to_additive "If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `Finset`."]
@[target]
theorem eq_one_of_prod_eq_one {s : Finset α} {f : α → β} {a : α} (hp : ∏ x ∈ s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by sorry

@[to_additive sum_boole_nsmul]
theorem prod_pow_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∏ x ∈ s, f x ^ ite (a = x) 1 0) = ite (a ∈ s) (f a) 1 := by simp

@[target]
theorem prod_dvd_prod_of_dvd {S : Finset α} (g1 g2 : α → β) (h : ∀ a ∈ S, g1 a ∣ g2 a) :
    S.prod g1 ∣ S.prod g2 := by sorry

@[target, to_additive]
lemma prod_mul_eq_prod_mul_of_exists {s : Finset α} {f : α → β} {b₁ b₂ : β}
    (a : α) (ha : a ∈ s) (h : f a * b₁ = f a * b₂) :
    (∏ a ∈ s, f a) * b₁ = (∏ a ∈ s, f a) * b₂ := by sorry

@[target, to_additive]
lemma isSquare_prod {s : Finset ι} [CommMonoid α] (f : ι → α)
    (h : ∀ c ∈ s, IsSquare (f c)) : IsSquare (∏ i ∈ s, f i) := by sorry

end CommMonoid

section CancelCommMonoid
variable [DecidableEq ι] [CancelCommMonoid α] {s t : Finset ι} {f : ι → α}

@[target, to_additive]
lemma prod_sdiff_eq_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i = ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i = ∏ i ∈ t, f i :=
  sorry

@[target, to_additive]
lemma prod_sdiff_ne_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i ≠ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≠ ∏ i ∈ t, f i :=
  sorry

end CancelCommMonoid

theorem card_eq_sum_ones (s : Finset α) : #s = ∑ _ ∈ s, 1 := by simp

theorem sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁

lemma sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι → κ) : ∑ j ∈ t, #{i ∈ s | g i = j} = #{i ∈ s | g i ∈ t} := by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

@[target]
lemma card_filter (p) [DecidablePred p] (s : Finset ι) :
    #{i ∈ s | p i} = ∑ i ∈ s, ite (p i) 1 0 := by sorry

section CommGroup

variable [CommGroup β] [DecidableEq α]

@[to_additive (attr := simp)]
theorem prod_sdiff_eq_div (h : s₁ ⊆ s₂) :
    ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[target, to_additive]
theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by sorry

@[target, to_additive (attr := by sorry

end CommGroup

@[simp]
theorem card_disjiUnion (s : Finset α) (t : α → Finset β) (h) :
    #(s.disjiUnion t h) = ∑ a ∈ s, #(t a) :=
  Multiset.card_bind _ _

theorem card_biUnion [DecidableEq β] {s : Finset α} {t : α → Finset β}
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (t x) (t y)) : #(s.biUnion t) = ∑ u ∈ s, #(t u) := by
  simpa using sum_biUnion h (β := ℕ) (f := 1)

@[target]
theorem card_biUnion_le [DecidableEq β] {s : Finset α} {t : α → Finset β} :
    #(s.biUnion t) ≤ ∑ a ∈ s, #(t a) :=
  sorry
      #((insert a s).biUnion t) ≤ #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ ≤ ∑ a ∈ insert a s, #(t a) := by rw [sum_insert has]; exact Nat.add_le_add_left ih _

@[target]
theorem card_eq_sum_card_fiberwise [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
    (H : ∀ x ∈ s, f x ∈ t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b} := by sorry

@[target]
theorem card_eq_sum_card_image [DecidableEq β] (f : α → β) (s : Finset α) :
    #s = ∑ b ∈ s.image f, #{a ∈ s | f a = b} :=
  sorry

theorem mem_sum {f : α → Multiset β} (s : Finset α) (b : β) :
    (b ∈ ∑ x ∈ s, f x) ↔ ∃ a ∈ s, b ∈ f a := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t hi ih => simp [sum_cons, ih, or_and_right, exists_or]

@[target, to_additive]
theorem prod_unique_nonempty {α β : Type*} [CommMonoid β] [Unique α] (s : Finset α) (f : α → β)
    (h : s.Nonempty) : ∏ x ∈ s, f x = f default := by sorry

section Image_Overlap

variable {α β ι : Type*} [DecidableEq α]

@[target, to_additive]
lemma prod_filter_of_pairwise_eq_one [CommMonoid β] {f : ι → α} {g : α → β} {n : ι} {I : Finset ι}
    (hn : n ∈ I) (hf : (I : Set ι).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ j ∈ filter (fun j ↦ f j = f n) I, g (f j) = g (f n) := by sorry
@[to_additive (attr := simp)
"A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 0`.
The conclusion is the same as in `sum_image`."]
@[target]
lemma prod_image_of_pairwise_eq_one [CommMonoid β] {f : ι → α} {g : α → β} {I : Finset ι}
    (hf : (I : Set ι).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by sorry
@[to_additive (attr := simp)
"A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 0`. The
conclusion is the same as in `sum_image`."
]
@[target]
lemma prod_image_of_disjoint [CommMonoid β] [PartialOrder α] [OrderBot α] {f : ι → α} {g : α → β}
    (hg_bot : g ⊥ = 1) {I : Finset ι} (hf_disj : (I : Set ι).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by sorry

end Image_Overlap

end Finset

namespace Fintype
variable {ι κ α : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid α]

@[target, to_additive]
lemma prod_of_injective (e : ι → κ) (he : Injective e) (f : ι → α) (g : κ → α)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j :=
  sorry

@[to_additive]
lemma prod_fiberwise [DecidableEq κ] (g : ι → κ) (f : ι → α) :
    ∏ j, ∏ i : {i // g i = j}, f i = ∏ i, f i := by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[target, to_additive]
lemma prod_fiberwise' [DecidableEq κ] (g : ι → κ) (f : κ → α) :
    ∏ j, ∏ _i : {i // g i = j}, f j = ∏ i, f (g i) := by sorry

@[to_additive]
theorem prod_unique {α β : Type*} [CommMonoid β] [Unique α] [Fintype α] (f : α → β) :
    ∏ x : α, f x = f default := by rw [univ_unique, prod_singleton]

@[target, to_additive]
theorem prod_subsingleton {α β : Type*} [CommMonoid β] [Subsingleton α] [Fintype α] (f : α → β)
    (a : α) : ∏ x : α, f x = f a := by sorry

@[to_additive] theorem prod_Prop {β} [CommMonoid β] (f : Prop → β) :
    ∏ p, f p = f True * f False := by simp

@[target, to_additive]
theorem prod_subtype_mul_prod_subtype {α β : Type*} [Fintype α] [CommMonoid β] (p : α → Prop)
    (f : α → β) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by sorry

@[to_additive] lemma prod_subset {s : Finset ι} {f : ι → α} (h : ∀ i, f i ≠ 1 → i ∈ s) :
    ∏ i ∈ s, f i = ∏ i, f i :=
  Finset.prod_subset s.subset_univ <| by simpa [not_imp_comm (a := _ ∈ s)]

@[to_additive]
lemma prod_ite_eq_ite_exists (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j)
    (a : α) : ∏ i, ite (p i) a 1 = ite (∃ i, p i) a 1 := by
  simp [prod_ite_one univ p (by simpa using h)]

variable [DecidableEq ι]

@[target, to_additive]
lemma prod_ite_mem (s : Finset ι) (f : ι → α) : ∏ i, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by sorry
@[to_additive "See also `Finset.sum_dite_eq`."] lemma prod_dite_eq (i : ι) (f : ∀ j, i = j → α) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_dite_eq'`. -/
@[to_additive "See also `Finset.sum_dite_eq'`."] lemma prod_dite_eq' (i : ι) (f : ∀ j, j = i → α) :
    ∏ j, (if h : j = i then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq', if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq`. -/
@[to_additive "See also `Finset.sum_ite_eq`."]
lemma prod_ite_eq (i : ι) (f : ι → α) : ∏ j, (if i = j then f j else 1) = f i := by
  rw [Finset.prod_ite_eq, if_pos (mem_univ _)]

/-- See also `Finset.prod_ite_eq'`. -/
@[target, to_additive "See also `Finset.sum_ite_eq'`."]
lemma prod_ite_eq' (i : ι) (f : ι → α) : ∏ j, (if j = i then f j else 1) = f i := by sorry
@[to_additive "See also `Finset.sum_pi_single`."]
lemma prod_pi_mulSingle {α : ι → Type*} [∀ i, CommMonoid (α i)] (i : ι) (f : ∀ i, α i) :
    ∏ j, Pi.mulSingle j (f j) i = f i := prod_dite_eq _ _

/-- See also `Finset.prod_pi_mulSingle'`. -/
@[target, to_additive "See also `Finset.sum_pi_single'`."]
lemma prod_pi_mulSingle' (i : ι) (a : α) : ∏ j, Pi.mulSingle i a j = a := sorry

end CommMonoid
end Fintype

namespace List

@[to_additive]
theorem prod_toFinset {M : Type*} [DecidableEq α] [CommMonoid M] (f : α → M) :
    ∀ {l : List α} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨not_mem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp not_mem), prod_toFinset _ hl]

@[simp]
theorem sum_toFinset_count_eq_length [DecidableEq α] (l : List α) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : ℕ)).symm

end List

namespace Multiset

@[target, simp]
lemma mem_sum {s : Finset ι} {m : ι → Multiset α} : a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by sorry

variable [DecidableEq α]

theorem toFinset_sum_count_eq (s : Multiset α) : ∑ a ∈ s.toFinset, s.count a = card s := by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : ℕ))).symm

@[simp] lemma sum_count_eq_card {s : Finset α} {m : Multiset α} (hms : ∀ a ∈ m, a ∈ s) :
    ∑ a ∈ s, m.count a = card m := by
  rw [← toFinset_sum_count_eq, ← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[target, simp]
theorem toFinset_sum_count_nsmul_eq (s : Multiset α) :
    ∑ a ∈ s.toFinset, s.count a • {a} = s := by sorry

theorem exists_smul_of_dvd_count (s : Multiset α) {k : ℕ}
    (h : ∀ a : α, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset α, s = k • u := by
  use ∑ a ∈ s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x ∈ s.toFinset, k • (count x s / k) • ({x} : Multiset α)) =
      ∑ x ∈ s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, toFinset_sum_count_nsmul_eq]

@[target, to_additive]
theorem prod_sum {α : Type*} {ι : Type*} [CommMonoid α] (f : ι → Multiset α) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by sorry

end Multiset

@[to_additive (attr := simp)]
lemma IsUnit.prod_iff [CommMonoid β] : IsUnit (∏ a ∈ s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha hs => rw [Finset.prod_cons, IsUnit.mul_iff, hs, Finset.forall_mem_cons]

@[target, to_additive]
lemma IsUnit.prod_univ_iff [Fintype α] [CommMonoid β] : IsUnit (∏ a, f a) ↔ ∀ a, IsUnit (f a) := by sorry

@[target]
theorem nat_abs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by sorry