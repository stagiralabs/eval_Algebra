import VerifiedAgora.tagger
/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Indicator
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Support of a function in an order

This file relates the support of a function to order constructions.
-/

assert_not_exists MonoidWithZero

open Set

variable {ι : Sort*} {α M : Type*}

namespace Function
variable [One M]

@[target, to_additive]
lemma mulSupport_sup [SemilatticeSup M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊔ g x) ⊆ mulSupport f ∪ mulSupport g :=
  sorry

@[to_additive]
lemma mulSupport_inf [SemilatticeInf M] (f g : α → M) :
    mulSupport (fun x ↦ f x ⊓ g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· ⊓ ·) (inf_idem _) f g

@[target, to_additive]
lemma mulSupport_max [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ max (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := sorry

@[target, to_additive]
lemma mulSupport_min [LinearOrder M] (f g : α → M) :
    mulSupport (fun x ↦ min (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := sorry

@[target, to_additive]
lemma mulSupport_iSup [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨆ i, f i x) ⊆ ⋃ i, mulSupport (f i) := by sorry

@[target, to_additive]
lemma mulSupport_iInf [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    mulSupport (fun x ↦ ⨅ i, f i x) ⊆ ⋃ i, mulSupport (f i) := sorry

end Function

namespace Set

section LE
variable [LE M] [One M] {s : Set α} {f g : α → M} {a : α} {y : M}

@[to_additive]
lemma mulIndicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) :
    mulIndicator s f a ≤ y := by
  by_cases ha : a ∈ s
  · simpa [ha] using hfg ha
  · simpa [ha] using hg ha

@[to_additive]
lemma mulIndicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ a, a ∉ s → 1 ≤ g a) :
    mulIndicator s f ≤ g := fun _ ↦ mulIndicator_apply_le' (hfg _) (hg _)

@[target, to_additive]
lemma le_mulIndicator_apply (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) :
    y ≤ mulIndicator s g a := sorry

@[target, to_additive]
lemma le_mulIndicator (hfg : ∀ a ∈ s, f a ≤ g a) (hf : ∀ a ∉ s, f a ≤ 1) :
    f ≤ mulIndicator s g := sorry

end LE

section Preorder
variable [Preorder M] [One M] {s t : Set α} {f g : α → M} {a : α}

@[to_additive indicator_apply_nonneg]
lemma one_le_mulIndicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mulIndicator_apply h fun _ ↦ le_rfl

@[target, to_additive indicator_nonneg]
lemma one_le_mulIndicator (h : ∀ a ∈ s, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  sorry

@[target, to_additive]
lemma mulIndicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  sorry

@[target, to_additive]
lemma mulIndicator_le_one (h : ∀ a ∈ s, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  sorry

@[to_additive]
lemma mulIndicator_le_mulIndicator' (h : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ mulIndicator s g a :=
  mulIndicator_rel_mulIndicator le_rfl h

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[to_additive]
lemma mulIndicator_le_mulIndicator_apply_of_subset (h : s ⊆ t) (hf : 1 ≤ f a) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mulIndicator_apply_le'
    (fun ha ↦ le_mulIndicator_apply (fun _ ↦ le_rfl) fun hat ↦ (hat <| h ha).elim) fun _ ↦
    one_le_mulIndicator_apply fun _ ↦ hf

@[target, to_additive]
lemma mulIndicator_le_mulIndicator_of_subset (h : s ⊆ t) (hf : 1 ≤ f) :
    mulIndicator s f ≤ mulIndicator t f :=
  sorry

@[to_additive]
lemma mulIndicator_le_self' (hf : ∀ x ∉ s, 1 ≤ f x) : mulIndicator s f ≤ f :=
  mulIndicator_le' (fun _ _ ↦ le_rfl) hf

end Preorder

section LinearOrder
variable [Zero M] [LinearOrder M]

@[target]
lemma indicator_le_indicator_nonneg (s : Set α) (f : α → M) :
    s.indicator f ≤ {a | 0 ≤ f a}.indicator f := by sorry

lemma indicator_nonpos_le_indicator (s : Set α) (f : α → M) :
    {a | f a ≤ 0}.indicator f ≤ s.indicator f :=
  indicator_le_indicator_nonneg (M := Mᵒᵈ) _ _

end LinearOrder

section CompleteLattice
variable [CompleteLattice M] [One M]

@[target, to_additive]
lemma mulIndicator_iUnion_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by sorry

variable [Nonempty ι]

@[target, to_additive]
lemma mulIndicator_iInter_apply (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by sorry

@[target, to_additive]
lemma iSup_mulIndicator {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {f : ι → α → M}
    {s : ι → Set α} (h1 : (⊥ : M) = 1) (hf : Monotone f) (hs : Monotone s) :
    ⨆ i, (s i).mulIndicator (f i) = (⋃ i, s i).mulIndicator (⨆ i, f i) := by sorry

end CompleteLattice

section CanonicallyOrderedMul

variable [Monoid M] [PartialOrder M] [CanonicallyOrderedMul M]

@[target, to_additive]
lemma mulIndicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  sorry

@[target, to_additive]
lemma mulIndicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) :
    mulIndicator s f a ≤ g a :=
  sorry

@[target, to_additive]
lemma mulIndicator_le {s : Set α} {f g : α → M} (hfg : ∀ a ∈ s, f a ≤ g a) :
    mulIndicator s f ≤ g :=
  sorry

end CanonicallyOrderedMul

section LinearOrderedCommGroup
variable [LinearOrderedCommGroup M]

open scoped symmDiff

@[target, to_additive]
lemma mabs_mulIndicator_symmDiff (s t : Set α) (f : α → M) (x : α) :
    |mulIndicator (s ∆ t) f x|ₘ = |mulIndicator s f x / mulIndicator t f x|ₘ :=
  sorry

end LinearOrderedCommGroup
end Set
