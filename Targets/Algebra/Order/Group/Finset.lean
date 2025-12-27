import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Data.Finset.Lattice.Prod

/-!
# `Finset.sup` in a group
-/

open scoped Finset

assert_not_exists MonoidWithZero

namespace Multiset
variable {α : Type*} [DecidableEq α]

@[simp] lemma toFinset_nsmul (s : Multiset α) : ∀ n ≠ 0, (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
  | n + 1, _ => by
    by_cases h : n = 0
    · rw [h, zero_add, one_nsmul]
    · rw [add_nsmul, toFinset_add, one_nsmul, toFinset_nsmul s n h, Finset.union_idempotent]

@[target]
lemma toFinset_eq_singleton_iff (s : Multiset α) (a : α) :
    s.toFinset = {a} ↔ card s ≠ 0 ∧ s = card s • {a} := by sorry

lemma toFinset_card_eq_one_iff (s : Multiset α) :
    #s.toFinset = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a} := by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

end Multiset

namespace Finset
variable {ι κ M G : Type*}

@[target]
lemma fold_max_add [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : WithBot M)
    (f : ι → M) : s.fold max ⊥ (fun i ↦ ↑(f i) + a) = s.fold max ⊥ ((↑) ∘ f) + a := by sorry

@[to_additive nsmul_inf']
lemma inf'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.inf' hs f ^ n = s.inf' hs fun a ↦ f a ^ n :=
  map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

@[to_additive nsmul_sup']
lemma sup'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.sup' hs f ^ n = s.sup' hs fun a ↦ f a ^ n :=
  map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _

section Group
variable [Group G] [LinearOrder G]

@[to_additive "Also see `Finset.sup'_add'` that works for canonically ordered monoids."]
lemma sup'_mul [MulRightMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := map_finset_sup' (OrderIso.mulRight a) hs f

set_option linter.docPrime false in
@[to_additive "Also see `Finset.add_sup''` that works for canonically ordered monoids."]
lemma mul_sup' [MulLeftMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := map_finset_sup' (OrderIso.mulLeft a) hs f

end Group

section CanonicallyLinearOrderedAddCommMonoid
variable [LinearOrderedAddCommMonoid M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

/-- Also see `Finset.sup'_add` that works for ordered groups. -/
@[target]
lemma sup'_add' (s : Finset ι) (f : ι → M) (a : M) (hs : s.Nonempty) :
    s.sup' hs f + a = s.sup' hs fun i ↦ f i + a := by sorry
@[target]
lemma add_sup'' (hs : s.Nonempty) (f : ι → M) (a : M) :
    a + s.sup' hs f = s.sup' hs fun i ↦ a + f i := by sorry

@[target]
lemma sup_add_sup (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → M) (g : κ → M) :
    s.sup f + t.sup g = (s ×ˢ t).sup fun ij ↦ f ij.1 + g ij.2 := by sorry

end CanonicallyLinearOrderedAddCommMonoid
end Finset
