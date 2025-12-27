import VerifiedAgora.tagger
/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Support
import Mathlib.Data.Set.SymmDiff

/-!
# Indicator function

- `Set.indicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `Set.mulIndicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `fun _ ↦ 1`.

The indicator function is implemented non-computably, to avoid having to pass around `Decidable`
arguments. This is in contrast with the design of `Pi.single` or `Set.piecewise`.

## Tags
indicator, characteristic
-/

assert_not_exists MonoidWithZero

open Function

variable {α β M N : Type*}

namespace Set

section One

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

/-- `Set.mulIndicator s f a` is `f a` if `a ∈ s`, `1` otherwise. -/
@[to_additive "`Set.indicator s f a` is `f a` if `a ∈ s`, `0` otherwise."]
noncomputable def mulIndicator (s : Set α) (f : α → M) (x : α) : M :=
  haveI := Classical.decPred (· ∈ s)
  if x ∈ s then f x else 1

@[to_additive (attr := simp)]
theorem piecewise_eq_mulIndicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun _ => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[target] theorem mulIndicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    mulIndicator s f a = if a ∈ s then f a else 1 := by
  sorry


@[to_additive (attr := simp)]
theorem mulIndicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a :=
  if_pos h

@[to_additive (attr := simp)]
theorem mulIndicator_of_not_mem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 :=
  if_neg h

@[to_additive]
theorem mulIndicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a := by
  by_cases h : a ∈ s
  · exact Or.inr (mulIndicator_of_mem h f)
  · exact Or.inl (mulIndicator_of_not_mem h f)

@[target] theorem mulIndicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 :=
  letI := Classical.dec (a ∈ s)
  ite_eq_left_iff.trans (by sorry


@[to_additive (attr := simp)]
theorem mulIndicator_eq_self : s.mulIndicator f = f ↔ mulSupport f ⊆ s := by
  simp only [funext_iff, subset_def, mem_mulSupport, mulIndicator_apply_eq_self, not_imp_comm]

@[to_additive]
theorem mulIndicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) :
    t.mulIndicator f = f := by
  rw [mulIndicator_eq_self] at h1 ⊢
  exact Subset.trans h1 h2

@[to_additive (attr := by sorry


@[target] theorem mulIndicator_eq_one : (mulIndicator s f = fun _ => 1) ↔ Disjoint (mulSupport f) s := by
  sorry


@[to_additive (attr := simp)]
theorem mulIndicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (mulSupport f) s :=
  mulIndicator_eq_one

@[to_additive]
theorem mulIndicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ mulSupport f := by
  simp only [Ne, mulIndicator_apply_eq_one, Classical.not_imp, mem_inter_iff, mem_mulSupport]

@[to_additive (attr := simp)]
theorem mulSupport_mulIndicator :
    Function.mulSupport (s.mulIndicator f) = s ∩ Function.mulSupport f :=
  ext fun x => by simp [Function.mem_mulSupport, mulIndicator_apply_eq_one]

/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[target] theorem mem_of_mulIndicator_ne_one (h : mulIndicator s f a ≠ 1) : a ∈ s := by sorry


/-- See `Set.eqOn_mulIndicator'` for the version with `sᶜ`. -/
/-- See `Set.eqOn_mulIndicator'` for the version with `sᶜ`. -/
@[target] theorem eqOn_mulIndicator : EqOn (mulIndicator s f) f s := by sorry


/-- See `Set.eqOn_mulIndicator` for the version with `s`. -/
@[to_additive
      "See `Set.eqOn_indicator` for the version with `s`."]
theorem eqOn_mulIndicator' : EqOn (mulIndicator s f) 1 sᶜ :=
  fun _ hx => mulIndicator_of_not_mem hx f

@[target] theorem mulSupport_mulIndicator_subset : mulSupport (s.mulIndicator f) ⊆ s := by sorry


@[to_additive (attr := by sorry


@[target] theorem mulIndicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    sorry


@[target] theorem mulIndicator_eq_mulIndicator {t : Set β} {g : β → M} {b : β}
    (h1 : a ∈ s ↔ b ∈ t) (h2 : f a = g b) :
    s.mulIndicator f a = t.mulIndicator g b := by
  sorry


@[target] theorem mulIndicator_const_eq_mulIndicator_const {t : Set β} {b : β} {c : M} (h : a ∈ s ↔ b ∈ t) :
    s.mulIndicator (fun _ ↦ c) a = t.mulIndicator (fun _ ↦ c) b := by sorry


@[to_additive (attr := simp)]
theorem mulIndicator_univ (f : α → M) : mulIndicator (univ : Set α) f = f :=
  mulIndicator_eq_self.2 <| subset_univ _

@[to_additive (attr := by sorry


@[to_additive]
theorem mulIndicator_empty' (f : α → M) : mulIndicator (∅ : Set α) f = 1 :=
  mulIndicator_empty f

variable (M)

@[target] theorem mulIndicator_one (s : Set α) : (mulIndicator s fun _ => (1 : M)) = fun _ => (1 : M) :=
  mulIndicator_eq_one.2 <| by sorry


@[to_additive (attr := simp)]
theorem mulIndicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 :=
  mulIndicator_one M s

variable {M}

@[to_additive]
theorem mulIndicator_mulIndicator (s t : Set α) (f : α → M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s ∩ t) f :=
  funext fun x => by
    simp only [mulIndicator]
    split_ifs <;> simp_all +contextual

@[to_additive (attr := simp)]
theorem mulIndicator_inter_mulSupport (s : Set α) (f : α → M) :
    mulIndicator (s ∩ mulSupport f) f = mulIndicator s f := by
  rw [← mulIndicator_mulIndicator, mulIndicator_mulSupport]

@[target] theorem comp_mulIndicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  sorry


@[to_additive]
theorem mulIndicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) := by
  simp only [mulIndicator, Function.comp]
  split_ifs with h h' h'' <;> first | rfl | contradiction

@[target] theorem mulIndicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  sorry


@[to_additive]
theorem mulIndicator_comp_of_one {g : M → N} (hg : g 1 = 1) :
    mulIndicator s (g ∘ f) = g ∘ mulIndicator s f := by
  funext
  simp only [mulIndicator]
  split_ifs <;> simp [*]

@[to_additive]
theorem comp_mulIndicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun _ => c) x)) = s.mulIndicator fun _ => f c :=
  (mulIndicator_comp_of_one hf).symm

@[to_additive]
theorem mulIndicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) :=
  letI := Classical.decPred (· ∈ s)
  piecewise_preimage s f 1 B

@[target] theorem mulIndicator_one_preimage (s : Set M) :
    t.mulIndicator 1 ⁻¹' s ∈ ({Set.univ, ∅} : Set (Set α)) := by
  sorry

  classical
    rw [mulIndicator_one', preimage_one]
    split_ifs <;> simp

@[to_additive]
theorem mulIndicator_const_preimage_eq_union (U : Set α) (s : Set M) (a : M) [Decidable (a ∈ s)]
    [Decidable ((1 : M) ∈ s)] : (U.mulIndicator fun _ => a) ⁻¹' s =
      (if a ∈ s then U else ∅) ∪ if (1 : M) ∈ s then Uᶜ else ∅ := by
  rw [mulIndicator_preimage, preimage_one, preimage_const]
  split_ifs <;> simp [← compl_eq_univ_diff]

@[target] theorem mulIndicator_const_preimage (U : Set α) (s : Set M) (a : M) :
    (U.mulIndicator fun _ => a) ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by
  sorry

  classical
    rw [mulIndicator_const_preimage_eq_union]
    split_ifs <;> simp

@[target] theorem indicator_one_preimage [Zero M] (U : Set α) (s : Set M) :
    U.indicator 1 ⁻¹' s ∈ ({Set.univ, U, Uᶜ, ∅} : Set (Set α)) := by sorry


@[target] theorem mulIndicator_preimage_of_not_mem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  sorry


@[to_additive]
theorem mem_range_mulIndicator {r : M} {s : Set α} {f : α → M} :
    r ∈ range (mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
  simp [mulIndicator, ite_eq_iff, exists_or, eq_univ_iff_forall, and_comm, or_comm,
    @eq_comm _ r 1]

@[target] theorem mulIndicator_rel_mulIndicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) := by
  sorry


end One

section Monoid

variable [MulOneClass M] {s t : Set α} {a : α}

@[target] theorem mulIndicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a
      = mulIndicator s f a * mulIndicator t f a := by
  sorry


@[to_additive]
theorem mulIndicator_union_mul_inter (f : α → M) (s t : Set α) :
    mulIndicator (s ∪ t) f * mulIndicator (s ∩ t) f = mulIndicator s f * mulIndicator t f :=
  funext <| mulIndicator_union_mul_inter_apply f s t

@[target] theorem mulIndicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → M) :
    mulIndicator (s ∪ t) f a = mulIndicator s f a * mulIndicator t f a := by
  sorry


@[target] theorem mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
    mulIndicator (s ∪ t) f = fun a => mulIndicator s f a * mulIndicator t f a := by sorry


open scoped symmDiff in
@[to_additive]
theorem mulIndicator_symmDiff (s t : Set α) (f : α → M) :
    mulIndicator (s ∆ t) f = mulIndicator (s \ t) f * mulIndicator (t \ s) f :=
  mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

@[target] theorem mulIndicator_mul (s : Set α) (f g : α → M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a := by
  sorry


@[to_additive]
theorem mulIndicator_mul' (s : Set α) (f g : α → M) :
    mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g :=
  mulIndicator_mul s f g

@[target] theorem mulIndicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator sᶜ f a * mulIndicator s f a = f a :=
  by_cases (fun ha : a ∈ s => by sorry


@[target] theorem mulIndicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a * mulIndicator sᶜ f a = f a :=
  by_cases (fun ha : a ∈ s => by sorry


@[to_additive (attr := by sorry


@[target] theorem mulIndicator_mul_eq_left {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport f).mulIndicator (f * g) = f := by
  sorry


@[target] theorem mulIndicator_mul_eq_right {f g : α → M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport g).mulIndicator (f * g) = g := by
  sorry


@[to_additive]
theorem mulIndicator_mul_compl_eq_piecewise [DecidablePred (· ∈ s)] (f g : α → M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g := by
  ext x
  by_cases h : x ∈ s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_not_mem (Set.not_mem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_not_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_not_mem h,
      Set.mulIndicator_of_mem (Set.mem_compl h), one_mul]

/-- `Set.mulIndicator` as a `monoidHom`. -/
@[to_additive "`Set.indicator` as an `addMonoidHom`."]
noncomputable def mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α → M) →* α → M where
  toFun := mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s

end Monoid

section Group

variable {G : Type*} [Group G] {s t : Set α}

@[target] theorem mulIndicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ := by sorry


@[to_additive]
theorem mulIndicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ :=
  mulIndicator_inv' s f

@[target] theorem mulIndicator_div (s : Set α) (f g : α → G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a := by sorry


@[to_additive]
theorem mulIndicator_div' (s : Set α) (f g : α → G) :
    mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g :=
  mulIndicator_div s f g

@[target] theorem mulIndicator_compl (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f * (mulIndicator s f)⁻¹ := by sorry


@[to_additive indicator_compl]
theorem mulIndicator_compl' (s : Set α) (f : α → G) :
    mulIndicator sᶜ f = f / mulIndicator s f := by rw [div_eq_mul_inv, mulIndicator_compl]

@[target] theorem mulIndicator_diff (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by
    sorry


@[to_additive indicator_diff]
theorem mulIndicator_diff' (h : s ⊆ t) (f : α → G) :
    mulIndicator (t \ s) f = mulIndicator t f / mulIndicator s f := by
  rw [mulIndicator_diff h, div_eq_mul_inv]

open scoped symmDiff in
@[to_additive]
theorem apply_mulIndicator_symmDiff {g : G → β} (hg : ∀ x, g x⁻¹ = g x)
    (s t : Set α) (f : α → G) (x : α) :
    g (mulIndicator (s ∆ t) f x) = g (mulIndicator s f x / mulIndicator t f x) := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [mem_symmDiff, *]

end Group

end Set

@[to_additive]
theorem MonoidHom.map_mulIndicator {M N : Type*} [MulOneClass M] [MulOneClass N] (f : M →* N)
    (s : Set α) (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  simp [Set.mulIndicator_comp_of_one]
