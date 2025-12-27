import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.Finsupp.Ext
import Mathlib.Data.Finsupp.Fin
import Mathlib.Data.Finsupp.Indicator

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/

assert_not_exists Field

noncomputable section

open Finset Function

variable {α ι γ A B C : Type*} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid C]
variable {t : ι → A → C}
variable {s : Finset α} {f : α → ι →₀ A} (i : ι)
variable (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)
variable {β M M' N P G H R S : Type*}

namespace Finsupp

/-!
### Declarations about `Finsupp.sum` and `Finsupp.prod`

In most of this section, the domain `β` is assumed to be an `AddMonoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g a (f a)` over the support of `f`. "]
def prod [Zero M] [CommMonoid N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a ∈ f.support, g a (f a)

variable [Zero M] [Zero M'] [CommMonoid N]

@[target, to_additive]
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.support ⊆ s) (g : α → M → N)
    (h : ∀ i ∈ s, g i 0 = 1) : f.prod g = ∏ x ∈ s, g x (f x) := by sorry

@[target, to_additive]
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) :
    f.prod g = ∏ i, g i (f i) :=
  sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem prod_mapRange_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N}
    (h0 : ∀ a, h a 0 = 1) : (mapRange f hf g).prod h = g.prod fun a b => h a (f b) :=
  sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
    (f.prod fun x v => g.prod fun x' v' => h x v x' v') =
      g.prod fun x' v' => f.prod fun x v => h x v x' v' :=
  sorry

@[to_additive (attr := simp)]
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.support) (b a (f a)) 1 := by
  dsimp [Finsupp.prod]
  rw [f.support.prod_ite_eq]

theorem sum_ite_self_eq [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (a = x) v 0) = f a := by
  classical
    convert f.sum_ite_eq a fun _ => id
    simp [ite_eq_right_iff.2 Eq.symm]

/--
The left hand side of `sum_ite_self_eq` simplifies; this is the variant that is useful for `simp`.
-/
@[target, simp]
theorem if_mem_support [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (if a ∈ f.support then f a else 0) = f a := by sorry
@[target, to_additive (attr := by sorry
@[target]
theorem sum_ite_self_eq' [DecidableEq α] {N : Type*} [AddCommMonoid N] (f : α →₀ N) (a : α) :
    (f.sum fun x v => ite (x = a) v 0) = f a := by sorry

@[to_additive (attr := simp)]
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) :
    (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  f.prod_fintype _ fun _ ↦ pow_zero _

@[target, to_additive (attr := sorry
@[to_additive
      "If `g` maps a second argument of 0 to 0, summing it over the
      result of `onFinset` is the same as summing it over the original `Finset`."]
theorem onFinset_prod {s : Finset α} {f : α → M} {g : α → M → N} (hf : ∀ a, f a ≠ 0 → a ∈ s)
    (hg : ∀ a, g a 0 = 1) : (onFinset s f hf).prod g = ∏ a ∈ s, g a (f a) :=
  Finset.prod_subset support_onFinset_subset <| by simp +contextual [*]

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      " Taking a sum over `f : α →₀ M` is the same as adding the value on a
      single element `y ∈ f.support` to the sum over `erase y f`. "]
theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.support) :
    g y (f y) * (erase y f).prod g = f.prod g := by
  classical
    rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase,
      Finset.prod_congr rfl]
    intro h hx
    rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

/-- Generalization of `Finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      " Generalization of `Finsupp.add_sum_erase`: if `g` maps a second argument of 0
      to 0, then its sum over `f : α →₀ M` is the same as adding the value on any element
      `y : α` to the sum over `erase y f`. "]
@[target]
theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).prod g = f.prod g := by sorry

@[target, to_additive]
theorem _root_.SubmonoidClass.finsupp_prod_mem {S : Type*} [SetLike S N] [SubmonoidClass S N]
    (s : S) (f : α →₀ M) (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  sorry

@[to_additive]
theorem prod_congr {f : α →₀ M} {g1 g2 : α → M → N} (h : ∀ x ∈ f.support, g1 x (f x) = g2 x (f x)) :
    f.prod g1 = f.prod g2 :=
  Finset.prod_congr rfl h

@[target, to_additive]
theorem prod_eq_single {f : α →₀ M} (a : α) {g : α → M → N}
    (h₀ : ∀ b, f b ≠ 0 → b ≠ a → g b (f b) = 1) (h₁ : f a = 0 → g a 0 = 1) :
    f.prod g = g a (f a) := by sorry

end SumProd

section CommMonoidWithZero
variable [Zero α] [CommMonoidWithZero β] [Nontrivial β] [NoZeroDivisors β]
  {f : ι →₀ α} (a : α) {g : ι → α → β}

@[target, simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := sorry
@[target]
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := sorry

end CommMonoidWithZero
end Finsupp

@[target, to_additive]
theorem map_finsupp_prod [Zero M] [CommMonoid N] [CommMonoid P] {H : Type*}
    [FunLike H N P] [MonoidHomClass H N P]
    (h : H) (f : α →₀ M) (g : α → M → N) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  sorry

@[to_additive]
theorem MonoidHom.coe_finsupp_prod [Zero β] [Monoid N] [CommMonoid P] (f : α →₀ β)
    (g : α → β → N →* P) : ⇑(f.prod g) = f.prod fun i fi => ⇑(g i fi) :=
  MonoidHom.coe_finset_prod _ _

@[target, to_additive (attr := sorry

namespace Finsupp

theorem single_multiset_sum [AddCommMonoid M] (s : Multiset M) (a : α) :
    single a s.sum = (s.map (single a)).sum :=
  Multiset.induction_on s (single_zero _) fun a s ih => by
    rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]

theorem single_finset_sum [AddCommMonoid M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b ∈ s, f b) = ∑ b ∈ s, single a (f b) := by
  trans
  · apply single_multiset_sum
  · rw [Multiset.map_map]
    rfl

@[target]
theorem single_sum [Zero M] [AddCommMonoid N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.sum f) = s.sum fun d c => single a (f d c) :=
  sorry

@[target, to_additive]
theorem prod_neg_index [AddGroup G] [CommMonoid M] {g : α →₀ G} {h : α → G → M}
    (h0 : ∀ a, h a 0 = 1) : (-g).prod h = g.prod fun a b => h a (-b) :=
  sorry

end Finsupp

namespace Finsupp

@[target]
theorem finset_sum_apply [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) (a : α) :
    (∑ i ∈ S, f i) a = ∑ i ∈ S, f i a :=
  sorry

@[target, simp]
theorem sum_apply [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.sum g) a₂ = f.sum fun a₁ b => g a₁ b a₂ :=
  sorry

@[simp, norm_cast] theorem coe_finset_sum [AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N) :
    ⇑(∑ i ∈ S, f i) = ∑ i ∈ S, ⇑(f i) :=
  map_sum (coeFnAddHom : (α →₀ N) →+ _) _ _

@[simp, norm_cast] theorem coe_sum [Zero M] [AddCommMonoid N] (f : α →₀ M) (g : α → M → β →₀ N) :
    ⇑(f.sum g) = f.sum fun a₁ b => ⇑(g a₁ b) :=
  coe_finset_sum _ _

@[target]
theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoid N] {f : α →₀ M} {g : α → M → β →₀ N} :
    (f.sum g).support ⊆ f.support.biUnion fun a => (g a (f a)).support := by sorry

theorem support_finset_sum [DecidableEq β] [AddCommMonoid M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).support ⊆ s.biUnion fun x => (f x).support := by
  rw [← Finset.sup_eq_biUnion]
  induction s using Finset.cons_induction_on with
  | h₁ => rfl
  | h₂ _ ih =>
    rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)

@[simp]
theorem sum_zero [Zero M] [AddCommMonoid N] {f : α →₀ M} : (f.sum fun _ _ => (0 : N)) = 0 :=
  Finset.sum_const_zero

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem prod_inv [Zero M] [CommGroup G] {f : α →₀ M} {h : α → M → G} :
    (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[target, simp]
theorem sum_sub [Zero M] [AddCommGroup G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
    (f.sum fun a b => h₁ a b - h₂ a b) = f.sum h₁ - f.sum h₂ :=
  sorry
@[to_additive
      "Taking the product under `h` is an additive homomorphism of finsupps,  if `h` is an
      additive homomorphism on the support. This is a more general version of
      `Finsupp.sum_add_index'`; the latter has simpler hypotheses."]
theorem prod_add_index [DecidableEq α] [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    {h : α → M → N} (h_zero : ∀ a ∈ f.support ∪ g.support, h a 0 = 1)
    (h_add : ∀ a ∈ f.support ∪ g.support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by
  rw [Finsupp.prod_of_support_subset f subset_union_left h h_zero,
    Finsupp.prod_of_support_subset g subset_union_right h h_zero, ←
    Finset.prod_mul_distrib, Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact Finset.prod_congr rfl fun x hx => by apply h_add x hx

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `Finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      "Taking the sum under `h` is an additive homomorphism of finsupps,if `h` is an additive
      homomorphism. This is a more specific version of `Finsupp.sum_add_index` with simpler
      hypotheses."]
@[target]
theorem prod_add_index' [AddZeroClass M] [CommMonoid N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).prod h = f.prod h * g.prod h := by sorry

@[simp]
theorem sum_hom_add_index [AddZeroClass M] [AddCommMonoid N] {f g : α →₀ M} (h : α → M →+ N) :
    ((f + g).sum fun x => h x) = (f.sum fun x => h x) + g.sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[target, simp]
theorem prod_hom_add_index [AddZeroClass M] [CommMonoid N] {f g : α →₀ M}
    (h : α → Multiplicative M →* N) :
    ((f + g).prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.prod fun a b => h a (Multiplicative.ofAdd b)) *
        g.prod fun a b => h a (Multiplicative.ofAdd b) :=
  sorry
def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where
  toFun F :=
    { toFun := fun f ↦ f.sum fun x ↦ F x
      map_zero' := Finset.sum_empty
      map_add' := fun _ _ => sum_add_index' (fun x => (F x).map_zero) fun x => (F x).map_add }
  invFun F x := F.comp (singleAddHom x)
  left_inv F := by
    ext
    simp [singleAddHom]
  right_inv F := by
    ext
    simp [singleAddHom, AddMonoidHom.comp, Function.comp_def]
  map_add' F G := by
    ext x
    exact sum_add

@[simp]
theorem liftAddHom_apply [AddCommMonoid M] [AddCommMonoid N] (F : α → M →+ N) (f : α →₀ M) :
    (liftAddHom (α := α) (M := M) (N := N)) F f = f.sum fun x => F x :=
  rfl

@[target, simp]
theorem liftAddHom_symm_apply [AddCommMonoid M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α) :
    (liftAddHom (α := sorry

theorem liftAddHom_symm_apply_apply [AddCommMonoid M] [AddCommMonoid N] (F : (α →₀ M) →+ N) (x : α)
    (y : M) : (liftAddHom (α := α) (M := M) (N := N)).symm F x y = F (single x y) :=
  rfl

@[target, simp]
theorem liftAddHom_singleAddHom [AddCommMonoid M] :
    (liftAddHom (α := sorry

@[simp]
theorem sum_single [AddCommMonoid M] (f : α →₀ M) : f.sum single = f :=
  DFunLike.congr_fun liftAddHom_singleAddHom f

/-- The `Finsupp` version of `Finset.univ_sum_single` -/
@[target, simp]
theorem univ_sum_single [Fintype α] [AddCommMonoid M] (f : α →₀ M) :
    ∑ a : α, single a (f a) = f := by sorry

@[simp]
theorem univ_sum_single_apply [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single i m j = m := by
  classical rw [single, coe_mk, Finset.sum_pi_single']
  simp

@[target, simp]
theorem univ_sum_single_apply' [AddCommMonoid M] [Fintype α] (i : α) (m : M) :
    ∑ j : α, single j m i = m := by sorry


@[target]
theorem equivFunOnFinite_symm_eq_sum [Fintype α] [AddCommMonoid M] (f : α → M) :
    equivFunOnFinite.symm f = ∑ a, Finsupp.single a (f a) := by sorry

theorem liftAddHom_apply_single [AddCommMonoid M] [AddCommMonoid N] (f : α → M →+ N) (a : α)
    (b : M) : (liftAddHom (α := α) (M := M) (N := N)) f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
theorem liftAddHom_comp_single [AddCommMonoid M] [AddCommMonoid N] (f : α → M →+ N) (a : α) :
    ((liftAddHom (α := α) (M := M) (N := N)) f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => liftAddHom_apply_single f a b

@[target]
theorem comp_liftAddHom [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] (g : N →+ P)
    (f : α → M →+ N) :
    g.comp ((liftAddHom (α := sorry

@[target]
theorem sum_sub_index [AddCommGroup β] [AddCommGroup γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).sum h = f.sum h - g.sum h :=
  sorry

@[to_additive]
theorem prod_embDomain [Zero M] [CommMonoid N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).prod g = v.prod fun a b => g (f a) b := by
  rw [prod, prod, support_embDomain, Finset.prod_map]
  simp_rw [embDomain_apply]

@[target, to_additive]
theorem prod_finset_sum_index [AddCommMonoid M] [CommMonoid N] {s : Finset ι} {g : ι → α →₀ M}
    {h : α → M → N} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h :=
  sorry

@[target, to_additive]
theorem prod_sum_index [AddCommMonoid M] [AddCommMonoid N] [CommMonoid P] {f : α →₀ M}
    {g : α → M → β →₀ N} {h : β → N → P} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.sum g).prod h = f.prod fun a b => (g a b).prod h :=
  sorry

@[target]
theorem multiset_sum_sum_index [AddCommMonoid M] [AddCommMonoid N] (f : Multiset (α →₀ M))
    (h : α → M → N) (h₀ : ∀ a, h a 0 = 0)
    (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.sum.sum h = (f.map fun g : α →₀ M => g.sum h).sum :=
  sorry

theorem support_sum_eq_biUnion {α : Type*} {ι : Type*} {M : Type*} [DecidableEq α]
    [AddCommMonoid M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).support (g i₂).support) :
    (∑ i ∈ s, g i).support = s.biUnion fun i => (g i).support := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi
    simp only [hi, sum_insert, not_false_iff, biUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs, Finset.disjoint_biUnion_right]
    intro j hj
    exact h _ _ (ne_of_mem_of_not_mem hj hi).symm

@[target]
theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.sum h) = f.sum fun a b => (h a b).map m :=
  sorry

@[target]
theorem multiset_sum_sum [Zero M] [AddCommMonoid N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.sum h) = f.sum fun a b => Multiset.sum (h a b) :=
  sorry
@[to_additive
      "For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`
      over `f1` and `f2` equals the sum of `g` over `f1 + f2`"]
@[target]
theorem prod_add_index_of_disjoint [AddCommMonoid M] {f1 f2 : α →₀ M}
    (hd : Disjoint f1.support f2.support) {β : Type*} [CommMonoid β] (g : α → M → β) :
    (f1 + f2).prod g = f1.prod g * f2.prod g := by sorry

theorem prod_dvd_prod_of_subset_of_dvd [AddCommMonoid M] [CommMonoid N] {f1 f2 : α →₀ M}
    {g1 g2 : α → M → N} (h1 : f1.support ⊆ f2.support)
    (h2 : ∀ a : α, a ∈ f1.support → g1 a (f1 a) ∣ g2 a (f2 a)) : f1.prod g1 ∣ f2.prod g2 := by
  classical
    simp only [Finsupp.prod, Finsupp.prod_mul]
    rw [← sdiff_union_of_subset h1, prod_union sdiff_disjoint]
    apply dvd_mul_of_dvd_right
    apply prod_dvd_prod_of_dvd
    exact h2

lemma indicator_eq_sum_attach_single [AddCommMonoid M] {s : Finset α} (f : ∀ a ∈ s, M) :
    indicator s f = ∑ x ∈ s.attach, single ↑x (f x x.2) := by
  rw [← sum_single (indicator s f), sum, sum_subset (support_indicator_subset _ _), ← sum_attach]
  · refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [indicator_of_mem]
  · intro i _ hi
    rw [not_mem_support_iff.mp hi, single_zero]

@[target]
lemma indicator_eq_sum_single [AddCommMonoid M] (s : Finset α) (f : α → M) :
    indicator s (fun x _ ↦ f x) = ∑ x ∈ s, single x (f x) :=
  sorry

@[to_additive (attr := simp)]
lemma prod_indicator_index_eq_prod_attach [Zero M] [CommMonoid N]
    {s : Finset α} (f : ∀ a ∈ s, M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s f).prod h = ∏ x ∈ s.attach, h ↑x (f x x.2) := by
  rw [prod_of_support_subset _ (support_indicator_subset _ _) h h_zero, ← prod_attach]
  refine Finset.prod_congr rfl (fun _ _ => ?_)
  rw [indicator_of_mem]

@[to_additive (attr := simp)]
lemma prod_indicator_index [Zero M] [CommMonoid N]
    {s : Finset α} (f : α → M) {h : α → M → N} (h_zero : ∀ a ∈ s, h a 0 = 1) :
    (indicator s (fun x _ ↦ f x)).prod h = ∏ x ∈ s, h x (f x) :=
  (prod_indicator_index_eq_prod_attach _ h_zero).trans <| prod_attach _ fun x ↦ h x (f x)

lemma sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

@[target]
lemma sum_cons' [AddCommMonoid M] [AddCommMonoid N] (n : ℕ) (σ : Fin n →₀ M) (i : M)
    (f : Fin (n+1) → M → N) (h : ∀ x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by sorry

@[target, to_additive]
lemma prod_mul_eq_prod_mul_of_exists [Zero M] [CommMonoid N]
    {f : α →₀ M} {g : α → M → N} {n₁ n₂ : N}
    (a : α) (ha : a ∈ f.support)
    (h : g a (f a) * n₁ = g a (f a) * n₂) :
    f.prod g * n₁ = f.prod g * n₂ := by sorry

end Finsupp

theorem Finset.sum_apply' : (∑ k ∈ s, f k) i = ∑ k ∈ s, f k i :=
  map_sum (Finsupp.applyAddHom i) f s

theorem Finsupp.sum_apply' : g.sum k x = g.sum fun i b => k i b x :=
  Finset.sum_apply _ _ _

theorem Finsupp.sum_sum_index' (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y) :
    (∑ x ∈ s, f x).sum t = ∑ x ∈ s, (f x).sum t := by
  classical
  exact Finset.induction_on s rfl fun a s has ih => by
    simp_rw [Finset.sum_insert has, Finsupp.sum_add_index' h0 h1, ih]

section

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

theorem Finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
    s.sum f * b = s.sum fun a c => f a c * b := by simp only [Finsupp.sum, Finset.sum_mul]

@[target]
theorem Finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
    b * s.sum f = s.sum fun a c => b * f a c := by sorry

@[simp] lemma Multiset.card_finsuppSum [Zero M] (f : ι →₀ M) (g : ι → M → Multiset α) :
    card (f.sum g) = f.sum fun i m ↦ card (g i m) := map_finsupp_sum cardHom ..

namespace Nat

/-- If `0 : ℕ` is not in the support of `f : ℕ →₀ ℕ` then `0 < ∏ x ∈ f.support, x ^ (f x)`. -/
theorem prod_pow_pos_of_zero_not_mem_support {f : ℕ →₀ ℕ} (nhf : 0 ∉ f.support) :
    0 < f.prod (· ^ ·) :=
  Nat.pos_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun _ hf =>
    pow_ne_zero _ fun H => by subst H; exact nhf hf

end Nat
