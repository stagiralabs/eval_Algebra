import VerifiedAgora.tagger
/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import Mathlib.Algebra.Order.Archimedean.Hom
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an isomorphism
preserving these properties to the reals. This is `LinearOrderedField.inducedOrderRingIso` for `ℚ`.
Moreover this isomorphism is unique.

We introduce definitions of conditionally complete linear ordered fields, and show all such are
archimedean. We also construct the natural map from a `LinearOrderedField` to such a field.

## Main definitions

* `ConditionallyCompleteLinearOrderedField`: A field satisfying the standard axiomatization of
  the real numbers, being a Dedekind complete and linear ordered field.
* `LinearOrderedField.inducedMap`: A (unique) map from any archimedean linear ordered field to a
  conditionally complete linear ordered field. Various bundlings are available.

## Main results

* `LinearOrderedField.uniqueOrderRingHom` : Uniqueness of `OrderRingHom`s from an archimedean
  linear ordered field to a conditionally complete linear ordered field.
* `LinearOrderedField.uniqueOrderRingIso` : Uniqueness of `OrderRingIso`s between two
  conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/
  who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

variable {F α β γ : Type*}

noncomputable section

open Function Rat Set

open scoped Pointwise

/-- A field which is both linearly ordered and conditionally complete with respect to the order.
This axiomatizes the reals. -/
-- @[protect_proj] -- Porting note: does not exist anymore
class ConditionallyCompleteLinearOrderedField (α : Type*) extends
    LinearOrderedField α, ConditionallyCompleteLinearOrder α

-- see Note [lower instance priority]
/-- Any conditionally complete linearly ordered field is archimedean. -/
instance (priority := 100) ConditionallyCompleteLinearOrderedField.to_archimedean
    [ConditionallyCompleteLinearOrderedField α] : Archimedean α :=
  archimedean_iff_nat_lt.2
    (by
      by_contra! h
      obtain ⟨x, h⟩ := h
      have := csSup_le _ _ (range_nonempty Nat.cast)
        (forall_mem_range.2 fun m =>
          le_sub_iff_add_le.2 <| le_csSup _ _ ⟨x, forall_mem_range.2 h⟩ ⟨m+1, Nat.cast_succ m⟩)
      linarith)

namespace LinearOrderedField

/-!
### Rational cut map

The idea is that a conditionally complete linear ordered field is fully characterized by its copy of
the rationals. Hence we define `LinearOrderedField.cutMap β : α → Set β` which sends `a : α` to the
"rationals in `β`" that are less than `a`.
-/


section CutMap

variable [LinearOrderedField α]

section DivisionRing

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
def cutMap (a : α) : Set β :=
  (Rat.cast : ℚ → β) '' {t | ↑t < a}

@[target]
theorem cutMap_mono (h : a₁ ≤ a₂) : cutMap β a₁ ⊆ cutMap β a₂ := sorry

variable {β}

@[target, simp]
theorem mem_cutMap_iff : b ∈ cutMap β a ↔ ∃ q : ℚ, (q : α) < a ∧ (q : β) = b := sorry

@[target]
theorem coe_mem_cutMap_iff [CharZero β] : (q : β) ∈ cutMap β a ↔ (q : α) < a :=
  sorry

@[target]
theorem cutMap_self (a : α) : cutMap α a = Iio a ∩ range (Rat.cast : ℚ → α) := by sorry

end DivisionRing

variable (β) [LinearOrderedField β] {a a₁ a₂ : α} {b : β} {q : ℚ}

theorem cutMap_coe (q : ℚ) : cutMap β (q : α) = Rat.cast '' {r : ℚ | (r : β) < q} := by
  simp_rw [cutMap, Rat.cast_lt]

variable [Archimedean α]

@[target]
theorem cutMap_nonempty (a : α) : (cutMap β a).Nonempty :=
  sorry

theorem cutMap_bddAbove (a : α) : BddAbove (cutMap β a) := by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact ⟨q, forall_mem_image.2 fun r hr => mod_cast (hq.trans' hr).le⟩

@[target]
theorem cutMap_add (a b : α) : cutMap β (a + b) = cutMap β a + cutMap β b := by sorry

end CutMap

/-!
### Induced map

`LinearOrderedField.cutMap` spits out a `Set β`. To get something in `β`, we now take the supremum.
-/


section InducedMap

variable (α β γ) [LinearOrderedField α] [ConditionallyCompleteLinearOrderedField β]
  [ConditionallyCompleteLinearOrderedField γ]

/-- The induced order preserving function from a linear ordered field to a conditionally complete
linear ordered field, defined by taking the Sup in the codomain of all the rationals less than the
input. -/
def inducedMap (x : α) : β :=
  sSup <| cutMap β x

variable [Archimedean α]

@[target]
theorem inducedMap_mono : Monotone (inducedMap α β) := sorry

@[target]
theorem inducedMap_rat (q : ℚ) : inducedMap α β (q : α) = q := by sorry

@[target, simp]
theorem inducedMap_zero : inducedMap α β 0 = 0 := sorry

@[target, simp]
theorem inducedMap_one : inducedMap α β 1 = 1 := sorry

variable {α β} {a : α} {b : β} {q : ℚ}

@[target]
theorem inducedMap_nonneg (ha : 0 ≤ a) : 0 ≤ inducedMap α β a :=
  sorry

@[target]
theorem coe_lt_inducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a := by sorry

@[target]
theorem lt_inducedMap_iff : b < inducedMap α β a ↔ ∃ q : ℚ, b < q ∧ (q : α) < a :=
  sorry

@[simp]
theorem inducedMap_self (b : β) : inducedMap β β b = b :=
  eq_of_forall_rat_lt_iff_lt fun _ => coe_lt_inducedMap_iff

variable (α β)

@[target, simp]
theorem inducedMap_inducedMap (a : α) : inducedMap β γ (inducedMap α β a) = inducedMap α γ a :=
  sorry

@[target]
theorem inducedMap_inv_self (b : β) : inducedMap γ β (inducedMap β γ b) = b := by sorry

theorem inducedMap_add (x y : α) :
    inducedMap α β (x + y) = inducedMap α β x + inducedMap α β y := by
  rw [inducedMap, cutMap_add]
  exact csSup_add (cutMap_nonempty β x) (cutMap_bddAbove β x) (cutMap_nonempty β y)
    (cutMap_bddAbove β y)

variable {α β}

/-- Preparatory lemma for `inducedOrderRingHom`. -/
@[target]
theorem le_inducedMap_mul_self_of_mem_cutMap (ha : 0 < a) (b : β) (hb : b ∈ cutMap β (a * a)) :
    b ≤ inducedMap α β a * inducedMap α β a := by sorry
theorem exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self (ha : 0 < a) (b : β)
    (hba : b < inducedMap α β a * inducedMap α β a) : ∃ c ∈ cutMap β (a * a), b < c := by
  obtain hb | hb := lt_or_le b 0
  · refine ⟨0, ?_, hb⟩
    rw [← Rat.cast_zero, coe_mem_cutMap_iff, Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine ⟨(q ^ 2 : ℚ), coe_mem_cutMap_iff.2 ?_, hbq⟩
  rw [pow_two] at hqa ⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := lt_inducedMap_iff.1 (lt_of_mul_self_lt_mul_self₀
    (inducedMap_nonneg ha.le) hqa)
  exact mul_self_lt_mul_self (mod_cast hq.le) (hqa'.trans' <| by assumption_mod_cast)

variable (α β)

/-- `inducedMap` as an additive homomorphism. -/
def inducedAddHom : α →+ β :=
  ⟨⟨inducedMap α β, inducedMap_zero α β⟩, inducedMap_add α β⟩

/-- `inducedMap` as an `OrderRingHom`. -/
@[simps!]
def inducedOrderRingHom : α →+*o β :=
  { AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero (inducedAddHom α β) (by
      suffices ∀ x, 0 < x → inducedAddHom α β (x * x) = inducedAddHom α β x * inducedAddHom α β x by
        intro x
        obtain h | rfl | h := lt_trichotomy x 0
        · convert this (-x) (neg_pos.2 h) using 1
          · rw [neg_mul, mul_neg, neg_neg]
          · simp_rw [AddMonoidHom.map_neg, neg_mul, mul_neg, neg_neg]
        · simp only [mul_zero, AddMonoidHom.map_zero]
        · exact this x h
        -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
        -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine fun x hx => csSup_eq_of_forall_le_of_forall_lt_exists_gt (cutMap_nonempty β _) ?_ ?_
      · exact le_inducedMap_mul_self_of_mem_cutMap hx
      · exact exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self hx)
      (two_ne_zero) (inducedMap_one _ _) with
    monotone' := inducedMap_mono _ _ }

/-- The isomorphism of ordered rings between two conditionally complete linearly ordered fields. -/
def inducedOrderRingIso : β ≃+*o γ :=
  { inducedOrderRingHom β γ with
    invFun := inducedMap γ β
    left_inv := inducedMap_inv_self _ _
    right_inv := inducedMap_inv_self _ _
    map_le_map_iff' := by
      dsimp
      refine ⟨fun h => ?_, fun h => inducedMap_mono _ _ h⟩
      convert inducedMap_mono γ β h <;>
      · rw [inducedOrderRingHom, AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero, inducedAddHom]
        dsimp
        rw [inducedMap_inv_self β γ _] }

@[target, simp]
theorem coe_inducedOrderRingIso : ⇑(inducedOrderRingIso β γ) = inducedMap β γ := sorry

@[simp]
theorem inducedOrderRingIso_symm : (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β := rfl

@[target, simp]
theorem inducedOrderRingIso_self : inducedOrderRingIso β β = OrderRingIso.refl β :=
  sorry

open OrderRingIso

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
instance uniqueOrderRingHom : Unique (α →+*o β) :=
  uniqueOfSubsingleton <| inducedOrderRingHom α β

/-- There is a unique ordered ring isomorphism between two conditionally complete linear ordered
fields. -/
instance uniqueOrderRingIso : Unique (β ≃+*o γ) :=
  uniqueOfSubsingleton <| inducedOrderRingIso β γ

end InducedMap

end LinearOrderedField

section Real

variable {R S : Type*} [OrderedRing R] [LinearOrderedRing S]

theorem ringHom_monotone (hR : ∀ r : R, 0 ≤ r → ∃ s : R, s ^ 2 = r) (f : R →+* S) : Monotone f :=
  (monotone_iff_map_nonneg f).2 fun r h => by
    obtain ⟨s, rfl⟩ := hR r h; rw [map_pow]; apply sq_nonneg

end Real
