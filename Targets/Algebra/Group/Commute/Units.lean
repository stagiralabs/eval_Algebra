import VerifiedAgora.tagger
/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about commuting pairs of elements involving units.

-/

assert_not_exists MonoidWithZero DenselyOrdered

variable {M : Type*}

section Monoid
variable [Monoid M] {n : ℕ} {a b : M} {u u₁ u₂ : Mˣ}

namespace Commute

@[target, to_additive]
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  sorry

@[to_additive (attr := simp)]
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff

@[to_additive]
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left

@[to_additive (attr := simp)]
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff

@[target, to_additive]
theorem units_val : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  sorry

@[to_additive]
theorem units_of_val : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_val

@[to_additive (attr := simp)]
theorem units_val_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_val_iff

end Commute

/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the left summand is
an additive unit."]
def Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv]

/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the right summand
is an additive unit."]
def Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.eq ▸ hu) hc.symm

@[to_additive]
theorem Commute.isUnit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b :=
  ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).isUnit, (u.rightOfMul a b hu.symm h).isUnit⟩,
  fun H => H.1.mul H.2⟩

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
lemma Commute.units_zpow_right (h : Commute a u) (m : ℤ) : Commute a ↑(u ^ m) :=
  SemiconjBy.units_zpow_right h m

@[to_additive (attr := simp)]
lemma Commute.units_zpow_left (h : Commute ↑u a) (m : ℤ) : Commute ↑(u ^ m) a :=
  (h.symm.units_zpow_right m).symm

/-- If a natural power of `x` is a unit, then `x` is a unit. -/
@[to_additive "If a natural multiple of `x` is an additive unit, then `x` is an additive unit."]
def Units.ofPow (u : Mˣ) (x : M) {n : ℕ} (hn : n ≠ 0) (hu : x ^ n = u) : Mˣ :=
  u.leftOfMul x (x ^ (n - 1))
    (by rwa [← _root_.pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero hn)])
    (Commute.self_pow _ _)

@[to_additive (attr := simp)] lemma isUnit_pow_iff (hn : n ≠ 0) : IsUnit (a ^ n) ↔ IsUnit a :=
  ⟨fun ⟨u, hu⟩ ↦ (u.ofPow a hn hu.symm).isUnit, IsUnit.pow n⟩

@[target, to_additive]
lemma isUnit_pow_succ_iff : IsUnit (a ^ (n + 1)) ↔ IsUnit a := sorry

@[target]
lemma isUnit_pow_iff_of_not_isUnit (hx : ¬ IsUnit a) {n : ℕ} :
    IsUnit (a ^ n) ↔ n = 0 := by sorry
@[to_additive (attr := simps!) "If `n • x = 0`, `n ≠ 0`, then `x` is an additive unit."]
def Units.ofPowEqOne (a : M) (n : ℕ) (ha : a ^ n = 1) (hn : n ≠ 0) : Mˣ := Units.ofPow 1 a hn ha

@[target, to_additive (attr := sorry

@[to_additive]
lemma IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n ≠ 0) : IsUnit a :=
  (Units.ofPowEqOne _ n ha hn).isUnit

@[deprecated (since := "2025-02-03")] alias isUnit_ofPowEqOne := IsUnit.of_pow_eq_one
@[deprecated (since := "2025-02-03")] alias isAddUnit_ofNSMulEqZero := IsAddUnit.of_nsmul_eq_zero

end Monoid

section DivisionMonoid
variable [DivisionMonoid M] {a b c d : M}

@[target, to_additive]
lemma Commute.div_eq_div_iff_of_isUnit (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by sorry

end DivisionMonoid
