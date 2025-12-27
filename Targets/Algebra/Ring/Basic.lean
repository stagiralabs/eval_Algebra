import VerifiedAgora.tagger
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Ring.Defs

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Algebra.Group.Basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Algebra.Ring.Defs`.
-/

variable {R : Type*}

open Function

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps (config := .asFn)]
def mulLeft [Distrib R] (r : R) : AddHom R R where
  toFun := (r * ·)
  map_add' := mul_add r

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps (config := .asFn)]
def mulRight [Distrib R] (r : R) : AddHom R R where
  toFun a := a * r
  map_add' _ _ := add_mul _ _ r

end AddHom

namespace AddMonoidHom

/-- Left multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
def mulLeft [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun := (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r

@[simp]
theorem coe_mulLeft [NonUnitalNonAssocSemiring R] (r : R) :
    (mulLeft r : R → R) = HMul.hMul r :=
  rfl

/-- Right multiplication by an element of a (semi)ring is an `AddMonoidHom` -/
def mulRight [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r

@[target, simp]
theorem coe_mulRight [NonUnitalNonAssocSemiring R] (r : R) :
    (mulRight r) = (· * r) :=
  sorry

@[target]
theorem mulRight_apply [NonUnitalNonAssocSemiring R] (a r : R) :
    mulRight r a = a * r :=
  sorry

end AddMonoidHom

section HasDistribNeg

section Mul

variable {α : Type*} [Mul α] [HasDistribNeg α]

open MulOpposite

instance instHasDistribNeg : HasDistribNeg αᵐᵒᵖ where
  neg_mul _ _ := unop_injective <| mul_neg _ _
  mul_neg _ _ := unop_injective <| neg_mul _ _

end Mul

section Group

variable {α : Type*} [Group α] [HasDistribNeg α]

@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_neg, inv_mul_cancel]

end Group

end HasDistribNeg

section NonUnitalCommRing

variable {α : Type*} [NonUnitalCommRing α]

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
@[target]
theorem vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by sorry

end NonUnitalCommRing

theorem succ_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))

@[target]
theorem pred_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := sorry

section NoZeroDivisors

variable (α)

@[target]
lemma IsLeftCancelMulZero.to_noZeroDivisors [NonUnitalNonAssocSemiring α]
    [IsLeftCancelMulZero α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {x _} h :=
    sorry

lemma IsRightCancelMulZero.to_noZeroDivisors [NonUnitalNonAssocSemiring α]
    [IsRightCancelMulZero α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ y} h :=
    or_iff_not_imp_right.mpr fun ne ↦ mul_right_cancel₀ ne ((zero_mul y).symm ▸ h)

instance (priority := 100) NoZeroDivisors.to_isCancelMulZero
    [NonUnitalNonAssocRing α] [NoZeroDivisors α] :
    IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha h := by
    rw [← sub_eq_zero, ← mul_sub] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
  mul_right_cancel_of_ne_zero hb h := by
    rw [← sub_eq_zero, ← sub_mul] at h
    exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb)

/-- In a ring, `IsCancelMulZero` and `NoZeroDivisors` are equivalent. -/
@[target]
lemma isCancelMulZero_iff_noZeroDivisors [NonUnitalNonAssocRing α] :
    IsCancelMulZero α ↔ NoZeroDivisors α :=
  sorry

@[target]
lemma NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
    IsDomain α :=
  sorry

instance (priority := 100) IsDomain.to_noZeroDivisors [Semiring α] [IsDomain α] :
    NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α

instance Subsingleton.to_isCancelMulZero [Mul α] [Zero α] [Subsingleton α] : IsCancelMulZero α where
  mul_right_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

instance Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero _ := .inl (Subsingleton.eq_zero _)

@[target]
lemma isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] :
    IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α :=
  sorry

@[target]
lemma isCancelMulZero_iff_isDomain_or_subsingleton [Semiring α] :
    IsCancelMulZero α ↔ IsDomain α ∨ Subsingleton α := by sorry

@[target]
lemma isDomain_iff_noZeroDivisors_and_nontrivial [Ring α] :
    IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α := by sorry

@[target]
lemma noZeroDivisors_iff_isDomain_or_subsingleton [Ring α] :
    NoZeroDivisors α ↔ IsDomain α ∨ Subsingleton α := by sorry

end NoZeroDivisors

section DivisionMonoid
variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

lemma one_div_neg_one_eq_neg_one : (1 : R) / -1 = -1 :=
  have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

@[target]
lemma one_div_neg_eq_neg_one_div (a : R) : 1 / -a = -(1 / a) :=
  sorry

lemma div_neg_eq_neg_div (a b : R) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

lemma neg_div (a b : R) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[target, field_simps]
lemma neg_div' (a b : R) : -(b / a) = -b / a := by sorry

@[target, simp]
lemma neg_div_neg_eq (a b : R) : -a / -b = a / b := by sorry

@[target]
lemma neg_inv : -a⁻¹ = (-a)⁻¹ := by sorry

@[target]
lemma div_neg (a : R) : a / -b = -(a / b) := by sorry

@[target]
lemma inv_neg : (-a)⁻¹ = -a⁻¹ := by sorry

lemma inv_neg_one : (-1 : R)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid
