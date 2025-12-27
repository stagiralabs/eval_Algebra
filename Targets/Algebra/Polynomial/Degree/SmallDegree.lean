import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Nat.WithBot

/-!
# Results on polynomials of specific small degrees
-/

open Finsupp Finset

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

theorem eq_X_add_C_of_degree_le_one (h : degree p ≤ 1) : p = C (p.coeff 1) * X + C (p.coeff 0) :=
  ext fun n =>
    Nat.casesOn n (by simp) fun n =>
      Nat.casesOn n (by simp [coeff_C]) fun m => by
        -- Porting note: `by decide` → `Iff.mpr ..`
        have : degree p < m.succ.succ := lt_of_le_of_lt h
          (Iff.mpr WithBot.coe_lt_coe <| Nat.succ_lt_succ <| Nat.zero_lt_succ m)
        simp [coeff_eq_zero_of_degree_lt this, coeff_C, Nat.succ_ne_zero, coeff_X, Nat.succ_inj',
          @eq_comm ℕ 0]

@[target]
theorem eq_X_add_C_of_degree_eq_one (h : degree p = 1) :
    p = C p.leadingCoeff * X + C (p.coeff 0) :=
  sorry

theorem eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) :=
  eq_X_add_C_of_degree_le_one <| degree_le_of_natDegree_le h

@[target]
theorem Monic.eq_X_add_C (hm : p.Monic) (hnd : p.natDegree = 1) : p = X + C (p.coeff 0) := by sorry

@[target]
theorem exists_eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) : ∃ a b, p = C a * X + C b :=
  sorry

end Semiring

section Semiring

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem zero_le_degree_iff : 0 ≤ degree p ↔ p ≠ 0 := by
  rw [← not_lt, Nat.WithBot.lt_zero_iff, degree_eq_bot]

@[target]
theorem ne_zero_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : p ≠ 0 :=
  sorry

@[target]
theorem le_natDegree_of_coe_le_degree (hdeg : ↑n ≤ p.degree) : n ≤ p.natDegree :=
  sorry

@[target]
theorem degree_linear_le : degree (C a * X + C b) ≤ 1 :=
  sorry

theorem degree_linear_lt : degree (C a * X + C b) < 2 :=
  degree_linear_le.trans_lt <| WithBot.coe_lt_coe.mpr one_lt_two

@[simp]
theorem degree_linear (ha : a ≠ 0) : degree (C a * X + C b) = 1 := by
  rw [degree_add_eq_left_of_degree_lt <| degree_C_lt_degree_C_mul_X ha, degree_C_mul_X ha]

@[target]
theorem natDegree_linear_le : natDegree (C a * X + C b) ≤ 1 :=
  sorry

@[target]
theorem natDegree_linear (ha : a ≠ 0) : natDegree (C a * X + C b) = 1 := by sorry

@[target, simp]
theorem leadingCoeff_linear (ha : a ≠ 0) : leadingCoeff (C a * X + C b) = a := by sorry

theorem degree_quadratic_le : degree (C a * X ^ 2 + C b * X + C c) ≤ 2 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 2 a)
      (le_trans degree_linear_le <| WithBot.coe_le_coe.mpr one_le_two)

@[target]
theorem degree_quadratic_lt : degree (C a * X ^ 2 + C b * X + C c) < 3 :=
  sorry

@[target]
theorem degree_linear_lt_degree_C_mul_X_sq (ha : a ≠ 0) :
    degree (C b * X + C c) < degree (C a * X ^ 2) := by sorry

@[simp]
theorem degree_quadratic (ha : a ≠ 0) : degree (C a * X ^ 2 + C b * X + C c) = 2 := by
  rw [add_assoc, degree_add_eq_left_of_degree_lt <| degree_linear_lt_degree_C_mul_X_sq ha,
    degree_C_mul_X_pow 2 ha]
  rfl

theorem natDegree_quadratic_le : natDegree (C a * X ^ 2 + C b * X + C c) ≤ 2 :=
  natDegree_le_of_degree_le degree_quadratic_le

theorem natDegree_quadratic (ha : a ≠ 0) : natDegree (C a * X ^ 2 + C b * X + C c) = 2 :=
  natDegree_eq_of_degree_eq_some <| degree_quadratic ha

@[target, simp]
theorem leadingCoeff_quadratic (ha : a ≠ 0) : leadingCoeff (C a * X ^ 2 + C b * X + C c) = a := by sorry

theorem degree_cubic_le : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 := by
  simpa only [add_assoc] using
    degree_add_le_of_degree_le (degree_C_mul_X_pow_le 3 a)
      (le_trans degree_quadratic_le <| WithBot.coe_le_coe.mpr <| Nat.le_succ 2)

@[target]
theorem degree_cubic_lt : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) < 4 :=
  sorry

theorem degree_quadratic_lt_degree_C_mul_X_cb (ha : a ≠ 0) :
    degree (C b * X ^ 2 + C c * X + C d) < degree (C a * X ^ 3) := by
  simpa only [degree_C_mul_X_pow 3 ha] using degree_quadratic_lt

@[target, simp]
theorem degree_cubic (ha : a ≠ 0) : degree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 := by sorry

theorem natDegree_cubic_le : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) ≤ 3 :=
  natDegree_le_of_degree_le degree_cubic_le

theorem natDegree_cubic (ha : a ≠ 0) : natDegree (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = 3 :=
  natDegree_eq_of_degree_eq_some <| degree_cubic ha

@[simp]
theorem leadingCoeff_cubic (ha : a ≠ 0) :
    leadingCoeff (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d) = a := by
  rw [add_assoc, add_assoc, ← add_assoc (C b * X ^ 2), add_comm,
    leadingCoeff_add_of_degree_lt <| degree_quadratic_lt_degree_C_mul_X_cb ha,
    leadingCoeff_C_mul_X_pow]

end Semiring

end Polynomial
