import VerifiedAgora.tagger
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Int.GCD

/-!
# ℕ and ℤ are normalized GCD monoids.

## Main statements

* ℕ is a `GCDMonoid`
* ℕ is a `NormalizedGCDMonoid`
* ℤ is a `NormalizationMonoid`
* ℤ is a `GCDMonoid`
* ℤ is a `NormalizedGCDMonoid`

## Tags
natural numbers, integers, normalization monoid, gcd monoid, greatest common divisor
-/

assert_not_exists OrderedCommMonoid

/-- `ℕ` is a gcd_monoid. -/
instance : GCDMonoid ℕ where
  gcd := Nat.gcd
  lcm := Nat.lcm
  gcd_dvd_left := Nat.gcd_dvd_left
  gcd_dvd_right := Nat.gcd_dvd_right
  dvd_gcd := Nat.dvd_gcd
  gcd_mul_lcm a b := by rw [Nat.gcd_mul_lcm]; rfl
  lcm_zero_left := Nat.lcm_zero_left
  lcm_zero_right := Nat.lcm_zero_right

@[target] theorem gcd_eq_nat_gcd (m n : ℕ) : gcd m n = Nat.gcd m n := by sorry


@[target] theorem lcm_eq_nat_lcm (m n : ℕ) : lcm m n = Nat.lcm m n := by sorry


instance : NormalizedGCDMonoid ℕ :=
  { (inferInstance : GCDMonoid ℕ),
    (inferInstance : NormalizationMonoid ℕ) with
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

namespace Int

section NormalizationMonoid

instance normalizationMonoid : NormalizationMonoid ℤ where
  normUnit a := if 0 ≤ a then 1 else -1
  normUnit_zero := if_pos le_rfl
  normUnit_mul {a b} hna hnb := by
    rcases hna.lt_or_lt with ha | ha <;> rcases hnb.lt_or_lt with hb | hb <;>
      simp [Int.mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le]
  normUnit_coe_units u :=
    (units_eq_one_or u).elim (fun eq => eq.symm ▸ if_pos Int.one_nonneg) fun eq =>
      eq.symm ▸ if_neg (not_le_of_gt <| show (-1 : ℤ) < 0 by decide)

theorem normUnit_eq (z : ℤ) : normUnit z = if 0 ≤ z then 1 else -1 := rfl

@[target] theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z := by
  sorry


@[target] theorem normalize_of_nonpos {z : ℤ} (h : z ≤ 0) : normalize z = -z := by
  sorry


@[target] theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n := by sorry


@[target] theorem abs_eq_normalize (z : ℤ) : |z| = normalize z := by
  sorry


@[target] theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z := by
  sorry


@[target] theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z := by sorry


@[target] theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a = b := by sorry


end NormalizationMonoid

section GCDMonoid

instance : GCDMonoid ℤ where
  gcd a b := Int.gcd a b
  lcm a b := Int.lcm a b
  gcd_dvd_left _ _ := Int.gcd_dvd_left
  gcd_dvd_right _ _ := Int.gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by
    rw [← Int.ofNat_mul, gcd_mul_lcm, natCast_natAbs, abs_eq_normalize]
    exact normalize_associated (a * b)
  lcm_zero_left _ := natCast_eq_zero.2 <| Nat.lcm_zero_left _
  lcm_zero_right _ := natCast_eq_zero.2 <| Nat.lcm_zero_right _

instance : NormalizedGCDMonoid ℤ :=
  { Int.normalizationMonoid,
    (inferInstance : GCDMonoid ℤ) with
    normalize_gcd := fun _ _ => normalize_coe_nat _
    normalize_lcm := fun _ _ => normalize_coe_nat _ }

@[target] theorem coe_gcd (i j : ℤ) : ↑(Int.gcd i j) = GCDMonoid.gcd i j := by sorry


@[target] theorem coe_lcm (i j : ℤ) : ↑(Int.lcm i j) = GCDMonoid.lcm i j := by sorry


@[target] theorem natAbs_gcd (i j : ℤ) : natAbs (GCDMonoid.gcd i j) = Int.gcd i j := by sorry


@[target] theorem natAbs_lcm (i j : ℤ) : natAbs (GCDMonoid.lcm i j) = Int.lcm i j := by sorry


end GCDMonoid

@[target] theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ) (_ : IsUnit u), (Int.natAbs a : ℤ) = u * a := by
  sorry


theorem gcd_eq_natAbs {a b : ℤ} : Int.gcd a b = Nat.gcd a.natAbs b.natAbs :=
  rfl
end Int

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associatesIntEquivNat : Associates ℤ ≃ ℕ := by
  sorry


theorem Int.associated_natAbs (k : ℤ) : Associated k k.natAbs :=
  associated_of_dvd_dvd (Int.dvd_natCast.mpr dvd_rfl) (Int.natAbs_dvd.mpr dvd_rfl)

theorem Int.associated_iff_natAbs {a b : ℤ} : Associated a b ↔ a.natAbs = b.natAbs := by
  rw [← dvd_dvd_iff_associated, ← Int.natAbs_dvd_natAbs, ← Int.natAbs_dvd_natAbs,
    dvd_dvd_iff_associated]
  exact associated_iff_eq

theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b := by
  rw [Int.associated_iff_natAbs]
  exact Int.natAbs_eq_natAbs_iff
