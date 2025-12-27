import VerifiedAgora.tagger
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

Results about squarefree natural numbers are proved in `Data.Nat.Squarefree`.

## Main Definitions
 - `Squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_emultiplicity_le_one`: `x` is `Squarefree` iff for every `y`, either
  `emultiplicity y x ≤ 1` or `IsUnit y`.
 - `UniqueFactorizationMonoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/


variable {R : Type*}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoid R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x

@[target]
theorem IsRelPrime.of_squarefree_mul [CommMonoid R] {m n : R} (h : Squarefree (m * n)) :
    IsRelPrime m n := sorry

@[target, simp]
theorem IsUnit.squarefree [CommMonoid R] {x : R} (h : IsUnit x) : Squarefree x := sorry

theorem squarefree_one [CommMonoid R] : Squarefree (1 : R) :=
  isUnit_one.squarefree

@[target, simp]
theorem not_squarefree_zero [MonoidWithZero R] [Nontrivial R] : ¬Squarefree (0 : R) := by sorry

theorem Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) :
    m ≠ 0 := by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]
theorem Irreducible.squarefree [CommMonoid R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.isUnit_or_isUnit hz with (hu | hu)
  · exact hu
  · apply isUnit_of_mul_isUnit_left hu

@[target, simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  sorry

theorem Squarefree.of_mul_left [Monoid R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m :=
  fun p hp => hmn p (dvd_mul_of_dvd_left hp n)

theorem Squarefree.of_mul_right [CommMonoid R] {m n : R} (hmn : Squarefree (m * n)) :
    Squarefree n := fun p hp => hmn p (dvd_mul_of_dvd_right hp m)

theorem Squarefree.squarefree_of_dvd [Monoid R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) :
    Squarefree x := fun _ h => hsq _ (h.trans hdvd)

theorem Squarefree.eq_zero_or_one_of_pow_of_not_isUnit [Monoid R] {x : R} {n : ℕ}
    (h : Squarefree (x ^ n)) (h' : ¬ IsUnit x) :
    n = 0 ∨ n = 1 := by
  contrapose! h'
  replace h' : 2 ≤ n := by omega
  have : x * x ∣ x ^ n := by rw [← sq]; exact pow_dvd_pow x h'
  exact h.squarefree_of_dvd this x (refl _)

theorem Squarefree.pow_dvd_of_pow_dvd [Monoid R] {x y : R} {n : ℕ}
    (hx : Squarefree y) (h : x ^ n ∣ y) : x ^ n ∣ x := by
  by_cases hu : IsUnit x
  · exact (hu.pow n).dvd
  · rcases (hx.squarefree_of_dvd h).eq_zero_or_one_of_pow_of_not_isUnit hu with rfl | rfl <;> simp

section SquarefreeGcdOfSquarefree

variable {α : Type*} [CancelCommMonoidWithZero α] [GCDMonoid α]

theorem Squarefree.gcd_right (a : α) {b : α} (hb : Squarefree b) : Squarefree (gcd a b) :=
  hb.squarefree_of_dvd (gcd_dvd_right _ _)

theorem Squarefree.gcd_left {a : α} (b : α) (ha : Squarefree a) : Squarefree (gcd a b) :=
  ha.squarefree_of_dvd (gcd_dvd_left _ _)

end SquarefreeGcdOfSquarefree

@[target]
theorem squarefree_iff_emultiplicity_le_one [CommMonoid R] (r : R) :
    Squarefree r ↔ ∀ x : R, emultiplicity x r ≤ 1 ∨ IsUnit x := by sorry

@[deprecated (since := "2024-11-30")]
alias multiplicity.squarefree_iff_emultiplicity_le_one := squarefree_iff_emultiplicity_le_one

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem squarefree_iff_no_irreducibles {x : R} (hx₀ : x ≠ 0) :
    Squarefree x ↔ ∀ p, Irreducible p → ¬ (p * p ∣ x) := by
  refine ⟨fun h p hp hp' ↦ hp.not_unit (h p hp'), fun h d hd ↦ by_contra fun hdu ↦ ?_⟩
  have hd₀ : d ≠ 0 := ne_zero_of_dvd_ne_zero (ne_zero_of_dvd_ne_zero hx₀ hd) (dvd_mul_left d d)
  obtain ⟨p, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd₀
  exact h p irr ((mul_dvd_mul dvd dvd).trans hd)

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne r 0 with (rfl | hr)
    · exact .inl (by simpa using h)
    · exact .inr ((squarefree_iff_no_irreducibles hr).mpr h)
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
    intro x hx t
    exact hx.not_unit (h x t)

@[target]
theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by sorry

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R}
    (hr : ∃ x : R, Irreducible x) : Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [hr, not_true, false_or, and_false]

end Irreducible

section IsRadical

section
variable [CommMonoidWithZero R] [DecompositionMonoid R]

theorem Squarefree.isRadical {x : R} (hx : Squarefree x) : IsRadical x :=
  (isRadical_iff_pow_one_lt 2 one_lt_two).2 fun y hy ↦ by
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul (sq y ▸ hy)
    exact (IsRelPrime.of_squarefree_mul hx).mul_dvd ha hb

@[target]
theorem Squarefree.dvd_pow_iff_dvd {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) :
    x ∣ y ^ n ↔ x ∣ y := sorry

variable [CancelCommMonoidWithZero R] {x y p d : R}

@[target]
theorem IsRadical.squarefree (h0 : x ≠ 0) (h : IsRadical x) : Squarefree x := by sorry

namespace Squarefree

@[target]
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_right {k : ℕ}
    (hx : Squarefree x) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ y := by sorry

@[target]
theorem pow_dvd_of_squarefree_of_pow_succ_dvd_mul_left {k : ℕ}
    (hy : Squarefree y) (hp : Prime p) (h : p ^ (k + 1) ∣ x * y) :
    p ^ k ∣ x := by sorry

variable [DecompositionMonoid R]

@[target]
theorem dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y := by sorry

theorem dvd_of_squarefree_of_mul_dvd_mul_left (hy : Squarefree y) (h : d * d ∣ x * y) : d ∣ x :=
  dvd_of_squarefree_of_mul_dvd_mul_right hy (mul_comm x y ▸ h)

end Squarefree

variable [DecompositionMonoid R]

/-- `x * y` is square-free iff `x` and `y` have no common factors and are themselves square-free. -/
@[target]
theorem squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime x y ∧ Squarefree x ∧ Squarefree y :=
  sorry

theorem isRadical_iff_squarefree_or_zero : IsRadical x ↔ Squarefree x ∨ x = 0 :=
  ⟨fun hx ↦ (em <| x = 0).elim .inr fun h ↦ .inl <| hx.squarefree h,
    Or.rec Squarefree.isRadical <| by
      rintro rfl
      rw [zero_isRadical_iff]
      infer_instance⟩

@[target]
theorem isRadical_iff_squarefree_of_ne_zero (h : x ≠ 0) : IsRadical x ↔ Squarefree x :=
  sorry

end IsRadical

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [UniqueFactorizationMonoid R]

@[target]
lemma _root_.exists_squarefree_dvd_pow_of_ne_zero {x : R} (hx : x ≠ 0) :
    ∃ (y : R) (n : ℕ), Squarefree y ∧ y ∣ x ∧ x ∣ y ^ n := by sorry

@[target]
theorem squarefree_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R}
    (x0 : x ≠ 0) : Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by sorry

end UniqueFactorizationMonoid

namespace Int

@[simp]
theorem squarefree_natAbs {n : ℤ} : Squarefree n.natAbs ↔ Squarefree n := by
  simp_rw [Squarefree, natAbs_surjective.forall, ← natAbs_mul, natAbs_dvd_natAbs,
    isUnit_iff_natAbs_eq, Nat.isUnit_iff]

@[target, simp]
theorem squarefree_natCast {n : ℕ} : Squarefree (n : ℤ) ↔ Squarefree n := by sorry

end Int
