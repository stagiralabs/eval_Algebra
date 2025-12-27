import VerifiedAgora.tagger
/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Prime and irreducible elements.

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`
(see `irreducible_iff_prime`), however this is not true in general.

## Main definitions
 * `Prime`: a prime element of a commutative monoid with zero
 * `Irreducible`: an irreducible element of a commutative monoid with zero

## Main results
 * `irreducible_iff_prime`: the two definitions are equivalent in a decomposition monoid.
-/

assert_not_exists OrderedCommMonoid Multiset

variable {M : Type*}

section Prime

variable [CommMonoidWithZero M]

/-- An element `p` of a commutative monoid with zero (e.g., a ring) is called *prime*,
if it's not zero, not a unit, and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`. -/
/-- An element `p` of a commutative monoid with zero (e.g., a ring) is called *prime*,
if it's not zero, not a unit, and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`. -/
def Prime (p : M) : Prop := by sorry


namespace Prime

variable {p : M} (hp : Prime p)
include hp

/-- A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
@[target] theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  sorry


@[target] theorem not_unit : ¬IsUnit p := by sorry


@[target] theorem not_dvd_one : ¬p ∣ 1 := by sorry


@[target] theorem ne_one : p ≠ 1 := by sorry


@[target] theorem dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by sorry


@[target] theorem dvd_mul [DecompositionMonoid α] {k m n : α} :
    k ∣ m * n ↔ ∃ d₁ d₂, d₁ ∣ m ∧ d₂ ∣ n ∧ k = d₁ * d₂ := by
  sorry


/-- The submonoid of primal elements in a cancellative commutative monoid with zero. -/
def Submonoid.isPrimal (M₀ : Type*) [CancelCommMonoidWithZero M₀] : Submonoid M₀ where
  carrier := by sorry


@[target] theorem not_dvd_mul {a b : M} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b := by sorry


theorem dvd_of_dvd_pow {a : M} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := not_unit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

@[target] theorem Squarefree.dvd_pow_iff_dvd {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) :
    x ∣ y ^ n ↔ x ∣ y := by sorry


end Prime

@[target] theorem not_prime_zero : ¬Prime (0 : M) := by sorry


@[simp]
theorem not_prime_one : ¬Prime (1 : M) := fun h => h.not_unit isUnit_one

end Prime

/-- `Irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
structure Irreducible [Monoid M] (p : M) : Prop where
  /-- `p` is not a unit -/
  not_unit : ¬IsUnit p
  /-- if `p` factors then one factor is a unit -/
  isUnit_or_isUnit' : ∀ a b, p = a * b → IsUnit a ∨ IsUnit b

namespace Irreducible

theorem not_dvd_one [CommMonoid M] {p : M} (hp : Irreducible p) : ¬p ∣ 1 :=
  mt (isUnit_of_dvd_one ·) hp.not_unit

@[target] theorem isUnit_or_isUnit [Monoid M] {p : M} (hp : Irreducible p) {a b : M} (h : p = a * b) :
    IsUnit a ∨ IsUnit b := by sorry


end Irreducible

protected theorem Associated.irreducible_iff [Monoid M] {p q : M} (h : p ~ᵤ q) :
    Irreducible p ↔ Irreducible q := by sorry


@[target] theorem not_irreducible_one [Monoid M] : ¬Irreducible (1 : M) := by sorry


theorem Irreducible.ne_one [Monoid M] : ∀ {p : M}, Irreducible p → p ≠ 1
  | _, hp, rfl => not_irreducible_one hp

@[target] theorem not_irreducible_zero [MonoidWithZero M] : ¬Irreducible (0 : M)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : M) ∨ IsUnit (0 : M) := by sorry


theorem Irreducible.ne_zero [MonoidWithZero M] : ∀ {p : M}, Irreducible p → p ≠ 0
  | _, hp, rfl => not_irreducible_zero hp

theorem of_irreducible_mul {M} [Monoid M] {x y : M} : Irreducible (x * y) → IsUnit x ∨ IsUnit y
  | ⟨_, h⟩ => h _ _ rfl

@[target] theorem irreducible_or_factor {M} [Monoid M] (x : M) (h : ¬IsUnit x) :
    Irreducible x ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ a * b = x := by
  sorry


/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
theorem Irreducible.dvd_symm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q → q ∣ p := by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_unit)]

theorem Irreducible.dvd_comm [Monoid M] {p q : M} (hp : Irreducible p) (hq : Irreducible q) :
    p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

section CommMonoidWithZero

variable [CommMonoidWithZero M]

theorem Irreducible.prime_of_isPrimal {a : M}
    (irr : Irreducible a) (primal : IsPrimal a) : Prime a :=
  ⟨irr.ne_zero, irr.not_unit, fun a b dvd ↦ by
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := primal dvd
    exact (of_irreducible_mul irr).symm.imp (·.mul_right_dvd.mpr h₁) (·.mul_left_dvd.mpr h₂)⟩

theorem Irreducible.prime [DecompositionMonoid M] {a : M} (irr : Irreducible a) : Prime a :=
  irr.prime_of_isPrimal (DecompositionMonoid.primal a)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M] {p : M}

protected theorem Prime.irreducible (hp : Prime p) : Irreducible p :=
  ⟨hp.not_unit, fun a b ↦ by
    rintro rfl
    exact (hp.dvd_or_dvd dvd_rfl).symm.imp
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_right <| right_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_right · _)
      (isUnit_of_dvd_one <| (mul_dvd_mul_iff_left <| left_ne_zero_of_mul hp.ne_zero).mp <|
        dvd_mul_of_dvd_left · _)⟩

@[target] theorem irreducible_iff_prime [DecompositionMonoid M] {a : M} : Irreducible a ↔ Prime a := by sorry


end CancelCommMonoidWithZero
