import VerifiedAgora.tagger
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Data.Nat.Basic

/-!
# Divisibility in groups with zero.

Lemmas about divisibility in groups and monoids with zero.

-/

assert_not_exists DenselyOrdered

variable {α : Type*}

section SemigroupWithZero

variable [SemigroupWithZero α] {a : α}

@[target] theorem eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0 := by sorry


/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
/-- Given an element `a` of a commutative semigroup with zero, there exists another element whose
    product with zero equals `a` iff `a` equals zero. -/
@[target] theorem zero_dvd_iff : 0 ∣ a ↔ a = 0 :=
  ⟨eq_zero_of_zero_dvd, fun h => by
    sorry


@[target] theorem dvd_zero (a : α) : a ∣ 0 :=
  Dvd.intro 0 (by sorry


end SemigroupWithZero

/-- Given two elements `b`, `c` of a `CancelMonoidWithZero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
/-- Given two elements `b`, `c` of a `CancelMonoidWithZero` and a nonzero element `a`,
 `a*b` divides `a*c` iff `b` divides `c`. -/
@[target] theorem mul_dvd_mul_iff_left [CancelMonoidWithZero α] {a b c : α} (ha : a ≠ 0) :
    a * b ∣ a * c ↔ b ∣ c :=
  exists_congr fun d => by sorry


/-- Given two elements `a`, `b` of a commutative `CancelMonoidWithZero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
/-- Given two elements `a`, `b` of a commutative `CancelMonoidWithZero` and a nonzero
  element `c`, `a*c` divides `b*c` iff `a` divides `b`. -/
@[target] theorem mul_dvd_mul_iff_right [CancelCommMonoidWithZero α] {a b c : α} (hc : c ≠ 0) :
    a * c ∣ b * c ↔ a ∣ b :=
  exists_congr fun d => by sorry


section CommMonoidWithZero

variable [CommMonoidWithZero α]

/-- `DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
/-- `DvdNotUnit a b` expresses that `a` divides `b` "strictly", i.e. that `b` divided by `a`
is not a unit. -/
def DvdNotUnit (a b : α) : Prop := by sorry


@[target] theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  sorry


variable {x y : α}

@[target] theorem isRelPrime_zero_left : IsRelPrime 0 x ↔ IsUnit x := by sorry


@[target] theorem isRelPrime_zero_right : IsRelPrime x 0 ↔ IsUnit x := by sorry


@[target] theorem not_isRelPrime_zero_zero [Nontrivial α] : ¬IsRelPrime (0 : α) 0 := by sorry


theorem IsRelPrime.ne_zero_or_ne_zero [Nontrivial α] (h : IsRelPrime x y) : x ≠ 0 ∨ y ≠ 0 :=
  not_or_of_imp <| by rintro rfl rfl; exact not_isRelPrime_zero_zero h

end CommMonoidWithZero

@[target] theorem isRelPrime_of_no_nonunits_factors [MonoidWithZero α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z, ¬ IsUnit z → z ≠ 0 → z ∣ x → ¬z ∣ y) : IsRelPrime x y := by
  sorry


@[target] theorem dvd_and_not_dvd_iff [CancelCommMonoidWithZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y :=
  ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by sorry


section MonoidWithZero

variable [MonoidWithZero α]

@[target] theorem ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q ≠ 0) (h₂ : p ∣ q) : p ≠ 0 := by
  sorry


@[target] theorem isPrimal_zero : IsPrimal (0 : α) := by sorry


theorem IsPrimal.mul {α} [CancelCommMonoidWithZero α] {m n : α}
    (hm : IsPrimal m) (hn : IsPrimal n) : IsPrimal (m * n) := by
  obtain rfl | h0 := eq_or_ne m 0; · rwa [zero_mul]
  intro b c h
  obtain ⟨a₁, a₂, ⟨b, rfl⟩, ⟨c, rfl⟩, rfl⟩ := hm (dvd_of_mul_right_dvd h)
  rw [mul_mul_mul_comm, mul_dvd_mul_iff_left h0] at h
  obtain ⟨a₁', a₂', h₁, h₂, rfl⟩ := hn h
  exact ⟨a₁ * a₁', a₂ * a₂', mul_dvd_mul_left _ h₁, mul_dvd_mul_left _ h₂, mul_mul_mul_comm _ _ _ _⟩

end MonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α] {a b : α} {m n : ℕ}

section Subsingleton
variable [Subsingleton αˣ]

@[target] theorem dvd_antisymm : a ∣ b → b ∣ a → a = b := by
  sorry


theorem dvd_antisymm' : a ∣ b → b ∣ a → b = a :=
  flip dvd_antisymm

alias Dvd.dvd.antisymm := dvd_antisymm

alias Dvd.dvd.antisymm' := dvd_antisymm'

@[target] theorem eq_of_forall_dvd (h : ∀ c, a ∣ c ↔ b ∣ c) : a = b := by sorry


theorem eq_of_forall_dvd' (h : ∀ c, c ∣ a ↔ c ∣ b) : a = b :=
  ((h _).1 dvd_rfl).antisymm <| (h _).2 dvd_rfl

end Subsingleton

@[target] lemma pow_dvd_pow_iff (ha₀ : a ≠ 0) (ha : ¬IsUnit a) : a ^ n ∣ a ^ m ↔ n ≤ m := by
  sorry


end CancelCommMonoidWithZero

section GroupWithZero
variable [GroupWithZero α]

/-- `∣` is not a useful definition if an inverse is available. -/
@[simp]
lemma GroupWithZero.dvd_iff {m n : α} : m ∣ n ↔ (m = 0 → n = 0) := by
  refine ⟨fun ⟨a, ha⟩ hm => ?_, fun h => ?_⟩
  · simp [hm, ha]
  · refine ⟨m⁻¹ * n, ?_⟩
    obtain rfl | hn := eq_or_ne n 0
    · simp
    · rw [mul_inv_cancel_left₀ (mt h hn)]

end GroupWithZero
