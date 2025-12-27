import VerifiedAgora.tagger
/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Ring.Defs

/-!
# Non-zero divisors in a ring
-/

assert_not_exists Field

open scoped nonZeroDivisors

section Ring
variable {R : Type*} [Ring R] {a x y r : R}

@[target] lemma mul_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r = y * r ↔ x = y := by
  sorry


@[target] lemma mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y := by sorry


/-- In a finite ring, an element is a unit iff it is a non-zero-divisor. -/
lemma isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a ∈ nonZeroDivisors R := by
  refine ⟨IsUnit.mem_nonZeroDivisors, fun ha ↦ ?_⟩
  rw [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]
  intro b c hbc
  rw [← sub_eq_zero, ← sub_mul] at hbc
  exact sub_eq_zero.mp (ha _ hbc)

end Ring

section CommRing
variable {R : Type*} [CommRing R] {r x y : R}

@[target] lemma mul_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x = r * y ↔ x = y := by
  sorry


@[target] lemma mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y := by sorry


lemma dvd_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r ∣ y * r ↔ x ∣ y :=
  ⟨fun ⟨z, _⟩ ↦ ⟨z, by rwa [← mul_cancel_right_mem_nonZeroDivisors hr, mul_assoc, mul_comm z r,
    ← mul_assoc]⟩, fun ⟨z, h⟩ ↦ ⟨z, by rw [h, mul_assoc, mul_comm z r, ← mul_assoc]⟩⟩

@[target] lemma dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y := by sorry


lemma dvd_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x ∣ r * y ↔ x ∣ y :=
  ⟨fun ⟨z, _⟩ ↦ ⟨z, by rwa [← mul_cancel_left_mem_nonZeroDivisors hr, ← mul_assoc]⟩,
    fun ⟨z, h⟩ ↦ ⟨z, by rw [h, ← mul_assoc]⟩⟩

lemma dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y :=
  dvd_cancel_left_mem_nonZeroDivisors c.prop

end CommRing
