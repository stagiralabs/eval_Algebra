import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Rounding

This file defines the `round` function, which uses the `floor` or `ceil` function to round a number
to the nearest integer.

## Main Definitions

* `round a`: Nearest integer to `a`. It rounds halves towards infinity.

## Tags

rounding
-/

assert_not_exists Finset

open Set

variable {F α β : Type*}

open Int

/-! ### Round -/

section round

section LinearOrderedRing

variable [LinearOrderedRing α] [FloorRing α]

/-- `round` rounds a number to the nearest integer. `round (1 / 2) = 1` -/
/-- `round` rounds a number to the nearest integer. `round (1 / 2) = 1` -/
def round (x : α) : ℤ := by sorry


@[target] theorem round_zero : round (0 : α) = 0 := by sorry


@[target] theorem round_one : round (1 : α) = 1 := by sorry


@[target] theorem round_natCast (n : ℕ) : round (n : α) = n := by sorry


@[target] theorem round_ofNat (n : ℕ) [n.AtLeastTwo] : round (ofNat(n) : α) = ofNat(n) := by sorry


@[target] theorem round_intCast (n : ℤ) : round (n : α) = n := by sorry


@[target] theorem round_add_int (x : α) (y : ℤ) : round (x + y) = round x + y := by
  sorry


@[simp]
theorem round_add_one (a : α) : round (a + 1) = round a + 1 := by
  rw [← round_add_int a 1, cast_one]

@[target] theorem round_sub_int (x : α) (y : ℤ) : round (x - y) = round x - y := by
  sorry


@[simp]
theorem round_sub_one (a : α) : round (a - 1) = round a - 1 := by
  rw [← round_sub_int a 1, cast_one]

@[target] theorem round_add_nat (x : α) (y : ℕ) : round (x + y) = round x + y := by sorry


@[target] theorem round_add_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x + ofNat(n)) = round x + ofNat(n) := by sorry


@[target] theorem round_sub_nat (x : α) (y : ℕ) : round (x - y) = round x - y := by sorry


@[target] theorem round_sub_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x - ofNat(n)) = round x - ofNat(n) := by sorry


@[target] theorem round_int_add (x : α) (y : ℤ) : round ((y : α) + x) = y + round x := by
  sorry


@[target] theorem round_nat_add (x : α) (y : ℕ) : round ((y : α) + x) = y + round x := by
  sorry


@[simp]
theorem round_ofNat_add (n : ℕ) [n.AtLeastTwo] (x : α) :
    round (ofNat(n) + x) = ofNat(n) + round x :=
  round_nat_add x n

@[target] theorem abs_sub_round_eq_min (x : α) : |x - round x| = min (fract x) (1 - fract x) := by
  sorry


@[target] theorem round_le (x : α) (z : ℤ) : |x - round x| ≤ |x - z| := by
  sorry


end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField α] [FloorRing α]

@[target] theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  sorry


@[target] theorem round_two_inv : round (2⁻¹ : α) = 1 := by
  sorry


@[target] theorem round_neg_two_inv : round (-2⁻¹ : α) = 0 := by
  sorry


@[target] theorem round_eq_zero_iff {x : α} : round x = 0 ↔ x ∈ Ico (-(1 / 2)) ((1 : α) / 2) := by
  sorry


theorem abs_sub_round (x : α) : |x - round x| ≤ 1 / 2 := by
  rw [round_eq, abs_sub_le_iff]
  have := floor_le (x + 1 / 2)
  have := lt_floor_add_one (x + 1 / 2)
  constructor <;> linarith

@[target] theorem abs_sub_round_div_natCast_eq {m n : ℕ} :
    |(m : α) / n - round ((m : α) / n)| = ↑(min (m % n) (n - m % n)) / n := by
  sorry


@[target] theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by
  sorry


@[target] theorem round_le_add_half (x : α) : round x ≤ x + 1 / 2 := by
  sorry


end LinearOrderedField

end round

namespace Int

variable [LinearOrderedField α] [LinearOrderedField β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by
  simp_rw [round_eq, ← map_floor _ hf, map_add, one_div, map_inv₀, map_ofNat]

end Int
