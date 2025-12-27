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
def round (x : α) : ℤ :=
  if 2 * fract x < 1 then ⌊x⌋ else ⌈x⌉

@[target, simp]
theorem round_zero : round (0 : α) = 0 := by sorry

@[target, simp]
theorem round_one : round (1 : α) = 1 := by sorry

@[simp]
theorem round_natCast (n : ℕ) : round (n : α) = n := by simp [round]

@[target, simp]
theorem round_ofNat (n : ℕ) [n.AtLeastTwo] : round (ofNat(n) : α) = ofNat(n) :=
  sorry

@[simp]
theorem round_intCast (n : ℤ) : round (n : α) = n := by simp [round]

@[simp]
theorem round_add_int (x : α) (y : ℤ) : round (x + y) = round x + y := by
  rw [round, round, Int.fract_add_int, Int.floor_add_int, Int.ceil_add_int, ← apply_ite₂, ite_self]

@[simp]
theorem round_add_one (a : α) : round (a + 1) = round a + 1 := by
  rw [← round_add_int a 1, cast_one]

@[target, simp]
theorem round_sub_int (x : α) (y : ℤ) : round (x - y) = round x - y := by sorry

@[target, simp]
theorem round_sub_one (a : α) : round (a - 1) = round a - 1 := by sorry

@[target, simp]
theorem round_add_nat (x : α) (y : ℕ) : round (x + y) = round x + y :=
  sorry

@[simp]
theorem round_add_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x + ofNat(n)) = round x + ofNat(n) :=
  round_add_nat x n

@[simp]
theorem round_sub_nat (x : α) (y : ℕ) : round (x - y) = round x - y :=
  mod_cast round_sub_int x y

@[simp]
theorem round_sub_ofNat (x : α) (n : ℕ) [n.AtLeastTwo] :
    round (x - ofNat(n)) = round x - ofNat(n) :=
  round_sub_nat x n

@[simp]
theorem round_int_add (x : α) (y : ℤ) : round ((y : α) + x) = y + round x := by
  rw [add_comm, round_add_int, add_comm]

@[target, simp]
theorem round_nat_add (x : α) (y : ℕ) : round ((y : α) + x) = y + round x := by sorry

@[target, simp]
theorem round_ofNat_add (n : ℕ) [n.AtLeastTwo] (x : α) :
    round (ofNat(n) + x) = ofNat(n) + round x :=
  sorry

@[target]
theorem abs_sub_round_eq_min (x : α) : |x - round x| = min (fract x) (1 - fract x) := by sorry

@[target]
theorem round_le (x : α) (z : ℤ) : |x - round x| ≤ |x - z| := by sorry

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField α] [FloorRing α]

theorem round_eq (x : α) : round x = ⌊x + 1 / 2⌋ := by
  simp_rw [round, (by simp only [lt_div_iff₀', two_pos] : 2 * fract x < 1 ↔ fract x < 1 / 2)]
  rcases lt_or_le (fract x) (1 / 2) with hx | hx
  · conv_rhs => rw [← fract_add_floor x, add_assoc, add_left_comm, floor_int_add]
    rw [if_pos hx, self_eq_add_right, floor_eq_iff, cast_zero, zero_add]
    constructor
    · linarith [fract_nonneg x]
    · linarith
  · have : ⌊fract x + 1 / 2⌋ = 1 := by
      rw [floor_eq_iff]
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [fract_lt_one x]
    rw [if_neg (not_lt.mpr hx), ← fract_add_floor x, add_assoc, add_left_comm, floor_int_add,
      ceil_add_int, add_comm _ ⌊x⌋, add_right_inj, ceil_eq_iff, this, cast_one, sub_self]
    constructor
    · linarith
    · linarith [fract_lt_one x]

@[target, simp]
theorem round_two_inv : round (2⁻¹ : α) = 1 := by sorry

@[simp]
theorem round_neg_two_inv : round (-2⁻¹ : α) = 0 := by
  simp only [round_eq, ← one_div, neg_add_cancel, floor_zero]

@[target, simp]
theorem round_eq_zero_iff {x : α} : round x = 0 ↔ x ∈ Ico (-(1 / 2)) ((1 : α) / 2) := by sorry

@[target]
theorem abs_sub_round (x : α) : |x - round x| ≤ 1 / 2 := by sorry

theorem abs_sub_round_div_natCast_eq {m n : ℕ} :
    |(m : α) / n - round ((m : α) / n)| = ↑(min (m % n) (n - m % n)) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  have hn' : 0 < (n : α) := by
    norm_cast
  rw [abs_sub_round_eq_min, Nat.cast_min, ← min_div_div_right hn'.le,
    fract_div_natCast_eq_div_natCast_mod, Nat.cast_sub (m.mod_lt hn).le, sub_div, div_self hn'.ne']

@[target, bound]
theorem sub_half_lt_round (x : α) : x - 1 / 2 < round x := by sorry

@[target, bound]
theorem round_le_add_half (x : α) : round x ≤ x + 1 / 2 := by sorry

end LinearOrderedField

end round

namespace Int

variable [LinearOrderedField α] [LinearOrderedField β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

@[target]
theorem map_round (f : F) (hf : StrictMono f) (a : α) : round (f a) = round a := by sorry

end Int
