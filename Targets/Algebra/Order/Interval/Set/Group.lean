import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Logic.Pairwise
import Mathlib.Tactic.Cases

/-! ### Lemmas about arithmetic operations and intervals. -/


variable {α : Type*}

namespace Set

section OrderedCommGroup

variable [OrderedCommGroup α] {a c d : α}

/-! `inv_mem_Ixx_iff`, `sub_mem_Ixx_iff` -/


@[to_additive]
theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.Icc c d ↔ a ∈ Set.Icc d⁻¹ c⁻¹ :=
  and_comm.trans <| and_congr inv_le' le_inv'

@[target, to_additive]
theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.Ico c d ↔ a ∈ Set.Ioc d⁻¹ c⁻¹ :=
  sorry

@[target, to_additive]
theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.Ioc c d ↔ a ∈ Set.Ico d⁻¹ c⁻¹ :=
  sorry

@[target, to_additive]
theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.Ioo c d ↔ a ∈ Set.Ioo d⁻¹ c⁻¹ :=
  sorry

end OrderedCommGroup

section OrderedAddCommGroup

variable [OrderedAddCommGroup α] {a b c d : α}

/-! `add_mem_Ixx_iff_left` -/

theorem add_mem_Icc_iff_left : a + b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c - b) (d - b) :=
  (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm

@[target]
theorem add_mem_Ico_iff_left : a + b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c - b) (d - b) :=
  sorry

theorem add_mem_Ioc_iff_left : a + b ∈ Set.Ioc c d ↔ a ∈ Set.Ioc (c - b) (d - b) :=
  (and_congr sub_lt_iff_lt_add le_sub_iff_add_le).symm

@[target]
theorem add_mem_Ioo_iff_left : a + b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c - b) (d - b) :=
  sorry

@[target]
theorem add_mem_Icc_iff_right : a + b ∈ Set.Icc c d ↔ b ∈ Set.Icc (c - a) (d - a) :=
  sorry

@[target]
theorem add_mem_Ico_iff_right : a + b ∈ Set.Ico c d ↔ b ∈ Set.Ico (c - a) (d - a) :=
  sorry

@[target]
theorem add_mem_Ioc_iff_right : a + b ∈ Set.Ioc c d ↔ b ∈ Set.Ioc (c - a) (d - a) :=
  sorry

@[target]
theorem add_mem_Ioo_iff_right : a + b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (c - a) (d - a) :=
  sorry

@[target]
theorem sub_mem_Icc_iff_left : a - b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c + b) (d + b) :=
  sorry

@[target]
theorem sub_mem_Ico_iff_left : a - b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c + b) (d + b) :=
  sorry

theorem sub_mem_Ioc_iff_left : a - b ∈ Set.Ioc c d ↔ a ∈ Set.Ioc (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_le_iff_le_add

theorem sub_mem_Ioo_iff_left : a - b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c + b) (d + b) :=
  and_congr lt_sub_iff_add_lt sub_lt_iff_lt_add

/-! `sub_mem_Ixx_iff_right` -/

theorem sub_mem_Icc_iff_right : a - b ∈ Set.Icc c d ↔ b ∈ Set.Icc (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_le_comm le_sub_comm

@[target]
theorem sub_mem_Ico_iff_right : a - b ∈ Set.Ico c d ↔ b ∈ Set.Ioc (a - d) (a - c) :=
  sorry

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.Ioc c d ↔ b ∈ Set.Ico (a - d) (a - c) :=
  and_comm.trans <| and_congr sub_le_comm lt_sub_comm

@[target]
theorem sub_mem_Ioo_iff_right : a - b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (a - d) (a - c) :=
  sorry

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.
@[target]
theorem mem_Icc_iff_abs_le {R : Type*} [LinearOrderedAddCommGroup R] {x y z : R} :
    |x - y| ≤ z ↔ y ∈ Icc (x - z) (x + z) :=
  sorry

@[target]
theorem sub_mem_Icc_zero_iff_right : b - a ∈ Icc 0 b ↔ a ∈ Icc 0 b := by sorry

@[target]
theorem sub_mem_Ico_zero_iff_right : b - a ∈ Ico 0 b ↔ a ∈ Ioc 0 b := by sorry

theorem sub_mem_Ioc_zero_iff_right : b - a ∈ Ioc 0 b ↔ a ∈ Ico 0 b := by
  simp only [sub_mem_Ioc_iff_right, sub_self, sub_zero]

@[target]
theorem sub_mem_Ioo_zero_iff_right : b - a ∈ Ioo 0 b ↔ a ∈ Ioo 0 b := by sorry

end OrderedAddCommGroup

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
@[target]
theorem nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
    Nonempty ↑(Ico x (x + dx) \ Ico y (y + dy)) := by sorry

end LinearOrderedAddCommGroup

/-! ### Lemmas about disjointness of translates of intervals -/

open scoped Function -- required for scoped `on` notation
section PairwiseDisjoint

section OrderedCommGroup

variable [OrderedCommGroup α] (a b : α)

@[target, to_additive]
theorem pairwise_disjoint_Ioc_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a * b ^ n) (a * b ^ (n + 1))) := by sorry

@[target, to_additive]
theorem pairwise_disjoint_Ico_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ico (a * b ^ n) (a * b ^ (n + 1))) := by sorry

@[to_additive]
theorem pairwise_disjoint_Ioo_mul_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a * b ^ n) (a * b ^ (n + 1))) := fun _ _ hmn =>
  (pairwise_disjoint_Ioc_mul_zpow a b hmn).mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self

@[target, to_additive]
theorem pairwise_disjoint_Ioc_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioc (b ^ n) (b ^ (n + 1))) := by sorry

@[to_additive]
theorem pairwise_disjoint_Ico_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ico (b ^ n) (b ^ (n + 1))) := by
  simpa only [one_mul] using pairwise_disjoint_Ico_mul_zpow 1 b

@[target, to_additive]
theorem pairwise_disjoint_Ioo_zpow :
    Pairwise (Disjoint on fun n : ℤ => Ioo (b ^ n) (b ^ (n + 1))) := by sorry

end OrderedCommGroup

section OrderedRing

variable [OrderedRing α] (a : α)

@[target]
theorem pairwise_disjoint_Ioc_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ioc (a + n) (a + n + 1)) := by sorry

theorem pairwise_disjoint_Ico_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ico (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)

@[target]
theorem pairwise_disjoint_Ioo_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ioo (a + n) (a + n + 1)) := by sorry

variable (α)

theorem pairwise_disjoint_Ico_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ico (n : α) (n + 1)) := by
  simpa only [zero_add] using pairwise_disjoint_Ico_add_intCast (0 : α)

theorem pairwise_disjoint_Ioo_intCast : Pairwise (Disjoint on fun n : ℤ => Ioo (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ioo_add_intCast (0 : α)

theorem pairwise_disjoint_Ioc_intCast : Pairwise (Disjoint on fun n : ℤ => Ioc (n : α) (n + 1)) :=
  by simpa only [zero_add] using pairwise_disjoint_Ioc_add_intCast (0 : α)

end OrderedRing

end PairwiseDisjoint

end Set
