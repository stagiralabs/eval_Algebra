import VerifiedAgora.tagger
/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Monotone
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic

/-!
# Floor and ceil

## Summary

We define the natural- and integer-valued floor and ceil functions on linearly ordered rings.

## Main Definitions

* `FloorSemiring`: An ordered semiring with natural-valued floor and ceil.
* `Nat.floor a`: Greatest natural `n` such that `n ≤ a`. Equal to `0` if `a < 0`.
* `Nat.ceil a`: Least natural `n` such that `a ≤ n`.

* `FloorRing`: A linearly ordered ring with integer-valued floor and ceil.
* `Int.floor a`: Greatest integer `z` such that `z ≤ a`.
* `Int.ceil a`: Least integer `z` such that `a ≤ z`.
* `Int.fract a`: Fractional part of `a`, defined as `a - floor a`.

## Notations

* `⌊a⌋₊` is `Nat.floor a`.
* `⌈a⌉₊` is `Nat.ceil a`.
* `⌊a⌋` is `Int.floor a`.
* `⌈a⌉` is `Int.ceil a`.

The index `₊` in the notations for `Nat.floor` and `Nat.ceil` is used in analogy to the notation
for `nnnorm`.

## TODO

`LinearOrderedRing`/`LinearOrderedSemiring` can be relaxed to `OrderedRing`/`OrderedSemiring` in
many lemmas.

## Tags

rounding, floor, ceil
-/

assert_not_exists Finset

open Set

variable {F α β : Type*}

/-! ### Floor semiring -/

/-- A `FloorSemiring` is an ordered semiring over `α` with a function
`floor : α → ℕ` satisfying `∀ (n : ℕ) (x : α), n ≤ ⌊x⌋ ↔ (n : α) ≤ x)`.
Note that many lemmas require a `LinearOrder`. Please see the above `TODO`. -/
class FloorSemiring (α) [OrderedSemiring α] where
  /-- `FloorSemiring.floor a` computes the greatest natural `n` such that `(n : α) ≤ a`. -/
  floor : α → ℕ
  /-- `FloorSemiring.ceil a` computes the least natural `n` such that `a ≤ (n : α)`. -/
  ceil : α → ℕ
  /-- `FloorSemiring.floor` of a negative element is zero. -/
  floor_of_neg {a : α} (ha : a < 0) : floor a = 0
  /-- A natural number `n` is smaller than `FloorSemiring.floor a` iff its coercion to `α` is
  smaller than `a`. -/
  gc_floor {a : α} {n : ℕ} (ha : 0 ≤ a) : n ≤ floor a ↔ (n : α) ≤ a
  /-- `FloorSemiring.ceil` is the lower adjoint of the coercion `↑ : ℕ → α`. -/
  gc_ceil : GaloisConnection ceil (↑)

instance : FloorSemiring ℕ where
  floor := id
  ceil := id
  floor_of_neg ha := (Nat.not_lt_zero _ ha).elim
  gc_floor _ := by
    rw [Nat.cast_id]
    rfl
  gc_ceil n a := by
    rw [Nat.cast_id]
    rfl

namespace Nat

section OrderedSemiring

variable [OrderedSemiring α] [FloorSemiring α] {a : α} {n : ℕ}

/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ :=
  FloorSemiring.floor

/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ :=
  FloorSemiring.ceil

@[simp]
theorem floor_nat : (Nat.floor : ℕ → ℕ) = id :=
  rfl

@[target, simp]
theorem ceil_nat : (Nat.ceil : ℕ → ℕ) = id :=
  sorry

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

theorem le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a :=
  FloorSemiring.gc_floor ha

theorem le_floor (h : (n : α) ≤ a) : n ≤ ⌊a⌋₊ :=
  (le_floor_iff <| n.cast_nonneg.trans h).2 h

theorem gc_ceil_coe : GaloisConnection (ceil : α → ℕ) (↑) :=
  FloorSemiring.gc_ceil

@[simp]
theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n :=
  gc_ceil_coe _ _

end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] [FloorSemiring α] {a b : α} {n : ℕ}

theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff ha

@[target]
theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  sorry

theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_le fun h' => (le_floor h').not_lt h

@[target]
theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := sorry

theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : α) ≤ a :=
  (le_floor_iff ha).1 le_rfl

theorem lt_succ_floor (a : α) : a < ⌊a⌋₊.succ :=
  lt_of_floor_lt <| Nat.lt_succ_self _

@[bound]
theorem lt_floor_add_one (a : α) : a < ⌊a⌋₊ + 1 := by simpa using lt_succ_floor a

@[simp]
theorem floor_natCast (n : ℕ) : ⌊(n : α)⌋₊ = n :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor_iff, Nat.cast_le]
    exact n.cast_nonneg

@[simp]
theorem floor_zero : ⌊(0 : α)⌋₊ = 0 := by rw [← Nat.cast_zero, floor_natCast]

@[simp]
theorem floor_one : ⌊(1 : α)⌋₊ = 1 := by rw [← Nat.cast_one, floor_natCast]

@[target, simp]
theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : α)⌋₊ = ofNat(n) :=
  sorry

theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
  ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    rintro rfl
    exact floor_zero

theorem floor_mono : Monotone (floor : α → ℕ) := fun a b h => by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact le_floor ((floor_le ha).trans h)

@[gcongr, bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋₊ ≤ ⌊b⌋₊ := floor_mono hab

@[target]
theorem le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a := by sorry

@[simp]
theorem one_le_floor_iff (x : α) : 1 ≤ ⌊x⌋₊ ↔ 1 ≤ x :=
  mod_cast @le_floor_iff' α _ _ x 1 one_ne_zero

theorem floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff' hn

theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a := by
  rw [Nat.lt_iff_add_one_le, zero_add, le_floor_iff' Nat.one_ne_zero, cast_one]

theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
  (le_or_lt a 0).resolve_left fun ha => lt_irrefl 0 <| by rwa [floor_of_nonpos ha] at h

@[target]
theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a :=
  sorry

@[target]
theorem floor_le_of_le (h : a ≤ n) : ⌊a⌋₊ ≤ n :=
  sorry

@[target]
theorem floor_le_one_of_le_one (h : a ≤ 1) : ⌊a⌋₊ ≤ 1 :=
  sorry

@[target, simp]
theorem floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 := by sorry

theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff ha, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt ha, Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

theorem floor_eq_iff' (hn : n ≠ 0) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff' hn, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt' (Nat.add_one_ne_zero n),
    Nat.lt_add_one_iff, le_antisymm_iff, and_comm]

theorem floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (Set.Ico n (n + 1) : Set α), ⌊a⌋₊ = n := fun _ ⟨h₀, h₁⟩ =>
  (floor_eq_iff <| n.cast_nonneg.trans h₀).mpr ⟨h₀, h₁⟩

theorem floor_eq_on_Ico' (n : ℕ) :
    ∀ a ∈ (Set.Ico n (n + 1) : Set α), (⌊a⌋₊ : α) = n :=
  fun x hx => mod_cast floor_eq_on_Ico n x hx

@[simp]
theorem preimage_floor_zero : (floor : α → ℕ) ⁻¹' {0} = Iio 1 :=
  ext fun _ => floor_eq_zero

theorem preimage_floor_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (floor : α → ℕ) ⁻¹' {n} = Ico (n : α) (n + 1) :=
  ext fun _ => floor_eq_iff' hn

/-! #### Ceil -/

theorem lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le

theorem add_one_le_ceil_iff : n + 1 ≤ ⌈a⌉₊ ↔ (n : α) < a := by
  rw [← Nat.lt_ceil, Nat.add_one_le_iff]

@[simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉₊ ↔ 0 < a := by
  rw [← zero_add 1, Nat.add_one_le_ceil_iff, Nat.cast_zero]

@[bound]
theorem ceil_le_floor_add_one (a : α) : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
  rw [ceil_le, Nat.cast_add, Nat.cast_one]
  exact (lt_floor_add_one a).le

@[bound]
theorem le_ceil (a : α) : a ≤ ⌈a⌉₊ :=
  ceil_le.1 le_rfl

@[simp]
theorem ceil_intCast {α : Type*} [LinearOrderedRing α] [FloorSemiring α] (z : ℤ) :
    ⌈(z : α)⌉₊ = z.toNat :=
  eq_of_forall_ge_iff fun a => by
    simp only [ceil_le, Int.toNat_le]
    norm_cast

@[simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : α)⌉₊ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, cast_le]

theorem ceil_mono : Monotone (ceil : α → ℕ) :=
  gc_ceil_coe.monotone_l

@[gcongr, bound] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉₊ ≤ ⌈b⌉₊ := ceil_mono hab

@[simp]
theorem ceil_zero : ⌈(0 : α)⌉₊ = 0 := by rw [← Nat.cast_zero, ceil_natCast]

@[simp]
theorem ceil_one : ⌈(1 : α)⌉₊ = 1 := by rw [← Nat.cast_one, ceil_natCast]

@[simp]
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : α)⌉₊ = ofNat(n) := ceil_natCast n

@[target, simp]
theorem ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := by sorry

@[simp]
theorem ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a := by rw [lt_ceil, cast_zero]

theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n :=
  (le_ceil a).trans_lt (Nat.cast_lt.2 h)

@[target]
theorem le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n :=
  sorry

@[bound]
theorem floor_le_ceil (a : α) : ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact Nat.zero_le _
  · exact cast_le.1 ((floor_le ha).trans <| le_ceil _)

theorem floor_lt_ceil_of_lt_of_pos {a b : α} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  rcases le_or_lt 0 a with (ha | ha)
  · rw [floor_lt ha]
    exact h.trans_le (le_ceil _)
  · rwa [floor_of_nonpos ha.le, lt_ceil, Nat.cast_zero]

theorem ceil_eq_iff (hn : n ≠ 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ n := by
  rw [← ceil_le, ← not_le, ← ceil_le, not_le,
    tsub_lt_iff_right (Nat.add_one_le_iff.2 (pos_iff_ne_zero.2 hn)), Nat.lt_add_one_iff,
    le_antisymm_iff, and_comm]

@[target, simp]
theorem preimage_ceil_zero : (Nat.ceil : α → ℕ) ⁻¹' {0} = Iic 0 :=
  sorry

theorem preimage_ceil_of_ne_zero (hn : n ≠ 0) : (Nat.ceil : α → ℕ) ⁻¹' {n} = Ioc (↑(n - 1) : α) n :=
  ext fun _ => ceil_eq_iff hn

/-! #### Intervals -/

@[simp]
theorem preimage_Ioo {a b : α} (ha : 0 ≤ a) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  ext
  simp [floor_lt, lt_ceil, ha]

@[simp]
theorem preimage_Ico {a b : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  ext
  simp [ceil_le, lt_ceil]

@[simp]
theorem preimage_Ioc {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  ext
  simp [floor_lt, le_floor_iff, hb, ha]

@[simp]
theorem preimage_Icc {a b : α} (hb : 0 ≤ b) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  ext
  simp [ceil_le, hb, le_floor_iff]

@[simp]
theorem preimage_Ioi {a : α} (ha : 0 ≤ a) : (Nat.cast : ℕ → α) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  ext
  simp [floor_lt, ha]

@[simp]
theorem preimage_Ici {a : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  ext
  simp [ceil_le]

@[simp]
theorem preimage_Iio {a : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  ext
  simp [lt_ceil]

@[simp]
theorem preimage_Iic {a : α} (ha : 0 ≤ a) : (Nat.cast : ℕ → α) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  ext
  simp [le_floor_iff, ha]

theorem floor_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
  eq_of_forall_le_iff fun b => by
    rw [le_floor_iff (add_nonneg ha n.cast_nonneg)]
    obtain hb | hb := le_total n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : α), add_le_add_iff_right, add_le_add_iff_right,
        le_floor_iff ha]
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_left_comm _ b, add_left_comm _ (b : α)]
      refine iff_of_true ?_ le_self_add
      exact le_add_of_nonneg_right <| ha.trans <| le_add_of_nonneg_right d.cast_nonneg

theorem floor_add_one (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 := by
  rw [← cast_one, floor_add_nat ha 1]

theorem floor_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋₊ = ⌊a⌋₊ + ofNat(n) :=
  floor_add_nat ha n

@[simp]
theorem floor_sub_nat [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) (n : ℕ) :
    ⌊a - n⌋₊ = ⌊a⌋₊ - n := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha, floor_of_nonpos (tsub_nonpos_of_le (ha.trans n.cast_nonneg)), zero_tsub]
  rcases le_total a n with h | h
  · rw [floor_of_nonpos (tsub_nonpos_of_le h), eq_comm, tsub_eq_zero_iff_le]
    exact Nat.cast_le.1 ((Nat.floor_le ha).trans h)
  · rw [eq_tsub_iff_add_eq_of_le (le_floor h), ← floor_add_nat _, tsub_add_cancel_of_le h]
    exact le_tsub_of_add_le_left ((add_zero _).trans_le h)

@[simp]
theorem floor_sub_one [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 :=
  mod_cast floor_sub_nat a 1

@[simp]
theorem floor_sub_ofNat [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n) :=
  floor_sub_nat a n

theorem ceil_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
  eq_of_forall_ge_iff fun b => by
    rw [← not_lt, ← not_lt, not_iff_not, lt_ceil]
    obtain hb | hb := le_or_lt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : α), add_lt_add_iff_right, add_lt_add_iff_right,
        lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (Nat.lt_add_left _ hb)

theorem ceil_add_one (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 := by
  rw [cast_one.symm, ceil_add_nat ha 1]

theorem ceil_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉₊ = ⌈a⌉₊ + ofNat(n) :=
  ceil_add_nat ha n

@[bound]
theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1 :=
  lt_ceil.1 <| (Nat.lt_succ_self _).trans_le (ceil_add_one ha).ge

@[bound]
theorem ceil_add_le (a b : α) : ⌈a + b⌉₊ ≤ ⌈a⌉₊ + ⌈b⌉₊ := by
  rw [ceil_le, Nat.cast_add]
  gcongr <;> apply le_ceil

end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing α] [FloorSemiring α]

@[bound]
theorem sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋₊ :=
  sub_lt_iff_lt_add.2 <| lt_floor_add_one a

end LinearOrderedRing

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] [FloorSemiring α]

-- TODO: should these lemmas be `simp`? `norm_cast`?

theorem floor_div_nat (a : α) (n : ℕ) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  rcases le_total a 0 with ha | ha
  · rw [floor_of_nonpos, floor_of_nonpos ha]
    · simp
    apply div_nonpos_of_nonpos_of_nonneg ha n.cast_nonneg
  obtain rfl | hn := n.eq_zero_or_pos
  · rw [cast_zero, div_zero, Nat.div_zero, floor_zero]
  refine (floor_eq_iff ?_).2 ?_
  · exact div_nonneg ha n.cast_nonneg
  constructor
  · exact cast_div_le.trans (div_le_div_of_nonneg_right (floor_le ha) n.cast_nonneg)
  rw [div_lt_iff₀, add_mul, one_mul, ← cast_mul, ← cast_add, ← floor_lt ha]
  · exact lt_div_mul_add hn
  · exact cast_pos.2 hn

@[target]
theorem floor_div_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n) :=
  sorry
@[target]
theorem floor_div_eq_div (m n : ℕ) : ⌊(m : α) / n⌋₊ = m / n := by sorry

end LinearOrderedSemifield

section LinearOrderedField
variable [LinearOrderedField α] [FloorSemiring α] {a b : α}

lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ ≤ a) : b * a < ⌊a⌋₊ := by
  calc
    b * a < b * (⌊a⌋₊ + 1) := by gcongr; exacts [hb₀, lt_floor_add_one _]
    _ ≤ ⌊a⌋₊ := by
      rw [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le]
      exact le_floor hba

lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a) : ⌈a⌉₊ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉₊ ≤ (⌈(b - 1)⁻¹⌉₊ : α) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉₊ < a + 1 := ceil_lt_add_one <| hba.trans' <| by positivity
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr; positivity
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b ≤ a) : ⌈a⌉₊ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [mul_div_cancel₀, cast_le, ceil_le]
    · exact _root_.div_le_self (by positivity) hb.le
    · positivity
  · exact (ceil_lt_mul hb hba).le

lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋₊ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉₊ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉₊ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

end LinearOrderedField
end Nat

/-- There exists at most one `FloorSemiring` structure on a linear ordered semiring. -/
@[target]
theorem subsingleton_floorSemiring {α} [LinearOrderedSemiring α] :
    Subsingleton (FloorSemiring α) := by sorry
class FloorRing (α) [LinearOrderedRing α] where
  /-- `FloorRing.floor a` computes the greatest integer `z` such that `(z : α) ≤ a`. -/
  floor : α → ℤ
  /-- `FloorRing.ceil a` computes the least integer `z` such that `a ≤ (z : α)`. -/
  ceil : α → ℤ
  /-- `FloorRing.ceil` is the upper adjoint of the coercion `↑ : ℤ → α`. -/
  gc_coe_floor : GaloisConnection (↑) floor
  /-- `FloorRing.ceil` is the lower adjoint of the coercion `↑ : ℤ → α`. -/
  gc_ceil_coe : GaloisConnection ceil (↑)

instance : FloorRing ℤ where
  floor := id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id]
    rfl
  gc_ceil_coe a b := by
    rw [Int.cast_id]
    rfl

/-- A `FloorRing` constructor from the `floor` function alone. -/
def FloorRing.ofFloor (α) [LinearOrderedRing α] (floor : α → ℤ)
    (gc_coe_floor : GaloisConnection (↑) floor) : FloorRing α :=
  { floor
    ceil := fun a => -floor (-a)
    gc_coe_floor
    gc_ceil_coe := fun a z => by rw [neg_le, ← gc_coe_floor, Int.cast_neg, neg_le_neg_iff] }

/-- A `FloorRing` constructor from the `ceil` function alone. -/
def FloorRing.ofCeil (α) [LinearOrderedRing α] (ceil : α → ℤ)
    (gc_ceil_coe : GaloisConnection ceil (↑)) : FloorRing α :=
  { floor := fun a => -ceil (-a)
    ceil
    gc_coe_floor := fun a z => by rw [le_neg, gc_ceil_coe, Int.cast_neg, neg_le_neg_iff]
    gc_ceil_coe }

namespace Int

variable [LinearOrderedRing α] [FloorRing α] {z : ℤ} {a b : α}

/-- `Int.floor a` is the greatest integer `z` such that `z ≤ a`. It is denoted with `⌊a⌋`. -/
def floor : α → ℤ :=
  FloorRing.floor

/-- `Int.ceil a` is the smallest integer `z` such that `a ≤ z`. It is denoted with `⌈a⌉`. -/
def ceil : α → ℤ :=
  FloorRing.ceil

/-- `Int.fract a` the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α :=
  a - floor a

@[target, simp]
theorem floor_int : (Int.floor : ℤ → ℤ) = id :=
  sorry

@[target, simp]
theorem ceil_int : (Int.ceil : ℤ → ℤ) = id :=
  sorry

@[target, simp]
theorem fract_int : (Int.fract : ℤ → ℤ) = 0 :=
  sorry

@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a

-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.

@[target, simp]
theorem floorRing_floor_eq : @FloorRing.floor = @Int.floor :=
  sorry

@[target, simp]
theorem floorRing_ceil_eq : @FloorRing.ceil = @Int.ceil :=
  sorry

theorem gc_coe_floor : GaloisConnection ((↑) : ℤ → α) floor :=
  FloorRing.gc_coe_floor

@[target]
theorem le_floor : z ≤ ⌊a⌋ ↔ (z : α) ≤ a :=
  sorry

@[target]
theorem floor_lt : ⌊a⌋ < z ↔ a < z :=
  sorry

@[target, bound]
theorem floor_le (a : α) : (⌊a⌋ : α) ≤ a :=
  sorry

@[target]
theorem floor_le_iff : ⌊a⌋ ≤ z ↔ a < z + 1 := by sorry
theorem lt_floor_iff : z < ⌊a⌋ ↔ z + 1 ≤ a := by rw [← add_one_le_iff, le_floor]; norm_cast

@[target]
theorem floor_nonneg : 0 ≤ ⌊a⌋ ↔ 0 ≤ a := by sorry

@[simp]
theorem floor_le_sub_one_iff : ⌊a⌋ ≤ z - 1 ↔ a < z := by rw [← floor_lt, le_sub_one_iff]

@[target, simp]
theorem floor_le_neg_one_iff : ⌊a⌋ ≤ -1 ↔ a < 0 := by sorry

@[bound]
theorem floor_nonpos (ha : a ≤ 0) : ⌊a⌋ ≤ 0 := by
  rw [← @cast_le α, Int.cast_zero]
  exact (floor_le a).trans ha

@[target]
theorem lt_succ_floor (a : α) : a < ⌊a⌋.succ :=
  sorry

@[target, simp, bound]
theorem lt_floor_add_one (a : α) : a < ⌊a⌋ + 1 := by sorry

@[target, simp, bound]
theorem sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋ :=
  sorry

@[target, simp]
theorem floor_intCast (z : ℤ) : ⌊(z : α)⌋ = z :=
  sorry

@[target, simp]
theorem floor_natCast (n : ℕ) : ⌊(n : α)⌋ = n :=
  sorry

@[target, simp]
theorem floor_zero : ⌊(0 : α)⌋ = 0 := by sorry

@[target, simp]
theorem floor_one : ⌊(1 : α)⌋ = 1 := by sorry

@[simp] theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : α)⌋ = ofNat(n) :=
  floor_natCast n

@[target, mono]
theorem floor_mono : Monotone (floor : α → ℤ) :=
  sorry

@[gcongr, bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ := floor_mono hab

@[target]
theorem floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a := by sorry

@[simp]
theorem floor_add_int (a : α) (z : ℤ) : ⌊a + z⌋ = ⌊a⌋ + z :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor, ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, Int.cast_sub]

@[target, simp]
theorem floor_add_one (a : α) : ⌊a + 1⌋ = ⌊a⌋ + 1 := by sorry

@[bound]
theorem le_floor_add (a b : α) : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
  rw [le_floor, Int.cast_add]
  gcongr <;> apply floor_le

@[bound]
theorem le_floor_add_floor (a b : α) : ⌊a + b⌋ - 1 ≤ ⌊a⌋ + ⌊b⌋ := by
  rw [← sub_le_iff_le_add, le_floor, Int.cast_sub, sub_le_comm, Int.cast_sub, Int.cast_one]
  refine le_trans ?_ (sub_one_lt_floor _).le
  rw [sub_le_iff_le_add', ← add_sub_assoc, sub_le_sub_iff_right]
  exact floor_le _

@[target, simp]
theorem floor_int_add (z : ℤ) (a : α) : ⌊↑z + a⌋ = z + ⌊a⌋ := by sorry

@[target, simp]
theorem floor_add_nat (a : α) (n : ℕ) : ⌊a + n⌋ = ⌊a⌋ + n := by sorry

@[target, simp]
theorem floor_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋ = ⌊a⌋ + ofNat(n) :=
  sorry

@[target, simp]
theorem floor_nat_add (n : ℕ) (a : α) : ⌊↑n + a⌋ = n + ⌊a⌋ := by sorry

@[target, simp]
theorem floor_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : α) :
    ⌊ofNat(n) + a⌋ = ofNat(n) + ⌊a⌋ :=
  sorry

@[simp]
theorem floor_sub_int (a : α) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)

@[target, simp]
theorem floor_sub_nat (a : α) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := by sorry

@[simp] theorem floor_sub_one (a : α) : ⌊a - 1⌋ = ⌊a⌋ - 1 := mod_cast floor_sub_nat a 1

@[simp]
theorem floor_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋ = ⌊a⌋ - ofNat(n) :=
  floor_sub_nat a n

@[target]
theorem abs_sub_lt_one_of_floor_eq_floor {α : Type*} [LinearOrderedCommRing α] [FloorRing α]
    {a b : α} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by sorry

@[target]
theorem floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 := by sorry

@[simp]
theorem floor_eq_zero_iff : ⌊a⌋ = 0 ↔ a ∈ Ico (0 : α) 1 := by simp [floor_eq_iff]

theorem floor_eq_on_Ico (n : ℤ) : ∀ a ∈ Set.Ico (n : α) (n + 1), ⌊a⌋ = n := fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩

@[target]
theorem floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ Set.Ico (n : α) (n + 1), (⌊a⌋ : α) = n := sorry

@[target, simp]
theorem preimage_floor_singleton (m : ℤ) : (floor : α → ℤ) ⁻¹' {m} = Ico (m : α) (m + 1) :=
  sorry

@[target]
lemma floor_eq_self_iff_mem (a : α) : ⌊a⌋ = a ↔ a ∈ Set.range Int.cast := by sorry


@[target, simp]
theorem self_sub_floor (a : α) : a - ⌊a⌋ = fract a :=
  sorry

@[simp]
theorem floor_add_fract (a : α) : (⌊a⌋ : α) + fract a = a :=
  add_sub_cancel _ _

@[simp]
theorem fract_add_floor (a : α) : fract a + ⌊a⌋ = a :=
  sub_add_cancel _ _

@[simp]
theorem fract_add_int (a : α) (m : ℤ) : fract (a + m) = fract a := by
  rw [fract]
  simp

@[target, simp]
theorem fract_add_nat (a : α) (m : ℕ) : fract (a + m) = fract a := by sorry

@[target, simp]
theorem fract_add_one (a : α) : fract (a + 1) = fract a := sorry

@[target, simp]
theorem fract_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    fract (a + ofNat(n)) = fract a :=
  sorry

@[target, simp]
theorem fract_int_add (m : ℤ) (a : α) : fract (↑m + a) = fract a := by sorry

@[target, simp]
theorem fract_nat_add (n : ℕ) (a : α) : fract (↑n + a) = fract a := by sorry

@[target, simp]
theorem fract_one_add (a : α) : fract (1 + a) = fract a := sorry

@[target, simp]
theorem fract_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : α) :
    fract (ofNat(n) + a) = fract a :=
  sorry

@[target, simp]
theorem fract_sub_int (a : α) (m : ℤ) : fract (a - m) = fract a := by sorry

@[target, simp]
theorem fract_sub_nat (a : α) (n : ℕ) : fract (a - n) = fract a := by sorry

@[target, simp]
theorem fract_sub_one (a : α) : fract (a - 1) = fract a := sorry

@[target, simp]
theorem fract_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    fract (a - ofNat(n)) = fract a :=
  sorry

-- Was a duplicate lemma under a bad name

@[target]
theorem fract_add_le (a b : α) : fract (a + b) ≤ fract a + fract b := by sorry

theorem fract_add_fract_le (a b : α) : fract a + fract b ≤ fract (a + b) + 1 := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_add, sub_le_sub_iff_left]
  exact mod_cast le_floor_add_floor a b

@[simp]
theorem self_sub_fract (a : α) : a - fract a = ⌊a⌋ :=
  sub_sub_cancel _ _

@[target, simp]
theorem fract_sub_self (a : α) : fract a - a = -⌊a⌋ :=
  sorry

@[target, simp]
theorem fract_nonneg (a : α) : 0 ≤ fract a :=
  sorry
@[target]
lemma fract_pos : 0 < fract a ↔ a ≠ ⌊a⌋ :=
  sorry

theorem fract_lt_one (a : α) : fract a < 1 :=
  sub_lt_comm.1 <| sub_one_lt_floor _

@[simp]
theorem fract_zero : fract (0 : α) = 0 := by rw [fract, floor_zero, cast_zero, sub_self]

@[target, simp]
theorem fract_one : fract (1 : α) = 0 := by sorry

@[target]
theorem abs_fract : |fract a| = fract a :=
  sorry

@[simp]
theorem abs_one_sub_fract : |1 - fract a| = 1 - fract a :=
  abs_eq_self.mpr <| sub_nonneg.mpr (fract_lt_one a).le

@[target, simp]
theorem fract_intCast (z : ℤ) : fract (z : α) = 0 := by sorry

@[target, simp]
theorem fract_natCast (n : ℕ) : fract (n : α) = 0 := by sorry

@[target, simp]
theorem fract_ofNat (n : ℕ) [n.AtLeastTwo] :
    fract (ofNat(n) : α) = 0 :=
  sorry

@[target]
theorem fract_floor (a : α) : fract (⌊a⌋ : α) = 0 :=
  sorry

@[simp]
theorem floor_fract (a : α) : ⌊fract a⌋ = 0 := by
  rw [floor_eq_iff, Int.cast_zero, zero_add]; exact ⟨fract_nonneg _, fract_lt_one _⟩

@[target]
theorem fract_eq_iff {a b : α} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
  sorry

@[target]
theorem fract_eq_fract {a b : α} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
  sorry

@[target, simp]
theorem fract_eq_self {a : α} : fract a = a ↔ 0 ≤ a ∧ a < 1 :=
  sorry

@[simp]
theorem fract_fract (a : α) : fract (fract a) = fract a :=
  fract_eq_self.2 ⟨fract_nonneg _, fract_lt_one _⟩

@[target]
theorem fract_add (a b : α) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
  sorry

theorem fract_neg {x : α} (hx : fract x ≠ 0) : fract (-x) = 1 - fract x := by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[target, simp]
theorem fract_neg_eq_zero {x : α} : fract (-x) = 0 ↔ fract x = 0 := by sorry

@[target]
theorem fract_mul_nat (a : α) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z := by sorry

theorem preimage_fract (s : Set α) :
    fract ⁻¹' s = ⋃ m : ℤ, (fun x => x - (m : α)) ⁻¹' (s ∩ Ico (0 : α) 1) := by
  ext x
  simp only [mem_preimage, mem_iUnion, mem_inter_iff]
  refine ⟨fun h => ⟨⌊x⌋, h, fract_nonneg x, fract_lt_one x⟩, ?_⟩
  rintro ⟨m, hms, hm0, hm1⟩
  obtain rfl : ⌊x⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 hm0, sub_lt_iff_lt_add'.1 hm1⟩
  exact hms

theorem image_fract (s : Set α) : fract '' s = ⋃ m : ℤ, (fun x : α => x - m) '' s ∩ Ico 0 1 := by
  ext x
  simp only [mem_image, mem_inter_iff, mem_iUnion]; constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⌊y⌋, ⟨y, hy, rfl⟩, fract_nonneg y, fract_lt_one y⟩
  · rintro ⟨m, ⟨y, hys, rfl⟩, h0, h1⟩
    obtain rfl : ⌊y⌋ = m := floor_eq_iff.2 ⟨sub_nonneg.1 h0, sub_lt_iff_lt_add'.1 h1⟩
    exact ⟨y, hys, rfl⟩

section LinearOrderedField

variable {k : Type*} [LinearOrderedField k] [FloorRing k] {b : k}

theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a ∈ Ico 0 a :=
  ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

theorem fract_div_mul_self_add_zsmul_eq (a b : k) (ha : a ≠ 0) :
    fract (b / a) * a + ⌊b / a⌋ • a = b := by
  rw [zsmul_eq_mul, ← add_mul, fract_add_floor, div_mul_cancel₀ b ha]

theorem sub_floor_div_mul_nonneg (a : k) (hb : 0 < b) : 0 ≤ a - ⌊a / b⌋ * b :=
  sub_nonneg_of_le <| (le_div_iff₀ hb).1 <| floor_le _

@[target]
theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b :=
  sorry

@[target]
theorem fract_div_natCast_eq_div_natCast_mod {m n : ℕ} : fract ((m : k) / n) = ↑(m % n) / n := by sorry

theorem fract_div_intCast_eq_div_intCast_mod {m : ℤ} {n : ℕ} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  replace hn : 0 < (n : k) := by norm_cast
  have : ∀ {l : ℤ}, 0 ≤ l → fract ((l : k) / n) = ↑(l % n) / n := by
    intros l hl
    obtain ⟨l₀, rfl | rfl⟩ := l.eq_nat_or_neg
    · rw [cast_natCast, ← natCast_mod, cast_natCast, fract_div_natCast_eq_div_natCast_mod]
    · rw [Right.nonneg_neg_iff, natCast_nonpos_iff] at hl
      simp [hl]
  obtain ⟨m₀, rfl | rfl⟩ := m.eq_nat_or_neg
  · exact this (ofNat_nonneg m₀)
  let q := ⌈↑m₀ / (n : k)⌉
  let m₁ := q * ↑n - (↑m₀ : ℤ)
  have hm₁ : 0 ≤ m₁ := by
    simpa [m₁, ← @cast_le k, ← div_le_iff₀ hn] using FloorRing.gc_ceil_coe.le_u_l _
  calc
    fract ((Int.cast (-(m₀ : ℤ)) : k) / (n : k))
      = fract (-(m₀ : k) / n) := by simp
    _ = fract ((m₁ : k) / n) := ?_
    _ = Int.cast (m₁ % (n : ℤ)) / Nat.cast n := this hm₁
    _ = Int.cast (-(↑m₀ : ℤ) % ↑n) / Nat.cast n := ?_
  · rw [← fract_int_add q, ← mul_div_cancel_right₀ (q : k) hn.ne', ← add_div, ← sub_eq_add_neg]
    simp [m₁]
  · congr 2
    simp only [m₁]
    rw [sub_eq_add_neg, add_comm (q * ↑n), add_mul_emod_self]

end LinearOrderedField

/-! #### Ceil -/

@[target]
theorem gc_ceil_coe : GaloisConnection ceil ((↑) : ℤ → α) :=
  sorry

@[target]
theorem ceil_le : ⌈a⌉ ≤ z ↔ a ≤ z :=
  sorry

@[target]
theorem floor_neg : ⌊-a⌋ = -⌈a⌉ :=
  sorry

@[target]
theorem ceil_neg : ⌈-a⌉ = -⌊a⌋ :=
  sorry

@[target]
theorem lt_ceil : z < ⌈a⌉ ↔ (z : α) < a :=
  sorry

@[simp]
theorem add_one_le_ceil_iff : z + 1 ≤ ⌈a⌉ ↔ (z : α) < a := by rw [← lt_ceil, add_one_le_iff]

@[target, simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉ ↔ 0 < a := by sorry

@[target, bound]
theorem ceil_le_floor_add_one (a : α) : ⌈a⌉ ≤ ⌊a⌋ + 1 := by sorry

@[bound]
theorem le_ceil (a : α) : a ≤ ⌈a⌉ :=
  gc_ceil_coe.le_u_l a

@[target]
lemma le_ceil_iff : z ≤ ⌈a⌉ ↔ z - 1 < a := by sorry
@[target]
lemma ceil_lt_iff : ⌈a⌉ < z ↔ a ≤ z - 1 := by sorry

@[target, simp]
theorem ceil_intCast (z : ℤ) : ⌈(z : α)⌉ = z :=
  sorry

@[target, simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : α)⌉ = n :=
  sorry

@[simp]
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : α)⌉ = ofNat(n) := ceil_natCast n

@[target]
theorem ceil_mono : Monotone (ceil : α → ℤ) :=
  sorry

@[gcongr, bound] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ := ceil_mono hab

@[target, simp]
theorem ceil_add_int (a : α) (z : ℤ) : ⌈a + z⌉ = ⌈a⌉ + z := by sorry

@[target, simp]
theorem ceil_add_nat (a : α) (n : ℕ) : ⌈a + n⌉ = ⌈a⌉ + n := by sorry

@[target, simp]
theorem ceil_add_one (a : α) : ⌈a + 1⌉ = ⌈a⌉ + 1 := by sorry

@[target, simp]
theorem ceil_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉ = ⌈a⌉ + ofNat(n) :=
  sorry

@[target, simp]
theorem ceil_sub_int (a : α) (z : ℤ) : ⌈a - z⌉ = ⌈a⌉ - z :=
  sorry

@[target, simp]
theorem ceil_sub_nat (a : α) (n : ℕ) : ⌈a - n⌉ = ⌈a⌉ - n := by sorry

@[target, simp]
theorem ceil_sub_one (a : α) : ⌈a - 1⌉ = ⌈a⌉ - 1 := by sorry

@[target, simp]
theorem ceil_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌈a - ofNat(n)⌉ = ⌈a⌉ - ofNat(n) :=
  sorry

@[target, bound]
theorem ceil_lt_add_one (a : α) : (⌈a⌉ : α) < a + 1 := by sorry

@[target, bound]
theorem ceil_add_le (a b : α) : ⌈a + b⌉ ≤ ⌈a⌉ + ⌈b⌉ := by sorry

@[target, bound]
theorem ceil_add_ceil_le (a b : α) : ⌈a⌉ + ⌈b⌉ ≤ ⌈a + b⌉ + 1 := by sorry

@[target, simp]
theorem ceil_pos : 0 < ⌈a⌉ ↔ 0 < a := by sorry

@[target, simp]
theorem ceil_zero : ⌈(0 : α)⌉ = 0 := by sorry

@[target, simp]
theorem ceil_one : ⌈(1 : α)⌉ = 1 := by sorry

@[target, bound]
theorem ceil_nonneg (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := sorry

@[target]
theorem ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ z := by sorry

@[target, simp]
theorem ceil_eq_zero_iff : ⌈a⌉ = 0 ↔ a ∈ Ioc (-1 : α) 0 := by sorry

theorem ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, ⌈a⌉ = z := fun _ ⟨h₀, h₁⟩ =>
  ceil_eq_iff.mpr ⟨h₀, h₁⟩

@[target]
theorem ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, (⌈a⌉ : α) = z := sorry

lemma ceil_eq_self_iff_mem (a : α) : ⌈a⌉ = a ↔ a ∈ Set.range Int.cast := by
  aesop

@[target, bound]
theorem floor_le_ceil (a : α) : ⌊a⌋ ≤ ⌈a⌉ :=
  sorry

@[target, bound]
theorem floor_lt_ceil_of_lt {a b : α} (h : a < b) : ⌊a⌋ < ⌈b⌉ :=
  sorry

@[target]
lemma ceil_eq_floor_add_one_iff_not_mem (a : α) : ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ Set.range Int.cast := by sorry

@[target, simp]
theorem preimage_ceil_singleton (m : ℤ) : (ceil : α → ℤ) ⁻¹' {m} = Ioc ((m : α) - 1) m :=
  sorry

theorem fract_eq_zero_or_add_one_sub_ceil (a : α) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : α) := by
  rcases eq_or_ne (fract a) 0 with ha | ha
  · exact Or.inl ha
  right
  suffices (⌈a⌉ : α) = ⌊a⌋ + 1 by
    rw [this, ← self_sub_fract]
    abel
  norm_cast
  rw [ceil_eq_iff]
  refine ⟨?_, _root_.le_of_lt <| by simp⟩
  rw [cast_add, cast_one, add_tsub_cancel_right, ← self_sub_fract a, sub_lt_self_iff]
  exact ha.symm.lt_of_le (fract_nonneg a)

@[target]
theorem ceil_eq_add_one_sub_fract (ha : fract a ≠ 0) : (⌈a⌉ : α) = a + 1 - fract a := by sorry

theorem ceil_sub_self_eq (ha : fract a ≠ 0) : (⌈a⌉ : α) - a = 1 - fract a := by
  rw [(or_iff_right ha).mp (fract_eq_zero_or_add_one_sub_ceil a)]
  abel

section LinearOrderedField
variable {k : Type*} [LinearOrderedField k] [FloorRing k] {a b : k}

@[target]
lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ ≤ a) : b * a < ⌊a⌋ := by sorry

@[target]
lemma ceil_div_ceil_inv_sub_one (ha : 1 ≤ a) : ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉ := by sorry

@[target]
lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a) : ⌈a⌉ < b * a := by sorry

@[target]
lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b ≤ a) : ⌈a⌉ ≤ b * a := by sorry

@[target]
lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋ := by sorry

@[target]
lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉ < 2 * a :=
  sorry

@[target]
lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉ ≤ 2 * a :=
  sorry

end LinearOrderedField

/-! #### Intervals -/

@[simp]
theorem preimage_Ioo {a b : α} : ((↑) : ℤ → α) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋ ⌈b⌉ := by
  ext
  simp [floor_lt, lt_ceil]

@[simp]
theorem preimage_Ico {a b : α} : ((↑) : ℤ → α) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉ ⌈b⌉ := by
  ext
  simp [ceil_le, lt_ceil]

@[target, simp]
theorem preimage_Ioc {a b : α} : ((↑) : ℤ → α) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ ⌊b⌋ := by sorry

@[simp]
theorem preimage_Icc {a b : α} : ((↑) : ℤ → α) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ ⌊b⌋ := by
  ext
  simp [ceil_le, le_floor]

@[target, simp]
theorem preimage_Ioi : ((↑) : ℤ → α) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ := by sorry

@[target, simp]
theorem preimage_Ici : ((↑) : ℤ → α) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ := by sorry

@[simp]
theorem preimage_Iio : ((↑) : ℤ → α) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ := by
  ext
  simp [lt_ceil]

@[target, simp]
theorem preimage_Iic : ((↑) : ℤ → α) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ := by sorry

end Int

open Int

namespace Nat

variable [LinearOrderedSemiring α] [LinearOrderedSemiring β] [FloorSemiring α] [FloorSemiring β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem floor_congr (h : ∀ n : ℕ, (n : α) ≤ a ↔ (n : β) ≤ b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  have h₀ : 0 ≤ a ↔ 0 ≤ b := by simpa only [cast_zero] using h 0
  obtain ha | ha := lt_or_le a 0
  · rw [floor_of_nonpos ha.le, floor_of_nonpos (le_of_not_le <| h₀.not.mp ha.not_le)]
  exact (le_floor <| (h _).1 <| floor_le ha).antisymm (le_floor <| (h _).2 <| floor_le <| h₀.1 ha)

theorem ceil_congr (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : ⌈a⌉₊ = ⌈b⌉₊ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _

theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋₊ = ⌊a⌋₊ :=
  floor_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉₊ = ⌈a⌉₊ :=
  ceil_congr fun n => by rw [← map_natCast f, hf.le_iff_le]

end Nat

namespace Int

variable [LinearOrderedRing α] [LinearOrderedRing β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

@[target]
theorem floor_congr (h : ∀ n : ℤ, (n : α) ≤ a ↔ (n : β) ≤ b) : ⌊a⌋ = ⌊b⌋ :=
  sorry

@[target]
theorem ceil_congr (h : ∀ n : ℤ, a ≤ n ↔ b ≤ n) : ⌈a⌉ = ⌈b⌉ :=
  sorry

@[target]
theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋ = ⌊a⌋ :=
  sorry

@[target]
theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉ = ⌈a⌉ :=
  sorry

theorem map_fract (f : F) (hf : StrictMono f) (a : α) : fract (f a) = f (fract a) := by
  simp_rw [fract, map_sub, map_intCast, map_floor _ hf]

end Int

section FloorRingToSemiring

variable [LinearOrderedRing α] [FloorRing α]

/-! #### A floor ring as a floor semiring -/


-- see Note [lower instance priority]
instance (priority := 100) FloorRing.toFloorSemiring : FloorSemiring α where
  floor a := ⌊a⌋.toNat
  ceil a := ⌈a⌉.toNat
  floor_of_neg {_} ha := Int.toNat_of_nonpos (Int.floor_nonpos ha.le)
  gc_floor {a n} ha := by rw [Int.le_toNat (Int.floor_nonneg.2 ha), Int.le_floor, Int.cast_natCast]
  gc_ceil a n := by rw [Int.toNat_le, Int.ceil_le, Int.cast_natCast]

theorem Int.floor_toNat (a : α) : ⌊a⌋.toNat = ⌊a⌋₊ :=
  rfl

theorem Int.ceil_toNat (a : α) : ⌈a⌉.toNat = ⌈a⌉₊ :=
  rfl

@[simp]
theorem Nat.floor_int : (Nat.floor : ℤ → ℕ) = Int.toNat :=
  rfl

@[target, simp]
theorem Nat.ceil_int : (Nat.ceil : ℤ → ℕ) = Int.toNat :=
  sorry

variable {a : α}

theorem Int.natCast_floor_eq_floor (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

@[target]
theorem Int.natCast_ceil_eq_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by sorry

theorem natCast_floor_eq_intCast_floor (ha : 0 ≤ a) : (⌊a⌋₊ : α) = ⌊a⌋ := by
  rw [← Int.natCast_floor_eq_floor ha, Int.cast_natCast]

theorem natCast_ceil_eq_intCast_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : α) = ⌈a⌉ := by
  rw [← Int.natCast_ceil_eq_ceil ha, Int.cast_natCast]

@[deprecated (since := "2024-08-20")] alias Int.ofNat_floor_eq_floor := natCast_floor_eq_floor
@[deprecated (since := "2024-08-20")] alias Int.ofNat_ceil_eq_ceil := natCast_ceil_eq_ceil

end FloorRingToSemiring

/-- There exists at most one `FloorRing` structure on a given linear ordered ring. -/
@[target]
theorem subsingleton_floorRing {α} [LinearOrderedRing α] : Subsingleton (FloorRing α) := by sorry

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

private theorem int_floor_nonneg [LinearOrderedRing α] [FloorRing α] {a : α} (ha : 0 ≤ a) :
    0 ≤ ⌊a⌋ :=
  Int.floor_nonneg.2 ha

private theorem int_floor_nonneg_of_pos [LinearOrderedRing α] [FloorRing α] {a : α}
    (ha : 0 < a) :
    0 ≤ ⌊a⌋ :=
  int_floor_nonneg ha.le

/-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
@[positivity ⌊ _ ⌋]
def evalIntFloor : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α' $i $j $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg_of_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(int_floor_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.floor application"

private theorem nat_ceil_pos [LinearOrderedSemiring α] [FloorSemiring α] {a : α} :
    0 < a → 0 < ⌈a⌉₊ :=
  Nat.ceil_pos.2

/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
@[positivity ⌈ _ ⌉₊]
def evalNatCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α' $i $j $a) =>
    let _i : Q(LinearOrderedSemiring $α') ← synthInstanceQ (u := u_1) _
    assertInstancesCommute
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
      assertInstancesCommute
      pure (.positive q(nat_ceil_pos (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Nat.ceil application"

private theorem int_ceil_pos [LinearOrderedRing α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ :=
  Int.ceil_pos.2

/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
@[positivity ⌈ _ ⌉]
def evalIntCeil : PositivityExt where eval {u α} _zα _pα e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α' $i $j $a) =>
    match ← core q(inferInstance) q(inferInstance) a with
    | .positive pa =>
        assertInstancesCommute
        pure (.positive q(int_ceil_pos (α := $α') $pa))
    | .nonnegative pa =>
        assertInstancesCommute
        pure (.nonnegative q(Int.ceil_nonneg (α := $α') $pa))
    | _ => pure .none
  | _, _, _ => throwError "failed to match on Int.ceil application"

end Mathlib.Meta.Positivity
