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
/-- `⌊a⌋₊` is the greatest natural `n` such that `n ≤ a`. If `a` is negative, then `⌊a⌋₊ = 0`. -/
def floor : α → ℕ := by sorry


/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
/-- `⌈a⌉₊` is the least natural `n` such that `a ≤ n` -/
def ceil : α → ℕ := by sorry


@[target] theorem floor_nat : (Nat.floor : ℕ → ℕ) = id := by sorry


@[simp]
theorem ceil_nat : (Nat.ceil : ℕ → ℕ) = id :=
  rfl

@[inherit_doc]
notation "⌊" a "⌋₊" => Nat.floor a

@[inherit_doc]
notation "⌈" a "⌉₊" => Nat.ceil a

@[target] theorem le_floor_iff (ha : 0 ≤ a) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a := by sorry


@[target] theorem le_floor (h : (n : α) ≤ a) : n ≤ ⌊a⌋₊ := by sorry


@[target] theorem gc_ceil_coe : GaloisConnection (ceil : α → ℕ) (↑) := by sorry


@[target] theorem ceil_le : ⌈a⌉₊ ≤ n ↔ a ≤ n := by sorry


end OrderedSemiring

section LinearOrderedSemiring

variable [LinearOrderedSemiring α] [FloorSemiring α] {a b : α} {n : ℕ}

@[target] theorem floor_lt (ha : 0 ≤ a) : ⌊a⌋₊ < n ↔ a < n := by sorry


@[target] theorem floor_lt_one (ha : 0 ≤ a) : ⌊a⌋₊ < 1 ↔ a < 1 :=
  (floor_lt ha).trans <| by sorry


theorem lt_of_floor_lt (h : ⌊a⌋₊ < n) : a < n :=
  lt_of_not_le fun h' => (le_floor h').not_lt h

@[target] theorem lt_one_of_floor_lt_one (h : ⌊a⌋₊ < 1) : a < 1 := by sorry


@[target] theorem floor_le (ha : 0 ≤ a) : (⌊a⌋₊ : α) ≤ a := by sorry


@[target] theorem lt_succ_floor (a : α) : a < ⌊a⌋₊.succ := by sorry


@[target] theorem lt_floor_add_one (a : α) : a < ⌊a⌋₊ + 1 := by sorry


@[target] theorem floor_natCast (n : ℕ) : ⌊(n : α)⌋₊ = n :=
  eq_of_forall_le_iff fun a => by
    sorry


@[target] theorem floor_zero : ⌊(0 : α)⌋₊ = 0 := by sorry


@[target] theorem floor_one : ⌊(1 : α)⌋₊ = 1 := by sorry


@[target] theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : α)⌋₊ = ofNat(n) := by sorry


@[target] theorem floor_of_nonpos (ha : a ≤ 0) : ⌊a⌋₊ = 0 :=
  ha.lt_or_eq.elim FloorSemiring.floor_of_neg <| by
    sorry


@[target] theorem floor_mono : Monotone (floor : α → ℕ) := fun a b h => by
  sorry


@[target] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋₊ ≤ ⌊b⌋₊ := by sorry


theorem le_floor_iff' (hn : n ≠ 0) : n ≤ ⌊a⌋₊ ↔ (n : α) ≤ a := by
  obtain ha | ha := le_total a 0
  · rw [floor_of_nonpos ha]
    exact
      iff_of_false (Nat.pos_of_ne_zero hn).not_le
        (not_le_of_lt <| ha.trans_lt <| cast_pos.2 <| Nat.pos_of_ne_zero hn)
  · exact le_floor_iff ha

@[target] theorem one_le_floor_iff (x : α) : 1 ≤ ⌊x⌋₊ ↔ 1 ≤ x := by sorry


theorem floor_lt' (hn : n ≠ 0) : ⌊a⌋₊ < n ↔ a < n :=
  lt_iff_lt_of_le_iff_le <| le_floor_iff' hn

@[target] theorem floor_pos : 0 < ⌊a⌋₊ ↔ 1 ≤ a := by
  sorry


@[target] theorem pos_of_floor_pos (h : 0 < ⌊a⌋₊) : 0 < a :=
  (le_or_lt a 0).resolve_left fun ha => lt_irrefl 0 <| by sorry


@[target] theorem lt_of_lt_floor (h : n < ⌊a⌋₊) : ↑n < a := by sorry


@[target] theorem floor_le_of_le (h : a ≤ n) : ⌊a⌋₊ ≤ n := by sorry


@[target] theorem floor_le_one_of_le_one (h : a ≤ 1) : ⌊a⌋₊ ≤ 1 := by sorry


@[simp]
theorem floor_eq_zero : ⌊a⌋₊ = 0 ↔ a < 1 := by
  rw [← lt_one_iff, ← @cast_one α]
  exact floor_lt' Nat.one_ne_zero

@[target] theorem floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  sorry


theorem floor_eq_iff' (hn : n ≠ 0) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1 := by
  rw [← le_floor_iff' hn, ← Nat.cast_one, ← Nat.cast_add, ← floor_lt' (Nat.add_one_ne_zero n),
    Nat.lt_add_one_iff, le_antisymm_iff, and_comm]

@[target] theorem floor_eq_on_Ico (n : ℕ) : ∀ a ∈ (Set.Ico n (n + 1) : Set α), ⌊a⌋₊ = n := by sorry


theorem floor_eq_on_Ico' (n : ℕ) :
    ∀ a ∈ (Set.Ico n (n + 1) : Set α), (⌊a⌋₊ : α) = n :=
  fun x hx => mod_cast floor_eq_on_Ico n x hx

@[target] theorem preimage_floor_zero : (floor : α → ℕ) ⁻¹' {0} = Iio 1 := by sorry


theorem preimage_floor_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (floor : α → ℕ) ⁻¹' {n} = Ico (n : α) (n + 1) :=
  ext fun _ => floor_eq_iff' hn

/-! #### Ceil -/

@[target] theorem lt_ceil : n < ⌈a⌉₊ ↔ (n : α) < a := by sorry


@[target] theorem add_one_le_ceil_iff : n + 1 ≤ ⌈a⌉₊ ↔ (n : α) < a := by
  sorry


@[target] theorem one_le_ceil_iff : 1 ≤ ⌈a⌉₊ ↔ 0 < a := by
  sorry


@[target] theorem ceil_le_floor_add_one (a : α) : ⌈a⌉₊ ≤ ⌊a⌋₊ + 1 := by
  sorry


@[bound]
theorem le_ceil (a : α) : a ≤ ⌈a⌉₊ :=
  ceil_le.1 le_rfl

@[target] theorem ceil_intCast {α : Type*} [LinearOrderedRing α] [FloorSemiring α] (z : ℤ) :
    ⌈(z : α)⌉₊ = z.toNat :=
  eq_of_forall_ge_iff fun a => by
    sorry


@[target] theorem ceil_natCast (n : ℕ) : ⌈(n : α)⌉₊ = n :=
  eq_of_forall_ge_iff fun a => by sorry


@[target] theorem ceil_mono : Monotone (ceil : α → ℕ) := by sorry


@[target] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉₊ ≤ ⌈b⌉₊ := by sorry


@[target] theorem ceil_zero : ⌈(0 : α)⌉₊ = 0 := by sorry


@[target] theorem ceil_one : ⌈(1 : α)⌉₊ = 1 := by sorry


@[target] theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : α)⌉₊ = ofNat(n) := by sorry


@[target] theorem ceil_eq_zero : ⌈a⌉₊ = 0 ↔ a ≤ 0 := by sorry


@[target] theorem ceil_pos : 0 < ⌈a⌉₊ ↔ 0 < a := by sorry


theorem lt_of_ceil_lt (h : ⌈a⌉₊ < n) : a < n :=
  (le_ceil a).trans_lt (Nat.cast_lt.2 h)

theorem le_of_ceil_le (h : ⌈a⌉₊ ≤ n) : a ≤ n :=
  (le_ceil a).trans (Nat.cast_le.2 h)

@[target] theorem floor_le_ceil (a : α) : ⌊a⌋₊ ≤ ⌈a⌉₊ := by
  sorry


@[target] theorem floor_lt_ceil_of_lt_of_pos {a b : α} (h : a < b) (h' : 0 < b) : ⌊a⌋₊ < ⌈b⌉₊ := by
  sorry


@[target] theorem ceil_eq_iff (hn : n ≠ 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ n := by
  sorry


@[target] theorem preimage_ceil_zero : (Nat.ceil : α → ℕ) ⁻¹' {0} = Iic 0 := by sorry


@[target] theorem preimage_ceil_of_ne_zero (hn : n ≠ 0) : (Nat.ceil : α → ℕ) ⁻¹' {n} = Ioc (↑(n - 1) : α) n := by sorry


@[target] theorem preimage_Ioo {a b : α} (ha : 0 ≤ a) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Ioo a b = Set.Ioo ⌊a⌋₊ ⌈b⌉₊ := by
  sorry


@[target] theorem preimage_Ico {a b : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Ico a b = Set.Ico ⌈a⌉₊ ⌈b⌉₊ := by
  sorry


@[target] theorem preimage_Ioc {a b : α} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
  sorry


@[target] theorem preimage_Icc {a b : α} (hb : 0 ≤ b) :
    (Nat.cast : ℕ → α) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊ := by
  sorry


@[target] theorem preimage_Ioi {a : α} (ha : 0 ≤ a) : (Nat.cast : ℕ → α) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋₊ := by
  sorry


@[target] theorem preimage_Ici {a : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉₊ := by
  sorry


@[target] theorem preimage_Iio {a : α} : (Nat.cast : ℕ → α) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉₊ := by
  sorry


@[target] theorem preimage_Iic {a : α} (ha : 0 ≤ a) : (Nat.cast : ℕ → α) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋₊ := by
  sorry


@[target] theorem floor_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌊a + n⌋₊ = ⌊a⌋₊ + n :=
  eq_of_forall_le_iff fun b => by
    sorry


@[target] theorem floor_add_one (ha : 0 ≤ a) : ⌊a + 1⌋₊ = ⌊a⌋₊ + 1 := by
  sorry


@[target] theorem floor_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋₊ = ⌊a⌋₊ + ofNat(n) := by sorry


@[target] theorem floor_sub_nat [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) (n : ℕ) :
    ⌊a - n⌋₊ = ⌊a⌋₊ - n := by
  sorry


@[target] theorem floor_sub_one [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) : ⌊a - 1⌋₊ = ⌊a⌋₊ - 1 := by sorry


@[target] theorem floor_sub_ofNat [Sub α] [OrderedSub α] [ExistsAddOfLE α] (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋₊ = ⌊a⌋₊ - ofNat(n) := by sorry


theorem ceil_add_nat (ha : 0 ≤ a) (n : ℕ) : ⌈a + n⌉₊ = ⌈a⌉₊ + n :=
  eq_of_forall_ge_iff fun b => by
    rw [← not_lt, ← not_lt, not_iff_not, lt_ceil]
    obtain hb | hb := le_or_lt n b
    · obtain ⟨d, rfl⟩ := exists_add_of_le hb
      rw [Nat.cast_add, add_comm n, add_comm (n : α), add_lt_add_iff_right, add_lt_add_iff_right,
        lt_ceil]
    · exact iff_of_true (lt_add_of_nonneg_of_lt ha <| cast_lt.2 hb) (Nat.lt_add_left _ hb)

@[target] theorem ceil_add_one (ha : 0 ≤ a) : ⌈a + 1⌉₊ = ⌈a⌉₊ + 1 := by
  sorry


@[target] theorem ceil_add_ofNat (ha : 0 ≤ a) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉₊ = ⌈a⌉₊ + ofNat(n) := by sorry


@[target] theorem ceil_lt_add_one (ha : 0 ≤ a) : (⌈a⌉₊ : α) < a + 1 := by sorry


@[target] theorem ceil_add_le (a b : α) : ⌈a + b⌉₊ ≤ ⌈a⌉₊ + ⌈b⌉₊ := by
  sorry


end LinearOrderedSemiring

section LinearOrderedRing

variable [LinearOrderedRing α] [FloorSemiring α]

@[target] theorem sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋₊ := by sorry


end LinearOrderedRing

section LinearOrderedSemifield

variable [LinearOrderedSemifield α] [FloorSemiring α]

-- TODO: should these lemmas be `simp`? `norm_cast`?

@[target] theorem floor_div_nat (a : α) (n : ℕ) : ⌊a / n⌋₊ = ⌊a⌋₊ / n := by
  sorry


@[target] theorem floor_div_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a / ofNat(n)⌋₊ = ⌊a⌋₊ / ofNat(n) := by sorry


/-- Natural division is the floor of field division. -/
/-- Natural division is the floor of field division. -/
@[target] theorem floor_div_eq_div (m n : ℕ) : ⌊(m : α) / n⌋₊ = m / n := by
  sorry


end LinearOrderedSemifield

section LinearOrderedField
variable [LinearOrderedField α] [FloorSemiring α] {a b : α}

@[target] lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉₊ ≤ a) : b * a < ⌊a⌋₊ := by
  sorry


@[target] lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b < a) : ⌈a⌉₊ < b * a := by
  sorry


@[target] lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉₊ / b ≤ a) : ⌈a⌉₊ ≤ b * a := by
  sorry


@[target] lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋₊ := by
  sorry


@[target] lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉₊ < 2 * a :=
  ceil_lt_mul one_lt_two (by sorry


@[target] lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉₊ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by sorry


end LinearOrderedField
end Nat

/-- There exists at most one `FloorSemiring` structure on a linear ordered semiring. -/
/-- There exists at most one `FloorSemiring` structure on a linear ordered semiring. -/
@[target] theorem subsingleton_floorSemiring {α} [LinearOrderedSemiring α] :
    Subsingleton (FloorSemiring α) := by
  sorry


/-- A `FloorRing` is a linear ordered ring over `α` with a function
`floor : α → ℤ` satisfying `∀ (z : ℤ) (a : α), z ≤ floor a ↔ (z : α) ≤ a)`.
-/
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
/-- `Int.fract a` the fractional part of `a`, is `a` minus its floor. -/
def fract (a : α) : α := by sorry


@[simp]
theorem floor_int : (Int.floor : ℤ → ℤ) = id :=
  rfl

@[simp]
theorem ceil_int : (Int.ceil : ℤ → ℤ) = id :=
  rfl

@[target] theorem fract_int : (Int.fract : ℤ → ℤ) = 0 :=
  funext fun x => by sorry


@[inherit_doc]
notation "⌊" a "⌋" => Int.floor a

@[inherit_doc]
notation "⌈" a "⌉" => Int.ceil a

-- Mathematical notation for `fract a` is usually `{a}`. Let's not even go there.

@[target] theorem floorRing_floor_eq : @FloorRing.floor = @Int.floor := by sorry


@[target] theorem floorRing_ceil_eq : @FloorRing.ceil = @Int.ceil := by sorry


theorem gc_coe_floor : GaloisConnection ((↑) : ℤ → α) floor :=
  FloorRing.gc_coe_floor

theorem le_floor : z ≤ ⌊a⌋ ↔ (z : α) ≤ a :=
  (gc_coe_floor z a).symm

theorem floor_lt : ⌊a⌋ < z ↔ a < z :=
  lt_iff_lt_of_le_iff_le le_floor

@[bound]
theorem floor_le (a : α) : (⌊a⌋ : α) ≤ a :=
  gc_coe_floor.l_u_le a

@[target] theorem floor_le_iff : ⌊a⌋ ≤ z ↔ a < z + 1 := by sorry

@[target] theorem lt_floor_iff : z < ⌊a⌋ ↔ z + 1 ≤ a := by sorry


@[target] theorem floor_nonneg : 0 ≤ ⌊a⌋ ↔ 0 ≤ a := by sorry


@[target] theorem floor_le_sub_one_iff : ⌊a⌋ ≤ z - 1 ↔ a < z := by sorry


@[target] theorem floor_le_neg_one_iff : ⌊a⌋ ≤ -1 ↔ a < 0 := by
  sorry


@[target] theorem floor_nonpos (ha : a ≤ 0) : ⌊a⌋ ≤ 0 := by
  sorry


theorem lt_succ_floor (a : α) : a < ⌊a⌋.succ :=
  floor_lt.1 <| Int.lt_succ_self _

@[simp, bound]
theorem lt_floor_add_one (a : α) : a < ⌊a⌋ + 1 := by
  simpa only [Int.succ, Int.cast_add, Int.cast_one] using lt_succ_floor a

@[simp, bound]
theorem sub_one_lt_floor (a : α) : a - 1 < ⌊a⌋ :=
  sub_lt_iff_lt_add.2 (lt_floor_add_one a)

@[target] theorem floor_intCast (z : ℤ) : ⌊(z : α)⌋ = z :=
  eq_of_forall_le_iff fun a => by sorry


@[simp]
theorem floor_natCast (n : ℕ) : ⌊(n : α)⌋ = n :=
  eq_of_forall_le_iff fun a => by rw [le_floor, ← cast_natCast, cast_le]

@[simp]
theorem floor_zero : ⌊(0 : α)⌋ = 0 := by rw [← cast_zero, floor_intCast]

@[simp]
theorem floor_one : ⌊(1 : α)⌋ = 1 := by rw [← cast_one, floor_intCast]

@[simp] theorem floor_ofNat (n : ℕ) [n.AtLeastTwo] : ⌊(ofNat(n) : α)⌋ = ofNat(n) :=
  floor_natCast n

@[mono]
theorem floor_mono : Monotone (floor : α → ℤ) :=
  gc_coe_floor.monotone_u

@[gcongr, bound] lemma floor_le_floor (hab : a ≤ b) : ⌊a⌋ ≤ ⌊b⌋ := floor_mono hab

theorem floor_pos : 0 < ⌊a⌋ ↔ 1 ≤ a := by
  rw [Int.lt_iff_add_one_le, zero_add, le_floor, cast_one]

@[simp]
theorem floor_add_int (a : α) (z : ℤ) : ⌊a + z⌋ = ⌊a⌋ + z :=
  eq_of_forall_le_iff fun a => by
    rw [le_floor, ← sub_le_iff_le_add, ← sub_le_iff_le_add, le_floor, Int.cast_sub]

@[simp]
theorem floor_add_one (a : α) : ⌊a + 1⌋ = ⌊a⌋ + 1 := by
  rw [← cast_one, floor_add_int]

@[target] theorem le_floor_add (a b : α) : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := by
  sorry


@[target] theorem le_floor_add_floor (a b : α) : ⌊a + b⌋ - 1 ≤ ⌊a⌋ + ⌊b⌋ := by
  sorry


@[target] theorem floor_int_add (z : ℤ) (a : α) : ⌊↑z + a⌋ = z + ⌊a⌋ := by
  sorry


@[simp]
theorem floor_add_nat (a : α) (n : ℕ) : ⌊a + n⌋ = ⌊a⌋ + n := by
  rw [← Int.cast_natCast, floor_add_int]

@[simp]
theorem floor_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a + ofNat(n)⌋ = ⌊a⌋ + ofNat(n) :=
  floor_add_nat a n

@[simp]
theorem floor_nat_add (n : ℕ) (a : α) : ⌊↑n + a⌋ = n + ⌊a⌋ := by
  rw [← Int.cast_natCast, floor_int_add]

@[target] theorem floor_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : α) :
    ⌊ofNat(n) + a⌋ = ofNat(n) + ⌊a⌋ := by sorry


@[simp]
theorem floor_sub_int (a : α) (z : ℤ) : ⌊a - z⌋ = ⌊a⌋ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (floor_add_int _ _)

@[simp]
theorem floor_sub_nat (a : α) (n : ℕ) : ⌊a - n⌋ = ⌊a⌋ - n := by
  rw [← Int.cast_natCast, floor_sub_int]

@[simp] theorem floor_sub_one (a : α) : ⌊a - 1⌋ = ⌊a⌋ - 1 := mod_cast floor_sub_nat a 1

@[simp]
theorem floor_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌊a - ofNat(n)⌋ = ⌊a⌋ - ofNat(n) :=
  floor_sub_nat a n

@[target] theorem abs_sub_lt_one_of_floor_eq_floor {α : Type*} [LinearOrderedCommRing α] [FloorRing α]
    {a b : α} (h : ⌊a⌋ = ⌊b⌋) : |a - b| < 1 := by
  sorry


theorem floor_eq_iff : ⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z + 1 := by
  rw [le_antisymm_iff, le_floor, ← Int.lt_add_one_iff, floor_lt, Int.cast_add, Int.cast_one,
    and_comm]

@[target] theorem floor_eq_zero_iff : ⌊a⌋ = 0 ↔ a ∈ Ico (0 : α) 1 := by sorry


theorem floor_eq_on_Ico (n : ℤ) : ∀ a ∈ Set.Ico (n : α) (n + 1), ⌊a⌋ = n := fun _ ⟨h₀, h₁⟩ =>
  floor_eq_iff.mpr ⟨h₀, h₁⟩

theorem floor_eq_on_Ico' (n : ℤ) : ∀ a ∈ Set.Ico (n : α) (n + 1), (⌊a⌋ : α) = n := fun a ha =>
  congr_arg _ <| floor_eq_on_Ico n a ha

@[target] theorem preimage_floor_singleton (m : ℤ) : (floor : α → ℤ) ⁻¹' {m} = Ico (m : α) (m + 1) := by sorry


@[target] lemma floor_eq_self_iff_mem (a : α) : ⌊a⌋ = a ↔ a ∈ Set.range Int.cast := by
  sorry



@[target] theorem self_sub_floor (a : α) : a - ⌊a⌋ = fract a := by sorry


@[target] theorem floor_add_fract (a : α) : (⌊a⌋ : α) + fract a = a := by sorry


@[target] theorem fract_add_floor (a : α) : fract a + ⌊a⌋ = a := by sorry


@[target] theorem fract_add_int (a : α) (m : ℤ) : fract (a + m) = fract a := by
  sorry


@[simp]
theorem fract_add_nat (a : α) (m : ℕ) : fract (a + m) = fract a := by
  rw [fract]
  simp

@[target] theorem fract_add_one (a : α) : fract (a + 1) = fract a := by sorry


@[target] theorem fract_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    fract (a + ofNat(n)) = fract a := by sorry


@[target] theorem fract_int_add (m : ℤ) (a : α) : fract (↑m + a) = fract a := by sorry


@[simp]
theorem fract_nat_add (n : ℕ) (a : α) : fract (↑n + a) = fract a := by rw [add_comm, fract_add_nat]

@[target] theorem fract_one_add (a : α) : fract (1 + a) = fract a := by sorry


@[target] theorem fract_ofNat_add (n : ℕ) [n.AtLeastTwo] (a : α) :
    fract (ofNat(n) + a) = fract a := by sorry


@[simp]
theorem fract_sub_int (a : α) (m : ℤ) : fract (a - m) = fract a := by
  rw [fract]
  simp

@[simp]
theorem fract_sub_nat (a : α) (n : ℕ) : fract (a - n) = fract a := by
  rw [fract]
  simp

@[target] theorem fract_sub_one (a : α) : fract (a - 1) = fract a := by sorry


@[target] theorem fract_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    fract (a - ofNat(n)) = fract a := by sorry


theorem fract_add_le (a b : α) : fract (a + b) ≤ fract a + fract b := by
  rw [fract, fract, fract, sub_add_sub_comm, sub_le_sub_iff_left, ← Int.cast_add, Int.cast_le]
  exact le_floor_add _ _

@[target] theorem fract_add_fract_le (a b : α) : fract a + fract b ≤ fract (a + b) + 1 := by
  sorry


@[target] theorem self_sub_fract (a : α) : a - fract a = ⌊a⌋ := by sorry


@[target] theorem fract_sub_self (a : α) : fract a - a = -⌊a⌋ := by sorry


@[target] theorem fract_nonneg (a : α) : 0 ≤ fract a := by sorry


/-- The fractional part of `a` is positive if and only if `a ≠ ⌊a⌋`. -/
/-- The fractional part of `a` is positive if and only if `a ≠ ⌊a⌋`. -/
@[target] lemma fract_pos : 0 < fract a ↔ a ≠ ⌊a⌋ := by sorry


@[target] theorem fract_lt_one (a : α) : fract a < 1 := by sorry


@[target] theorem fract_zero : fract (0 : α) = 0 := by sorry


@[target] theorem fract_one : fract (1 : α) = 0 := by sorry


@[target] theorem abs_fract : |fract a| = fract a := by sorry


@[simp]
theorem abs_one_sub_fract : |1 - fract a| = 1 - fract a :=
  abs_eq_self.mpr <| sub_nonneg.mpr (fract_lt_one a).le

@[simp]
theorem fract_intCast (z : ℤ) : fract (z : α) = 0 := by
  unfold fract
  rw [floor_intCast]
  exact sub_self _

@[simp]
theorem fract_natCast (n : ℕ) : fract (n : α) = 0 := by simp [fract]

@[target] theorem fract_ofNat (n : ℕ) [n.AtLeastTwo] :
    fract (ofNat(n) : α) = 0 := by sorry


theorem fract_floor (a : α) : fract (⌊a⌋ : α) = 0 :=
  fract_intCast _

@[target] theorem floor_fract (a : α) : ⌊fract a⌋ = 0 := by
  sorry


@[target] theorem fract_eq_iff {a b : α} : fract a = b ↔ 0 ≤ b ∧ b < 1 ∧ ∃ z : ℤ, a - b = z :=
  ⟨fun h => by
    sorry


@[target] theorem fract_eq_fract {a b : α} : fract a = fract b ↔ ∃ z : ℤ, a - b = z :=
  ⟨fun h => ⟨⌊a⌋ - ⌊b⌋, by sorry


@[target] theorem fract_eq_self {a : α} : fract a = a ↔ 0 ≤ a ∧ a < 1 :=
  fract_eq_iff.trans <| and_assoc.symm.trans <| and_iff_left ⟨0, by sorry


@[target] theorem fract_fract (a : α) : fract (fract a) = fract a := by sorry


theorem fract_add (a b : α) : ∃ z : ℤ, fract (a + b) - fract a - fract b = z :=
  ⟨⌊a⌋ + ⌊b⌋ - ⌊a + b⌋, by
    unfold fract
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg, cast_add, cast_neg]
    abel⟩

theorem fract_neg {x : α} (hx : fract x ≠ 0) : fract (-x) = 1 - fract x := by
  rw [fract_eq_iff]
  constructor
  · rw [le_sub_iff_add_le, zero_add]
    exact (fract_lt_one x).le
  refine ⟨sub_lt_self _ (lt_of_le_of_ne' (fract_nonneg x) hx), -⌊x⌋ - 1, ?_⟩
  simp only [sub_sub_eq_add_sub, cast_sub, cast_neg, cast_one, sub_left_inj]
  conv in -x => rw [← floor_add_fract x]
  simp [-floor_add_fract]

@[simp]
theorem fract_neg_eq_zero {x : α} : fract (-x) = 0 ↔ fract x = 0 := by
  simp only [fract_eq_iff, le_refl, zero_lt_one, tsub_zero, true_and]
  constructor <;> rintro ⟨z, hz⟩ <;> use -z <;> simp [← hz]

@[target] theorem fract_mul_nat (a : α) (b : ℕ) : ∃ z : ℤ, fract a * b - fract (a * b) = z := by
  sorry


@[target] theorem preimage_fract (s : Set α) :
    fract ⁻¹' s = ⋃ m : ℤ, (fun x => x - (m : α)) ⁻¹' (s ∩ Ico (0 : α) 1) := by
  sorry


@[target] theorem image_fract (s : Set α) : fract '' s = ⋃ m : ℤ, (fun x : α => x - m) '' s ∩ Ico 0 1 := by
  sorry


section LinearOrderedField

variable {k : Type*} [LinearOrderedField k] [FloorRing k] {b : k}

theorem fract_div_mul_self_mem_Ico (a b : k) (ha : 0 < a) : fract (b / a) * a ∈ Ico 0 a :=
  ⟨(mul_nonneg_iff_of_pos_right ha).2 (fract_nonneg (b / a)),
    (mul_lt_iff_lt_one_left ha).2 (fract_lt_one (b / a))⟩

theorem fract_div_mul_self_add_zsmul_eq (a b : k) (ha : a ≠ 0) :
    fract (b / a) * a + ⌊b / a⌋ • a = b := by
  rw [zsmul_eq_mul, ← add_mul, fract_add_floor, div_mul_cancel₀ b ha]

@[target] theorem sub_floor_div_mul_nonneg (a : k) (hb : 0 < b) : 0 ≤ a - ⌊a / b⌋ * b := by sorry


@[target] theorem sub_floor_div_mul_lt (a : k) (hb : 0 < b) : a - ⌊a / b⌋ * b < b :=
  sub_lt_iff_lt_add.2 <| by
    sorry


@[target] theorem fract_div_natCast_eq_div_natCast_mod {m n : ℕ} : fract ((m : k) / n) = ↑(m % n) / n := by
  sorry


@[target] theorem fract_div_intCast_eq_div_intCast_mod {m : ℤ} {n : ℕ} :
    fract ((m : k) / n) = ↑(m % n) / n := by
  sorry


end LinearOrderedField

/-! #### Ceil -/

theorem gc_ceil_coe : GaloisConnection ceil ((↑) : ℤ → α) :=
  FloorRing.gc_ceil_coe

theorem ceil_le : ⌈a⌉ ≤ z ↔ a ≤ z :=
  gc_ceil_coe a z

@[target] theorem floor_neg : ⌊-a⌋ = -⌈a⌉ :=
  eq_of_forall_le_iff fun z => by sorry


@[target] theorem ceil_neg : ⌈-a⌉ = -⌊a⌋ :=
  eq_of_forall_ge_iff fun z => by sorry


theorem lt_ceil : z < ⌈a⌉ ↔ (z : α) < a :=
  lt_iff_lt_of_le_iff_le ceil_le

@[simp]
theorem add_one_le_ceil_iff : z + 1 ≤ ⌈a⌉ ↔ (z : α) < a := by rw [← lt_ceil, add_one_le_iff]

@[simp]
theorem one_le_ceil_iff : 1 ≤ ⌈a⌉ ↔ 0 < a := by
  rw [← zero_add (1 : ℤ), add_one_le_ceil_iff, cast_zero]

@[bound]
theorem ceil_le_floor_add_one (a : α) : ⌈a⌉ ≤ ⌊a⌋ + 1 := by
  rw [ceil_le, Int.cast_add, Int.cast_one]
  exact (lt_floor_add_one a).le

@[bound]
theorem le_ceil (a : α) : a ≤ ⌈a⌉ :=
  gc_ceil_coe.le_u_l a

@[target] lemma le_ceil_iff : z ≤ ⌈a⌉ ↔ z - 1 < a := by sorry

@[target] lemma ceil_lt_iff : ⌈a⌉ < z ↔ a ≤ z - 1 := by sorry


@[simp]
theorem ceil_intCast (z : ℤ) : ⌈(z : α)⌉ = z :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, Int.cast_le]

@[simp]
theorem ceil_natCast (n : ℕ) : ⌈(n : α)⌉ = n :=
  eq_of_forall_ge_iff fun a => by rw [ceil_le, ← cast_natCast, cast_le]

@[simp]
theorem ceil_ofNat (n : ℕ) [n.AtLeastTwo] : ⌈(ofNat(n) : α)⌉ = ofNat(n) := ceil_natCast n

theorem ceil_mono : Monotone (ceil : α → ℤ) :=
  gc_ceil_coe.monotone_l

@[gcongr, bound] lemma ceil_le_ceil (hab : a ≤ b) : ⌈a⌉ ≤ ⌈b⌉ := ceil_mono hab

@[target] theorem ceil_add_int (a : α) (z : ℤ) : ⌈a + z⌉ = ⌈a⌉ + z := by
  sorry


@[simp]
theorem ceil_add_nat (a : α) (n : ℕ) : ⌈a + n⌉ = ⌈a⌉ + n := by rw [← Int.cast_natCast, ceil_add_int]

@[simp]
theorem ceil_add_one (a : α) : ⌈a + 1⌉ = ⌈a⌉ + 1 := by
  rw [← ceil_add_int a (1 : ℤ), cast_one]

@[simp]
theorem ceil_add_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌈a + ofNat(n)⌉ = ⌈a⌉ + ofNat(n) :=
  ceil_add_nat a n

@[simp]
theorem ceil_sub_int (a : α) (z : ℤ) : ⌈a - z⌉ = ⌈a⌉ - z :=
  Eq.trans (by rw [Int.cast_neg, sub_eq_add_neg]) (ceil_add_int _ _)

@[simp]
theorem ceil_sub_nat (a : α) (n : ℕ) : ⌈a - n⌉ = ⌈a⌉ - n := by
  convert ceil_sub_int a n using 1
  simp

@[target] theorem ceil_sub_one (a : α) : ⌈a - 1⌉ = ⌈a⌉ - 1 := by
  sorry


@[target] theorem ceil_sub_ofNat (a : α) (n : ℕ) [n.AtLeastTwo] :
    ⌈a - ofNat(n)⌉ = ⌈a⌉ - ofNat(n) := by sorry


@[bound]
theorem ceil_lt_add_one (a : α) : (⌈a⌉ : α) < a + 1 := by
  rw [← lt_ceil, ← Int.cast_one, ceil_add_int]
  apply lt_add_one

@[bound]
theorem ceil_add_le (a b : α) : ⌈a + b⌉ ≤ ⌈a⌉ + ⌈b⌉ := by
  rw [ceil_le, Int.cast_add]
  gcongr <;> apply le_ceil

@[target] theorem ceil_add_ceil_le (a b : α) : ⌈a⌉ + ⌈b⌉ ≤ ⌈a + b⌉ + 1 := by
  sorry


@[simp]
theorem ceil_pos : 0 < ⌈a⌉ ↔ 0 < a := by rw [lt_ceil, cast_zero]

@[simp]
theorem ceil_zero : ⌈(0 : α)⌉ = 0 := by rw [← cast_zero, ceil_intCast]

@[simp]
theorem ceil_one : ⌈(1 : α)⌉ = 1 := by rw [← cast_one, ceil_intCast]

@[target] theorem ceil_nonneg (ha : 0 ≤ a) : 0 ≤ ⌈a⌉ := by sorry


theorem ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a ≤ z := by
  rw [← ceil_le, ← Int.cast_one, ← Int.cast_sub, ← lt_ceil, Int.sub_one_lt_iff, le_antisymm_iff,
    and_comm]

@[target] theorem ceil_eq_zero_iff : ⌈a⌉ = 0 ↔ a ∈ Ioc (-1 : α) 0 := by sorry


@[target] theorem ceil_eq_on_Ioc (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, ⌈a⌉ = z := by sorry


theorem ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : α) z, (⌈a⌉ : α) = z := fun a ha =>
  mod_cast ceil_eq_on_Ioc z a ha

@[target] lemma ceil_eq_self_iff_mem (a : α) : ⌈a⌉ = a ↔ a ∈ Set.range Int.cast := by
  sorry


@[bound]
theorem floor_le_ceil (a : α) : ⌊a⌋ ≤ ⌈a⌉ :=
  cast_le.1 <| (floor_le _).trans <| le_ceil _

@[target] theorem floor_lt_ceil_of_lt {a b : α} (h : a < b) : ⌊a⌋ < ⌈b⌉ := by sorry


@[target] lemma ceil_eq_floor_add_one_iff_not_mem (a : α) : ⌈a⌉ = ⌊a⌋ + 1 ↔ a ∉ Set.range Int.cast := by
  sorry


@[target] theorem preimage_ceil_singleton (m : ℤ) : (ceil : α → ℤ) ⁻¹' {m} = Ioc ((m : α) - 1) m := by sorry


@[target] theorem fract_eq_zero_or_add_one_sub_ceil (a : α) : fract a = 0 ∨ fract a = a + 1 - (⌈a⌉ : α) := by
  sorry


@[target] theorem ceil_eq_add_one_sub_fract (ha : fract a ≠ 0) : (⌈a⌉ : α) = a + 1 - fract a := by
  sorry


@[target] theorem ceil_sub_self_eq (ha : fract a ≠ 0) : (⌈a⌉ : α) - a = 1 - fract a := by
  sorry


section LinearOrderedField
variable {k : Type*} [LinearOrderedField k] [FloorRing k] {a b : k}

lemma mul_lt_floor (hb₀ : 0 < b) (hb : b < 1) (hba : ⌈b / (1 - b)⌉ ≤ a) : b * a < ⌊a⌋ := by
  calc
    b * a < b * (⌊a⌋ + 1) := by gcongr; exacts [hb₀, lt_floor_add_one _]
    _ ≤ ⌊a⌋ := by
      rwa [_root_.mul_add_one, ← le_sub_iff_add_le', ← one_sub_mul, ← div_le_iff₀' (by linarith),
        ← ceil_le, le_floor]

@[target] lemma ceil_div_ceil_inv_sub_one (ha : 1 ≤ a) : ⌈⌈(a - 1)⁻¹⌉ / a⌉ = ⌈(a - 1)⁻¹⌉ := by
  sorry


lemma ceil_lt_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b < a) : ⌈a⌉ < b * a := by
  obtain hab | hba := le_total a (b - 1)⁻¹
  · calc
      ⌈a⌉ ≤ (⌈(b - 1)⁻¹⌉ : k) := by gcongr
      _ < b * a := by rwa [← div_lt_iff₀']; positivity
  · rw [← sub_pos] at hb
    calc
      ⌈a⌉ < a + 1 := ceil_lt_add_one _
      _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
      _ ≤ a + (b - 1) * a := by gcongr; positivity
      _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_le_mul (hb : 1 < b) (hba : ⌈(b - 1)⁻¹⌉ / b ≤ a) : ⌈a⌉ ≤ b * a := by
  obtain rfl | hba := hba.eq_or_lt
  · rw [ceil_div_ceil_inv_sub_one hb.le, mul_div_cancel₀]
    positivity
  · exact (ceil_lt_mul hb hba).le

lemma div_two_lt_floor (ha : 1 ≤ a) : a / 2 < ⌊a⌋ := by
  rw [div_eq_inv_mul]; refine mul_lt_floor ?_ ?_ ?_ <;> norm_num; assumption

lemma ceil_lt_two_mul (ha : 2⁻¹ < a) : ⌈a⌉ < 2 * a :=
  ceil_lt_mul one_lt_two (by norm_num at ha ⊢; exact ha)

lemma ceil_le_two_mul (ha : 2⁻¹ ≤ a) : ⌈a⌉ ≤ 2 * a :=
  ceil_le_mul one_lt_two (by norm_num at ha ⊢; exact ha)

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

@[simp]
theorem preimage_Ioc {a b : α} : ((↑) : ℤ → α) ⁻¹' Set.Ioc a b = Set.Ioc ⌊a⌋ ⌊b⌋ := by
  ext
  simp [floor_lt, le_floor]

@[simp]
theorem preimage_Icc {a b : α} : ((↑) : ℤ → α) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉ ⌊b⌋ := by
  ext
  simp [ceil_le, le_floor]

@[simp]
theorem preimage_Ioi : ((↑) : ℤ → α) ⁻¹' Set.Ioi a = Set.Ioi ⌊a⌋ := by
  ext
  simp [floor_lt]

@[simp]
theorem preimage_Ici : ((↑) : ℤ → α) ⁻¹' Set.Ici a = Set.Ici ⌈a⌉ := by
  ext
  simp [ceil_le]

@[simp]
theorem preimage_Iio : ((↑) : ℤ → α) ⁻¹' Set.Iio a = Set.Iio ⌈a⌉ := by
  ext
  simp [lt_ceil]

@[simp]
theorem preimage_Iic : ((↑) : ℤ → α) ⁻¹' Set.Iic a = Set.Iic ⌊a⌋ := by
  ext
  simp [le_floor]

end Int

open Int

namespace Nat

variable [LinearOrderedSemiring α] [LinearOrderedSemiring β] [FloorSemiring α] [FloorSemiring β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

@[target] theorem floor_congr (h : ∀ n : ℕ, (n : α) ≤ a ↔ (n : β) ≤ b) : ⌊a⌋₊ = ⌊b⌋₊ := by
  sorry


@[target] theorem ceil_congr (h : ∀ n : ℕ, a ≤ n ↔ b ≤ n) : ⌈a⌉₊ = ⌈b⌉₊ := by sorry


@[target] theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋₊ = ⌊a⌋₊ :=
  floor_congr fun n => by sorry


@[target] theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉₊ = ⌈a⌉₊ :=
  ceil_congr fun n => by sorry


end Nat

namespace Int

variable [LinearOrderedRing α] [LinearOrderedRing β] [FloorRing α] [FloorRing β]
variable [FunLike F α β] [RingHomClass F α β] {a : α} {b : β}

theorem floor_congr (h : ∀ n : ℤ, (n : α) ≤ a ↔ (n : β) ≤ b) : ⌊a⌋ = ⌊b⌋ :=
  (le_floor.2 <| (h _).1 <| floor_le _).antisymm <| le_floor.2 <| (h _).2 <| floor_le _

theorem ceil_congr (h : ∀ n : ℤ, a ≤ n ↔ b ≤ n) : ⌈a⌉ = ⌈b⌉ :=
  (ceil_le.2 <| (h _).2 <| le_ceil _).antisymm <| ceil_le.2 <| (h _).1 <| le_ceil _

theorem map_floor (f : F) (hf : StrictMono f) (a : α) : ⌊f a⌋ = ⌊a⌋ :=
  floor_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

theorem map_ceil (f : F) (hf : StrictMono f) (a : α) : ⌈f a⌉ = ⌈a⌉ :=
  ceil_congr fun n => by rw [← map_intCast f, hf.le_iff_le]

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

@[simp]
theorem Nat.ceil_int : (Nat.ceil : ℤ → ℕ) = Int.toNat :=
  rfl

variable {a : α}

theorem Int.natCast_floor_eq_floor (ha : 0 ≤ a) : (⌊a⌋₊ : ℤ) = ⌊a⌋ := by
  rw [← Int.floor_toNat, Int.toNat_of_nonneg (Int.floor_nonneg.2 ha)]

theorem Int.natCast_ceil_eq_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : ℤ) = ⌈a⌉ := by
  rw [← Int.ceil_toNat, Int.toNat_of_nonneg (Int.ceil_nonneg ha)]

@[target] theorem natCast_floor_eq_intCast_floor (ha : 0 ≤ a) : (⌊a⌋₊ : α) = ⌊a⌋ := by
  sorry


@[target] theorem natCast_ceil_eq_intCast_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : α) = ⌈a⌉ := by
  sorry


@[deprecated (since := "2024-08-20")] alias Int.ofNat_floor_eq_floor := natCast_floor_eq_floor
@[deprecated (since := "2024-08-20")] alias Int.ofNat_ceil_eq_ceil := natCast_ceil_eq_ceil

end FloorRingToSemiring

/-- There exists at most one `FloorRing` structure on a given linear ordered ring. -/
/-- There exists at most one `FloorRing` structure on a given linear ordered ring. -/
@[target] theorem subsingleton_floorRing {α} [LinearOrderedRing α] : Subsingleton (FloorRing α) := by
  sorry


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
/-- Extension for the `positivity` tactic: `Int.floor` is nonnegative if its input is. -/
@[positivity ⌊ _ ⌋]
def evalIntFloor : PositivityExt where eval {u α} _zα _pα e := by sorry


private theorem nat_ceil_pos [LinearOrderedSemiring α] [FloorSemiring α] {a : α} :
    0 < a → 0 < ⌈a⌉₊ :=
  Nat.ceil_pos.2

/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
/-- Extension for the `positivity` tactic: `Nat.ceil` is positive if its input is. -/
@[positivity ⌈ _ ⌉₊]
def evalNatCeil : PositivityExt where eval {u α} _zα _pα e := by sorry


private theorem int_ceil_pos [LinearOrderedRing α] [FloorRing α] {a : α} : 0 < a → 0 < ⌈a⌉ :=
  Int.ceil_pos.2

/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
/-- Extension for the `positivity` tactic: `Int.ceil` is positive/nonnegative if its input is. -/
@[positivity ⌈ _ ⌉]
def evalIntCeil : PositivityExt where eval {u α} _zα _pα e := by sorry


end Mathlib.Meta.Positivity
