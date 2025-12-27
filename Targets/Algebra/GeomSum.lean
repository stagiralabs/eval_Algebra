import VerifiedAgora.tagger
/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Opposite
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Regular

/-!
# Partial sums of geometric series

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^iy^{n - 1 - i}=\frac{x^n-y^{n-m}x^m}{x-y}$
  in a field.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

universe u

variable {α : Type u}

open Finset MulOpposite

section Semiring

variable [Semiring α]

theorem geom_sum_succ {x : α} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = (x * ∑ i ∈ range n, x ^ i) + 1 := by
  simp only [mul_sum, ← pow_succ', sum_range_succ', pow_zero]

@[target]
theorem geom_sum_succ' {x : α} {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i = x ^ n + ∑ i ∈ range n, x ^ i :=
  sorry

@[target]
theorem geom_sum_zero (x : α) : ∑ i ∈ range 0, x ^ i = 0 :=
  sorry

theorem geom_sum_one (x : α) : ∑ i ∈ range 1, x ^ i = 1 := by simp [geom_sum_succ']

@[target, simp]
theorem geom_sum_two {x : α} : ∑ i ∈ range 2, x ^ i = x + 1 := by sorry

@[target, simp]
theorem zero_geom_sum : ∀ {n}, ∑ i ∈ range n, (0 : α) ^ i = if n = 0 then 0 else 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [geom_sum_succ']
    simp [zero_geom_sum]

theorem one_geom_sum (n : ℕ) : ∑ i ∈ range n, (1 : α) ^ i = n := by sorry

theorem op_geom_sum (x : α) (n : ℕ) : op (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, op x ^ i := by
  simp

@[target, simp]
theorem op_geom_sum₂ (x y : α) (n : ℕ) : ∑ i ∈ range n, op y ^ (n - 1 - i) * op x ^ i =
    ∑ i ∈ range n, op y ^ i * op x ^ (n - 1 - i) := by sorry

@[target]
theorem geom_sum₂_with_one (x : α) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * 1 ^ (n - 1 - i) = ∑ i ∈ range n, x ^ i :=
  sorry

end Semiring

@[target, simp]
theorem neg_one_geom_sum [Ring α] {n : ℕ} :
    ∑ i ∈ range n, (-1 : α) ^ i = if Even n then 0 else 1 := by sorry

@[target]
theorem geom_sum₂_self {α : Type*} [CommRing α] (x : α) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * x ^ (n - 1 - i) = n * x ^ (n - 1) :=
  sorry
theorem geom_sum₂_mul_add [CommSemiring α] (x y : α) (n : ℕ) :
    (∑ i ∈ range n, (x + y) ^ i * y ^ (n - 1 - i)) * x + y ^ n = (x + y) ^ n :=
  (Commute.all x y).geom_sum₂_mul_add n

theorem geom_sum_mul_add [Semiring α] (x : α) (n : ℕ) :
    (∑ i ∈ range n, (x + 1) ^ i) * x + 1 = (x + 1) ^ n := by
  have := (Commute.one_right x).geom_sum₂_mul_add n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

protected theorem Commute.geom_sum₂_mul [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  have := (h.sub_left (Commute.refl y)).geom_sum₂_mul_add n
  rw [sub_add_cancel] at this
  rw [← this, add_sub_cancel_right]

theorem Commute.mul_neg_geom_sum₂ [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((y - x) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n := by
  apply op_injective
  simp only [op_mul, op_sub, op_geom_sum₂, op_pow]
  simp [(Commute.op h.symm).geom_sum₂_mul n]

theorem Commute.mul_geom_sum₂ [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    ((x - y) * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = x ^ n - y ^ n := by
  rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul, neg_sub]

@[target]
theorem geom_sum₂_mul [CommRing α] (x y : α) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n :=
  sorry

theorem geom_sum₂_mul_of_ge [CommSemiring α] [PartialOrder α] [AddLeftReflectLE α] [AddLeftMono α]
    [ExistsAddOfLE α] [Sub α] [OrderedSub α] {x y : α} (hxy : y ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n - y ^ n := by
  apply eq_tsub_of_add_eq
  simpa only [tsub_add_cancel_of_le hxy] using geom_sum₂_mul_add (x - y) y n

@[target]
theorem geom_sum₂_mul_of_le [CommSemiring α] [PartialOrder α] [AddLeftReflectLE α] [AddLeftMono α]
    [ExistsAddOfLE α] [Sub α] [OrderedSub α] {x y : α} (hxy : x ≤ y) (n : ℕ) :
    (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) * (y - x) = y ^ n - x ^ n := by sorry

@[target]
theorem Commute.sub_dvd_pow_sub_pow [Ring α] {x y : α} (h : Commute x y) (n : ℕ) :
    x - y ∣ x ^ n - y ^ n :=
  sorry

@[target]
theorem sub_dvd_pow_sub_pow [CommRing α] (x y : α) (n : ℕ) : x - y ∣ x ^ n - y ^ n :=
  sorry

theorem nat_sub_dvd_pow_sub_pow (x y n : ℕ) : x - y ∣ x ^ n - y ^ n := by
  rcases le_or_lt y x with h | h
  · have : y ^ n ≤ x ^ n := Nat.pow_le_pow_left h _
    exact mod_cast sub_dvd_pow_sub_pow (x : ℤ) (↑y) n
  · have : x ^ n ≤ y ^ n := Nat.pow_le_pow_left h.le _
    exact (Nat.sub_eq_zero_of_le this).symm ▸ dvd_zero (x - y)

@[target]
theorem one_sub_dvd_one_sub_pow [Ring α] (x : α) (n : ℕ) :
    1 - x ∣ 1 - x ^ n := by sorry

@[target]
theorem sub_one_dvd_pow_sub_one [Ring α] (x : α) (n : ℕ) :
    x - 1 ∣ x ^ n - 1 := by sorry

@[target]
lemma pow_one_sub_dvd_pow_mul_sub_one [Ring α] (x : α) (m n : ℕ) :
    ((x ^ m) - 1 : α) ∣ (x ^ (m * n) - 1) := by sorry

@[target]
lemma nat_pow_one_sub_dvd_pow_mul_sub_one (x m n : ℕ) : x ^ m - 1 ∣ x ^ (m * n) - 1 := by sorry

theorem Odd.add_dvd_pow_add_pow [CommRing α] (x y : α) {n : ℕ} (h : Odd n) :
    x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

theorem Odd.nat_add_dvd_pow_add_pow (x y : ℕ) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n :=
  mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h

theorem geom_sum_mul [Ring α] (x : α) (n : ℕ) : (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  have := (Commute.one_right x).geom_sum₂_mul n
  rw [one_pow, geom_sum₂_with_one] at this
  exact this

theorem geom_sum_mul_of_one_le [CommSemiring α] [PartialOrder α] [AddLeftReflectLE α]
    [AddLeftMono α] [ExistsAddOfLE α] [Sub α] [OrderedSub α] {x : α} (hx : 1 ≤ x) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  simpa using geom_sum₂_mul_of_ge hx n

@[target]
theorem geom_sum_mul_of_le_one [CommSemiring α] [PartialOrder α] [AddLeftReflectLE α]
    [AddLeftMono α] [ExistsAddOfLE α] [Sub α] [OrderedSub α] {x : α} (hx : x ≤ 1) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by sorry

@[target]
theorem mul_geom_sum [Ring α] (x : α) (n : ℕ) : ((x - 1) * ∑ i ∈ range n, x ^ i) = x ^ n - 1 :=
  sorry

@[target]
theorem geom_sum_mul_neg [Ring α] (x : α) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) * (1 - x) = 1 - x ^ n := by sorry

theorem mul_neg_geom_sum [Ring α] (x : α) (n : ℕ) : ((1 - x) * ∑ i ∈ range n, x ^ i) = 1 - x ^ n :=
  op_injective <| by simpa using geom_sum_mul_neg (op x) n

protected theorem Commute.geom_sum₂_comm {α : Type u} [Semiring α] {x y : α} (n : ℕ)
    (h : Commute x y) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) := by
  cases n; · simp
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [← Finset.sum_flip]
  refine Finset.sum_congr rfl fun i hi => ?_
  simpa [Nat.sub_sub_self (Nat.succ_le_succ_iff.mp (Finset.mem_range.mp hi))] using h.pow_pow _ _

@[target]
theorem geom_sum₂_comm {α : Type u} [CommSemiring α] (x y : α) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = ∑ i ∈ range n, y ^ i * x ^ (n - 1 - i) :=
  sorry

theorem geom₂_sum [Field α] {x y : α} (h : x ≠ y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  (Commute.all x y).geom_sum₂ h n

theorem geom₂_sum_of_gt {α : Type*} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α]
    {x y : α} (h : y < x) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ n) / (x - y) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_ge h.le n)

theorem geom₂_sum_of_lt {α : Type*} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α]
    {x y : α} (h : x < y) (n : ℕ) :
    ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) = (y ^ n - x ^ n) / (y - x) :=
  eq_div_of_mul_eq (tsub_pos_of_lt h).ne' (geom_sum₂_mul_of_le h.le n)

theorem geom_sum_eq [DivisionRing α] {x : α} (h : x ≠ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ i = (x ^ n - 1) / (x - 1) := by
  have : x - 1 ≠ 0 := by simp_all [sub_eq_iff_eq_add]
  rw [← geom_sum_mul, mul_div_cancel_right₀ _ this]

@[target]
lemma geom_sum_of_one_lt {x : α} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α]
    (h : 1 < x) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (x ^ n - 1) / (x - 1) :=
  sorry

@[target]
lemma geom_sum_of_lt_one {x : α} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α]
    (h : x < 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, x ^ i = (1 - x ^ n) / (1 - x) :=
  sorry

theorem geom_sum_lt {x : α} [LinearOrderedSemifield α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α]
    (h0 : x ≠ 0) (h1 : x < 1) (n : ℕ) : ∑ i ∈ range n, x ^ i < (1 - x)⁻¹ := by
  rw [← pos_iff_ne_zero] at h0
  rw [geom_sum_of_lt_one h1, div_lt_iff₀, inv_mul_cancel₀, tsub_lt_self_iff]
  · exact ⟨h0.trans h1, pow_pos h0 n⟩
  · rwa [ne_eq, tsub_eq_zero_iff_le, not_le]
  · rwa [tsub_pos_iff_lt]

protected theorem Commute.mul_geom_sum₂_Ico [Ring α] {x y : α} (h : Commute x y) {m n : ℕ}
    (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) := by
  rw [sum_Ico_eq_sub _ hmn]
  have :
    ∑ k ∈ range m, x ^ k * y ^ (n - 1 - k) =
      ∑ k ∈ range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)) := by
    refine sum_congr rfl fun j j_in => ?_
    rw [← pow_add]
    congr
    rw [mem_range] at j_in
    omega
  rw [this]
  simp_rw [pow_mul_comm y (n - m) _]
  simp_rw [← mul_assoc]
  rw [← sum_mul, mul_sub, h.mul_geom_sum₂, ← mul_assoc, h.mul_geom_sum₂, sub_mul, ← pow_add,
    add_tsub_cancel_of_le hmn, sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)]

protected theorem Commute.geom_sum₂_succ_eq {α : Type u} [Ring α] {x y : α} (h : Commute x y)
    {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) := by
  simp_rw [mul_sum, sum_range_succ_comm, tsub_self, pow_zero, mul_one, add_right_inj, ← mul_assoc,
    (h.symm.pow_right _).eq, mul_assoc, ← pow_succ']
  refine sum_congr rfl fun i hi => ?_
  suffices n - 1 - i + 1 = n - i by rw [this]
  rw [Finset.mem_range] at hi
  omega

@[target]
theorem geom_sum₂_succ_eq {α : Type u} [CommRing α] (x y : α) {n : ℕ} :
    ∑ i ∈ range (n + 1), x ^ i * y ^ (n - i) =
      x ^ n + y * ∑ i ∈ range n, x ^ i * y ^ (n - 1 - i) :=
  sorry

@[target]
theorem mul_geom_sum₂_Ico [CommRing α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
    ((x - y) * ∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
  sorry

@[target]
theorem geom_sum_Ico_mul [Ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (x - 1) = x ^ n - x ^ m := by sorry

@[target]
theorem geom_sum_Ico_mul_neg [Ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i) * (1 - x) = x ^ m - x ^ n := by sorry

theorem geom_sum₂_Ico [Field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
    (∑ i ∈ Finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = (x ^ n - y ^ (n - m) * x ^ m) / (x - y) :=
  (Commute.all x y).geom_sum₂_Ico hxy hmn

theorem geom_sum_Ico [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) := by
  simp only [sum_Ico_eq_sub _ hmn, geom_sum_eq hx, div_sub_div_same, sub_sub_sub_cancel_right]

@[target]
theorem geom_sum_Ico' [DivisionRing α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) := by sorry

theorem geom_sum_Ico_le_of_lt_one [LinearOrderedField α] {x : α} (hx : 0 ≤ x) (h'x : x < 1)
    {m n : ℕ} : ∑ i ∈ Ico m n, x ^ i ≤ x ^ m / (1 - x) := by
  rcases le_or_lt m n with (hmn | hmn)
  · rw [geom_sum_Ico' h'x.ne hmn]
    apply div_le_div₀ (pow_nonneg hx _) _ (sub_pos.2 h'x) le_rfl
    simpa using pow_nonneg hx _
  · rw [Ico_eq_empty, sum_empty]
    · apply div_nonneg (pow_nonneg hx _)
      simpa using h'x.le
    · simpa using hmn.le

@[target]
theorem geom_sum_inv [DivisionRing α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
    ∑ i ∈ range n, x⁻¹ ^ i = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) := by sorry

variable {β : Type*}

-- TODO: for consistency, the next two lemmas should be moved to the root namespace
theorem RingHom.map_geom_sum [Semiring α] [Semiring β] (x : α) (n : ℕ) (f : α →+* β) :
    f (∑ i ∈ range n, x ^ i) = ∑ i ∈ range n, f x ^ i := by simp [map_sum f]

@[target]
theorem RingHom.map_geom_sum₂ [Semiring α] [Semiring β] (x y : α) (n : ℕ) (f : α →+* β) :
    f (∑ i ∈ range n, x ^ i * y ^ (n - 1 - i)) = ∑ i ∈ range n, f x ^ i * f y ^ (n - 1 - i) := by sorry


theorem Nat.pred_mul_geom_sum_le (a b n : ℕ) :
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) ≤ a * b - a / b ^ n :=
  calc
    ((b - 1) * ∑ i ∈ range n.succ, a / b ^ i) =
    (∑ i ∈ range n, a / b ^ (i + 1) * b) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      rw [tsub_mul, mul_comm, sum_mul, one_mul, sum_range_succ', sum_range_succ, pow_zero,
        Nat.div_one]
    _ ≤ (∑ i ∈ range n, a / b ^ i) + a * b - ((∑ i ∈ range n, a / b ^ i) + a / b ^ n) := by
      gcongr with i hi
      rw [pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
    _ = a * b - a / b ^ n := add_tsub_add_eq_tsub_left _ _ _

theorem Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ range n, a / b ^ i ≤ a * b / (b - 1) := by
  refine (Nat.le_div_iff_mul_le <| tsub_pos_of_lt hb).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, zero_mul]
    exact Nat.zero_le _
  rw [mul_comm]
  exact (Nat.pred_mul_geom_sum_le a b n).trans tsub_le_self

theorem Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ Ico 1 n, a / b ^ i ≤ a / (b - 1) := by
  rcases n with - | n
  · rw [Ico_eq_empty_of_le (zero_le_one' ℕ), sum_empty]
    exact Nat.zero_le _
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i ∈ Ico 1 n.succ, a / b ^ i) = a / b ^ 0 + ∑ i ∈ Ico 1 n.succ, a / b ^ i := by
      rw [pow_zero, Nat.div_one]
    _ = ∑ i ∈ range n.succ, a / b ^ i := by
      rw [range_eq_Ico, ← Nat.Ico_insert_succ_left (Nat.succ_pos _), sum_insert]
      exact fun h => zero_lt_one.not_le (mem_Ico.1 h).1
    _ ≤ a * b / (b - 1) := Nat.geom_sum_le hb a _
    _ = (a * 1 + a * (b - 1)) / (b - 1) := by
      rw [← mul_add, add_tsub_cancel_of_le (one_le_two.trans hb)]
    _ = a + a / (b - 1) := by rw [mul_one, Nat.add_mul_div_right _ _ (tsub_pos_of_lt hb), add_comm]

section Order

variable {n : ℕ} {x : α}

theorem geom_sum_pos [StrictOrderedSemiring α] (hx : 0 ≤ x) (hn : n ≠ 0) :
    0 < ∑ i ∈ range n, x ^ i :=
  sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

@[target]
theorem geom_sum_pos_and_lt_one [StrictOrderedRing α] (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
    (0 < ∑ i ∈ range n, x ^ i) ∧ ∑ i ∈ range n, x ^ i < 1 := by sorry

theorem geom_sum_alternating_of_le_neg_one [StrictOrderedRing α] (hx : x + 1 ≤ 0) (n : ℕ) :
    if Even n then (∑ i ∈ range n, x ^ i) ≤ 0 else 1 ≤ ∑ i ∈ range n, x ^ i := by
  have hx0 : x ≤ 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih with h
    · rw [if_neg (not_not_intro h), le_add_iff_nonneg_left]
      exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
    · rw [if_pos h]
      refine (add_le_add_right ?_ _).trans hx
      simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0

@[target]
theorem geom_sum_alternating_of_lt_neg_one [StrictOrderedRing α] (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then (∑ i ∈ range n, x ^ i) < 0 else 1 < ∑ i ∈ range n, x ^ i := by sorry

@[target]
theorem geom_sum_pos' [LinearOrderedRing α] (hx : 0 < x + 1) (hn : n ≠ 0) :
    0 < ∑ i ∈ range n, x ^ i := by sorry

@[target]
theorem Odd.geom_sum_pos [LinearOrderedRing α] (h : Odd n) : 0 < ∑ i ∈ range n, x ^ i := by sorry

theorem geom_sum_pos_iff [LinearOrderedRing α] (hn : n ≠ 0) :
    (0 < ∑ i ∈ range n, x ^ i) ↔ Odd n ∨ 0 < x + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_le ?_
    simpa [if_pos hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn

@[target]
theorem geom_sum_ne_zero [LinearOrderedRing α] (hx : x ≠ -1) (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i ≠ 0 := by sorry

theorem geom_sum_eq_zero_iff_neg_one [LinearOrderedRing α] (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, if_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

theorem geom_sum_neg_iff [LinearOrderedRing α] (hn : n ≠ 0) :
    ∑ i ∈ range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), ← Nat.not_even_iff_odd, ←
    add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm, ← imp_iff_not_or, or_comm,
    and_comm, Decidable.and_or_imp, or_comm]

end Order

variable {m n : ℕ} {s : Finset ℕ}

/-- Value of a geometric sum over the naturals. Note: see `geom_sum_mul_add` for a formulation
that avoids division and subtraction. -/
lemma Nat.geomSum_eq (hm : 2 ≤ m) (n : ℕ) :
    ∑ k ∈ range n, m ^ k = (m ^ n - 1) / (m - 1) := by
  refine (Nat.div_eq_of_eq_mul_left (tsub_pos_iff_lt.2 hm) <| tsub_eq_of_eq_add ?_).symm
  simpa only [tsub_add_cancel_of_le (one_le_two.trans hm), eq_comm] using geom_sum_mul_add (m - 1) n

/-- If all the elements of a finset of naturals are less than `n`, then the sum of their powers of
`m ≥ 2` is less than `m ^ n`. -/
@[target]
lemma Nat.geomSum_lt (hm : 2 ≤ m) (hs : ∀ k ∈ s, k < n) : ∑ k ∈ s, m ^ k < m ^ n :=
  sorry