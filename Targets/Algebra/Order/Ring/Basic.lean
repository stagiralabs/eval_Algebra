import VerifiedAgora.tagger
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis
-/
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Bound.Attribute

/-!
# Basic lemmas about ordered rings
-/

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Int

variable {α M R : Type*}

@[target]
theorem IsSquare.nonneg [Semiring R] [LinearOrder R] [IsRightCancelAdd R]
    [ZeroLEOneClass R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftStrictMono R]
    {x : R} (h : IsSquare x) : 0 ≤ x := by sorry

namespace MonoidHom

variable [Ring R] [Monoid M] [LinearOrder M] [MulLeftMono M] (f : R →* M)

theorem map_neg_one : f (-1) = 1 :=
  (pow_eq_one_iff (Nat.succ_ne_zero 1)).1 <| by rw [← map_pow, neg_one_sq, map_one]

@[simp]
theorem map_neg (x : R) : f (-x) = f x := by rw [← neg_one_mul, map_mul, map_neg_one, one_mul]

@[target]
theorem map_sub_swap (x y : R) : f (x - y) = f (y - x) := by sorry

end MonoidHom

section OrderedSemiring

variable [OrderedSemiring R] {a b x y : R} {n : ℕ}

theorem pow_add_pow_le (hx : 0 ≤ x) (hy : 0 ≤ y) (hn : n ≠ 0) : x ^ n + y ^ n ≤ (x + y) ^ n := by
  rcases Nat.exists_eq_add_one_of_ne_zero hn with ⟨k, rfl⟩
  induction k with
  | zero => simp only [zero_add, pow_one, le_refl]
  | succ k ih =>
    let n := k.succ
    have h1 := add_nonneg (mul_nonneg hx (pow_nonneg hy n)) (mul_nonneg hy (pow_nonneg hx n))
    have h2 := add_nonneg hx hy
    calc
      x ^ (n + 1) + y ^ (n + 1) ≤ x * x ^ n + y * y ^ n + (x * y ^ n + y * x ^ n) := by
        rw [pow_succ' _ n, pow_succ' _ n]
        exact le_add_of_nonneg_right h1
      _ = (x + y) * (x ^ n + y ^ n) := by
        rw [add_mul, mul_add, mul_add, add_comm (y * x ^ n), ← add_assoc, ← add_assoc,
          add_assoc (x * x ^ n) (x * y ^ n), add_comm (x * y ^ n) (y * y ^ n), ← add_assoc]
      _ ≤ (x + y) ^ (n + 1) := by
        rw [pow_succ' _ n]
        exact mul_le_mul_of_nonneg_left (ih (Nat.succ_ne_zero k)) h2

attribute [bound] pow_le_one₀ one_le_pow₀

@[deprecated (since := "2024-09-28")] alias mul_le_one := mul_le_one₀
@[deprecated (since := "2024-09-28")] alias pow_le_one := pow_le_one₀
@[deprecated (since := "2024-09-28")] alias pow_lt_one := pow_lt_one₀
@[deprecated (since := "2024-09-28")] alias one_le_pow_of_one_le := one_le_pow₀
@[deprecated (since := "2024-09-28")] alias one_lt_pow := one_lt_pow₀
@[deprecated (since := "2024-10-04")] alias pow_right_mono := pow_right_mono₀
@[deprecated (since := "2024-10-04")] alias pow_le_pow_right := pow_le_pow_right₀

@[deprecated pow_le_pow_left₀ (since := "2024-11-13")]
theorem pow_le_pow_left {a b : R} (ha : 0 ≤ a) (hab : a ≤ b) : ∀ n, a ^ n ≤ b ^ n :=
  pow_le_pow_left₀ ha hab

lemma pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n := by
  rw [two_mul]
  exact add_le_add (pow_le_pow_left₀ ha (le_add_of_nonneg_right hb) _)
    (pow_le_pow_left₀ hb (le_add_of_nonneg_left ha) _)

end OrderedSemiring

-- See note [reducible non instances]
/-- Turn an ordered domain into a strict ordered ring. -/
abbrev OrderedRing.toStrictOrderedRing (α : Type*)
    [OrderedRing α] [NoZeroDivisors α] [Nontrivial α] : StrictOrderedRing α where
  __ := ‹OrderedRing α›
  __ := ‹NoZeroDivisors α›
  mul_pos _ _ ap bp := (mul_nonneg ap.le bp.le).lt_of_ne' (mul_ne_zero ap.ne' bp.ne')

section StrictOrderedSemiring

variable [StrictOrderedSemiring R] {a x y : R} {n m : ℕ}

@[target, deprecated pow_lt_pow_left₀ (since := sorry

@[deprecated pow_left_strictMonoOn₀ (since := "2024-11-13")]
lemma pow_left_strictMonoOn (hn : n ≠ 0) : StrictMonoOn (· ^ n : R → R) {a | 0 ≤ a} :=
  pow_left_strictMonoOn₀ hn

@[deprecated pow_right_strictMono₀ (since := "2024-11-13")]
lemma pow_right_strictMono (h : 1 < a) : StrictMono (a ^ ·) :=
  pow_right_strictMono₀ h

@[target, deprecated pow_lt_pow_right₀ (since := sorry

@[target, deprecated pow_lt_pow_iff_right₀ (since := sorry

@[deprecated pow_le_pow_iff_right₀ (since := "2024-11-13")]
lemma pow_le_pow_iff_right (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m := pow_le_pow_iff_right₀ h

@[target, deprecated lt_self_pow₀ (since := sorry

@[target, deprecated pow_right_strictAnti₀ (since := sorry

@[target, deprecated pow_lt_pow_iff_right_of_lt_one₀ (since := sorry

@[target, deprecated pow_lt_pow_right_of_lt_one₀ (since := sorry

@[target, deprecated pow_lt_self_of_lt_one₀ (since := sorry

end StrictOrderedSemiring

section StrictOrderedRing
variable [StrictOrderedRing R] {a : R}

@[target]
lemma sq_pos_of_neg (ha : a < 0) : 0 < a ^ 2 := by sorry

end StrictOrderedRing

section LinearOrderedSemiring
variable [LinearOrderedSemiring R] {a b : R} {m n : ℕ}

@[target, deprecated pow_le_pow_iff_left₀ (since := sorry

@[deprecated pow_lt_pow_iff_left₀ (since := "2024-11-12")]
lemma pow_lt_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  pow_lt_pow_iff_left₀ ha hb hn

@[deprecated pow_left_inj₀ (since := "2024-11-12")]
lemma pow_left_inj (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b :=
  pow_left_inj₀ ha hb hn

@[deprecated pow_right_injective₀ (since := "2024-11-12")]
lemma pow_right_injective (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Injective (a ^ ·) :=
  pow_right_injective₀ ha₀ ha₁

@[target, deprecated pow_right_inj₀ (since := sorry

@[target, deprecated sq_le_one_iff₀ (since := sorry

@[target, deprecated sq_lt_one_iff₀ (since := sorry

@[deprecated one_le_sq_iff₀ (since := "2024-11-12")]
theorem one_le_sq_iff {a : R} (ha : 0 ≤ a) : 1 ≤ a ^ 2 ↔ 1 ≤ a := one_le_sq_iff₀ ha

@[deprecated one_lt_sq_iff₀ (since := "2024-11-12")]
theorem one_lt_sq_iff {a : R} (ha : 0 ≤ a) : 1 < a ^ 2 ↔ 1 < a := one_lt_sq_iff₀ ha

@[target, deprecated lt_of_pow_lt_pow_left₀ (since := sorry

@[deprecated le_of_pow_le_pow_left₀ (since := "2024-11-12")]
theorem le_of_pow_le_pow_left (hn : n ≠ 0) (hb : 0 ≤ b) (h : a ^ n ≤ b ^ n) : a ≤ b :=
  le_of_pow_le_pow_left₀ hn hb h

@[target, deprecated sq_eq_sq₀ (since := sorry

@[target, deprecated lt_of_mul_self_lt_mul_self₀ (since := sorry
### Lemmas for canonically linear ordered semirings or linear ordered rings

The slightly unusual typeclass assumptions `[LinearOrderedSemiring R] [ExistsAddOfLE R]` cover two
more familiar settings:
* `[LinearOrderedRing R]`, eg `ℤ`, `ℚ` or `ℝ`
* `[CanonicallyLinearOrderedSemiring R]` (although we don't actually have this typeclass), eg `ℕ`,
  `ℚ≥0` or `ℝ≥0`
-/

variable [ExistsAddOfLE R]

@[target]
lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by sorry

-- TODO: Use `gcongr`, `positivity`, `ring` once those tactics are made available here
@[target]
lemma add_pow_le (ha : 0 ≤ a) (hb : 0 ≤ b) : ∀ n, (a + b) ^ n ≤ 2 ^ (n - 1) * (a ^ n + b ^ n)
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [pow_succ]
    calc
      _ ≤ 2 ^ n * (a ^ (n + 1) + b ^ (n + 1)) * (a + b) :=
          sorry

lemma Even.pow_nonneg (hn : Even n) (a : R) : 0 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := hn; rw [pow_add]; exact mul_self_nonneg _

lemma Even.pow_pos (hn : Even n) (ha : a ≠ 0) : 0 < a ^ n :=
  (hn.pow_nonneg _).lt_of_ne' (pow_ne_zero _ ha)

@[target]
lemma Even.pow_pos_iff (hn : Even n) (h₀ : n ≠ 0) : 0 < a ^ n ↔ a ≠ 0 := by sorry

lemma Odd.pow_neg_iff (hn : Odd n) : a ^ n < 0 ↔ a < 0 := by
  refine ⟨lt_imp_lt_of_le_imp_le (pow_nonneg · _), fun ha ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ]
  exact mul_neg_of_pos_of_neg ((even_two_mul _).pow_pos ha.ne) ha

lemma Odd.pow_nonneg_iff (hn : Odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 hn.pow_neg_iff

lemma Odd.pow_nonpos_iff (hn : Odd n) : a ^ n ≤ 0 ↔ a ≤ 0 := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, hn.pow_neg_iff, pow_eq_zero_iff]
  rintro rfl; simp [Odd, eq_comm (a := 0)] at hn

lemma Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff

@[target]
lemma Odd.strictMono_pow (hn : Odd n) : StrictMono fun a : R => a ^ n := by sorry

lemma sq_pos_iff {a : R} : 0 < a ^ 2 ↔ a ≠ 0 := even_two.pow_pos_iff two_ne_zero

alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero

@[target]
lemma pow_four_le_pow_two_of_pow_two_le (h : a ^ 2 ≤ b) : a ^ 4 ≤ b ^ 2 :=
  sorry

end LinearOrderedSemiring
