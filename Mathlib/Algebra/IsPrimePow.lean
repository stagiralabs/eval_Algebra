import VerifiedAgora.tagger
/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Order.Nat
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/
assert_not_exists Nat.divisors

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def IsPrimePow : Prop :=
  ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n

@[target] theorem isPrimePow_def : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n := by sorry


/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
@[target] theorem isPrimePow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ p ^ (k + 1) = n :=
  (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨p, k - 1, hp, by sorry


@[target] theorem not_isPrimePow_zero [NoZeroDivisors R] : ¬IsPrimePow (0 : R) := by
  sorry


theorem IsPrimePow.not_unit {n : R} (h : IsPrimePow n) : ¬IsUnit n :=
  let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_unit

theorem IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_unit h

@[target] theorem not_isPrimePow_one : ¬IsPrimePow (1 : R) := by sorry


theorem Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by simp⟩

theorem IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩

theorem IsPrimePow.ne_zero [NoZeroDivisors R] {n : R} (h : IsPrimePow n) : n ≠ 0 := fun t =>
  not_isPrimePow_zero (t ▸ h)

theorem IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t =>
  not_isPrimePow_one (t ▸ h)

section Nat

@[target] theorem isPrimePow_nat_iff (n : ℕ) : IsPrimePow n ↔ ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  sorry


theorem Nat.Prime.isPrimePow {p : ℕ} (hp : p.Prime) : IsPrimePow p :=
  _root_.Prime.isPrimePow (prime_iff.mp hp)

@[target] theorem isPrimePow_nat_iff_bounded (n : ℕ) :
    IsPrimePow n ↔ ∃ p : ℕ, p ≤ n ∧ ∃ k : ℕ, k ≤ n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n := by
  sorry


instance {n : ℕ} : Decidable (IsPrimePow n) :=
  decidable_of_iff' _ (isPrimePow_nat_iff_bounded n)

theorem IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m := by
  rw [isPrimePow_nat_iff] at hn ⊢
  rcases hn with ⟨p, k, hp, _hk, rfl⟩
  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hm
  refine ⟨p, i, hp, ?_, rfl⟩
  apply Nat.pos_of_ne_zero
  rintro rfl
  simp only [pow_zero, ne_eq, not_true_eq_false] at hm₁

theorem IsPrimePow.two_le : ∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
  | 0, h => (not_isPrimePow_zero h).elim
  | 1, h => (not_isPrimePow_one h).elim
  | _n + 2, _ => le_add_self

theorem IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le

theorem IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n :=
  h.two_le

end Nat
