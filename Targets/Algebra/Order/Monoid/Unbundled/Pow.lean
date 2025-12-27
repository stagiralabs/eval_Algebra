import VerifiedAgora.tagger
/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Yury Kudryashov
-/
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Monotonicity.Attr

/-!
# Lemmas about the interaction of power operations with order in terms of `CovariantClass`
-/

open Function

variable {β G M : Type*}

section Monoid

variable [Monoid M]

section Preorder

variable [Preorder M]

namespace Left

variable [MulLeftMono M] {a : M}

@[target, to_additive Left.nsmul_nonneg]
theorem one_le_pow_of_le (ha : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    exact one_le_mul (one_le_pow_of_le ha k) ha

@[deprecated (since := sorry

@[target, to_additive nsmul_nonpos]
theorem pow_le_one_of_le (ha : a ≤ 1) (n : ℕ) : a ^ n ≤ 1 := sorry

@[deprecated (since := "2024-09-21")] alias pow_nonpos := nsmul_nonpos

@[to_additive nsmul_neg]
theorem pow_lt_one_of_lt {a : M} {n : ℕ} (h : a < 1) (hn : n ≠ 0) : a ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [pow_succ']
  exact mul_lt_one_of_lt_of_le h (pow_le_one_of_le h.le _)

@[deprecated (since := "2024-09-21")] alias pow_neg := nsmul_neg

end Left

@[to_additive nsmul_nonneg] alias one_le_pow_of_one_le' := Left.one_le_pow_of_le
@[to_additive nsmul_nonpos] alias pow_le_one' := Left.pow_le_one_of_le
@[to_additive nsmul_neg] alias pow_lt_one' := Left.pow_lt_one_of_lt

section Left

variable [MulLeftMono M] {a : M} {n : ℕ}

@[to_additive nsmul_left_monotone]
theorem pow_right_monotone (ha : 1 ≤ a) : Monotone fun n : ℕ ↦ a ^ n :=
  monotone_nat_of_le_succ fun n ↦ by rw [pow_succ]; exact le_mul_of_one_le_right' ha

@[to_additive (attr := gcongr) nsmul_le_nsmul_left]
theorem pow_le_pow_right' {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
  pow_right_monotone ha h

@[to_additive nsmul_le_nsmul_left_of_nonpos]
theorem pow_le_pow_right_of_le_one' {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
  pow_le_pow_right' (M := Mᵒᵈ) ha h

@[target, to_additive nsmul_pos]
theorem one_lt_pow' (ha : 1 < a) {k : ℕ} (hk : k ≠ 0) : 1 < a ^ k :=
  sorry

@[target, to_additive]
lemma le_self_pow (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by sorry

end Left

section LeftLt

variable [MulLeftStrictMono M] {a : M} {n m : ℕ}

@[to_additive nsmul_left_strictMono]
theorem pow_right_strictMono' (ha : 1 < a) : StrictMono ((a ^ ·) : ℕ → M) :=
  strictMono_nat_of_lt_succ fun n ↦ by rw [pow_succ]; exact lt_mul_of_one_lt_right' (a ^ n) ha

@[to_additive (attr := gcongr) nsmul_lt_nsmul_left]
theorem pow_lt_pow_right' (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
  pow_right_strictMono' ha h

end LeftLt

section Right

variable [MulRightMono M] {x : M}

@[to_additive Right.nsmul_nonneg]
theorem Right.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x ^ n
  | 0 => (pow_zero _).ge
  | n + 1 => by
    rw [pow_succ]
    exact Right.one_le_mul (Right.one_le_pow_of_le hx) hx

@[deprecated (since := "2024-09-21")] alias Right.pow_nonneg := Right.nsmul_nonneg

@[to_additive Right.nsmul_nonpos]
theorem Right.pow_le_one_of_le (hx : x ≤ 1) {n : ℕ} : x ^ n ≤ 1 :=
  Right.one_le_pow_of_le (M := Mᵒᵈ) hx

@[deprecated (since := "2024-09-21")] alias Right.pow_nonpos := Right.nsmul_nonpos

@[to_additive Right.nsmul_neg]
theorem Right.pow_lt_one_of_lt {n : ℕ} {x : M} (hn : 0 < n) (h : x < 1) : x ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
  rw [pow_succ]
  exact mul_lt_one_of_le_of_lt (pow_le_one_of_le h.le) h

@[deprecated (since := "2024-09-21")] alias Right.pow_neg := Right.nsmul_neg

/-- This lemma is useful in non-cancellative monoids, like sets under pointwise operations. -/
@[to_additive
"This lemma is useful in non-cancellative monoids, like sets under pointwise operations."]
@[target]
lemma pow_le_pow_mul_of_sq_le_mul [MulLeftMono M] {a b : M} (hab : a ^ 2 ≤ b * a) :
    ∀ {n}, n ≠ 0 → a ^ n ≤ b ^ (n - 1) * a
  | 1, _ => by simp
  | n + 2, _ => by
    calc
      a ^ (n + 2) = a ^ (n + 1) * a := by sorry

end Right

section CovariantLTSwap

variable [Preorder β] [MulLeftStrictMono M] [MulRightStrictMono M] {f : β → M} {n : ℕ}

@[target, to_additive StrictMono.const_nsmul]
theorem StrictMono.pow_const (hf : StrictMono f) : ∀ {n : ℕ}, n ≠ 0 → StrictMono (f · ^ n)
  | 0, hn => (hn rfl).elim
  | 1, _ => by simpa
  | Nat.succ <| Nat.succ n, _ => by
    simpa only [pow_succ] using (hf.pow_const n.succ_ne_zero).mul' hf

/-- See also `pow_left_strictMonoOn₀`. -/
@[to_additive nsmul_right_strictMono]
theorem pow_left_strictMono (hn : n ≠ 0) : StrictMono (· ^ n : M → M) := sorry

@[target, to_additive (attr := sorry

end CovariantLTSwap

section CovariantLESwap

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

end CovariantLESwap

end Preorder

section SemilatticeSup
variable [SemilatticeSup M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

@[target]
lemma le_pow_sup : a ^ n ⊔ b ^ n ≤ (a ⊔ b) ^ n :=
  sorry

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

@[target]
lemma pow_inf_le : (a ⊓ b) ^ n ≤ a ^ n ⊓ b ^ n :=
  sorry

end SemilatticeInf

section LinearOrder

variable [LinearOrder M]

section CovariantLE

variable [MulLeftMono M]

-- This generalises to lattices. See `pow_two_semiclosed`
@[to_additive nsmul_nonneg_iff]
theorem one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x :=
  ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

@[target, to_additive]
theorem pow_le_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n ≤ 1 ↔ x ≤ 1 :=
  sorry

@[target, to_additive nsmul_pos_iff]
theorem one_lt_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 < x ^ n ↔ 1 < x :=
  sorry

@[to_additive]
theorem pow_lt_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n < 1 ↔ x < 1 :=
  lt_iff_lt_of_le_iff_le (one_le_pow_iff hn)

@[target, to_additive]
theorem pow_eq_one_iff {x : M} {n : ℕ} (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by sorry

end CovariantLE

section CovariantLT

variable [MulLeftStrictMono M] {a : M} {m n : ℕ}

@[target, to_additive nsmul_le_nsmul_iff_left]
theorem pow_le_pow_iff_right' (ha : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n :=
  sorry

@[target, to_additive nsmul_lt_nsmul_iff_left]
theorem pow_lt_pow_iff_right' (ha : 1 < a) : a ^ m < a ^ n ↔ m < n :=
  sorry

end CovariantLT

section CovariantLESwap

variable [MulLeftMono M] [MulRightMono M]

@[to_additive lt_of_nsmul_lt_nsmul_right]
theorem lt_of_pow_lt_pow_left' {a b : M} (n : ℕ) : a ^ n < b ^ n → a < b :=
  (pow_left_mono _).reflect_lt

@[to_additive min_lt_of_add_lt_two_nsmul]
theorem min_lt_of_mul_lt_sq {a b c : M} (h : a * b < c ^ 2) : min a b < c := by
  simpa using min_lt_max_of_mul_lt_mul (h.trans_eq <| pow_two _)

@[target, to_additive lt_max_of_two_nsmul_lt_add]
theorem lt_max_of_sq_lt_mul {a b c : M} (h : a ^ 2 < b * c) : a < max b c := by sorry

end CovariantLESwap

section CovariantLTSwap

variable [MulLeftStrictMono M] [MulRightStrictMono M]

@[to_additive le_of_nsmul_le_nsmul_right]
theorem le_of_pow_le_pow_left' {a b : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n → a ≤ b :=
  (pow_left_strictMono hn).le_iff_le.1

@[to_additive min_le_of_add_le_two_nsmul]
theorem min_le_of_mul_le_sq {a b c : M} (h : a * b ≤ c ^ 2) : min a b ≤ c := by
  simpa using min_le_max_of_mul_le_mul (h.trans_eq <| pow_two _)

@[to_additive le_max_of_two_nsmul_le_add]
theorem le_max_of_sq_le_mul {a b c : M} (h : a ^ 2 ≤ b * c) : a ≤ max b c := by
  simpa using min_le_max_of_mul_le_mul ((pow_two _).symm.trans_le h)

end CovariantLTSwap

@[to_additive Left.nsmul_neg_iff]
theorem Left.pow_lt_one_iff' [MulLeftStrictMono M] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 :=
  haveI := mulLeftMono_of_mulLeftStrictMono M
  pow_lt_one_iff hn.ne'

@[target]
theorem Left.pow_lt_one_iff [MulLeftStrictMono M] {n : ℕ} {x : M} (hn : 0 < n) :
    x ^ n < 1 ↔ x < 1 := sorry

@[to_additive]
theorem Right.pow_lt_one_iff [MulRightStrictMono M] {n : ℕ} {x : M}
    (hn : 0 < n) : x ^ n < 1 ↔ x < 1 :=
  haveI := mulRightMono_of_mulRightStrictMono M
  ⟨fun H => not_le.mp fun k => H.not_le <| Right.one_le_pow_of_le k, Right.pow_lt_one_of_lt hn⟩

end LinearOrder

end Monoid

section DivInvMonoid

variable [DivInvMonoid G] [Preorder G] [MulLeftMono G]

@[target, to_additive zsmul_nonneg]
theorem one_le_zpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ x ^ n := by sorry

end DivInvMonoid
