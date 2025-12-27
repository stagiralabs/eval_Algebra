import VerifiedAgora.tagger
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import Aesop
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Int.Init
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`Algebra/Group/Defs.lean`.
-/

assert_not_exists MonoidWithZero DenselyOrdered

open Function

variable {α β G M : Type*}

section ite
variable [Pow α β]

@[target] lemma pow_dite (p : Prop) [Decidable p] (a : α) (b : p → β) (c : ¬ p → β) :
    a ^ (if h : p then b h else c h) = if h : p then a ^ b h else a ^ c h := by sorry


@[target] lemma dite_pow (p : Prop) [Decidable p] (a : p → α) (b : ¬ p → α) (c : β) :
    (if h : p then a h else b h) ^ c = if h : p then a h ^ c else b h ^ c := by sorry


@[to_additive (attr := by sorry


@[to_additive (attr := by sorry

attribute [to_additive (attr := simp)] dite_smul smul_dite ite_smul smul_ite

end ite

section Semigroup
variable [Semigroup α]

@[to_additive]
instance Semigroup.to_isAssociative : Std.Associative (α := α) (· * ·) := ⟨mul_assoc⟩

/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[to_additive (attr := simp) "Composing two additions on the left by `y` then `x`
is equal to an addition on the left by `x + y`."]
theorem comp_mul_left (x y : α) : (x * ·) ∘ (y * ·) = (x * y * ·) := by
  ext z
  simp [mul_assoc]

/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[target] theorem comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) := by
  sorry


end Semigroup

@[to_additive]
instance CommMagma.to_isCommutative [CommMagma G] : Std.Commutative (α := G) (· * ·) := ⟨mul_comm⟩

section MulOneClass

variable [MulOneClass M]

@[target] theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} :
    ite P (a * b) 1 = ite P a 1 * ite P b 1 := by
  sorry


@[target] theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} :
    ite P 1 (a * b) = ite P 1 a * ite P 1 b := by
  sorry


@[target] theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  sorry


@[target] theorem one_mul_eq_id : ((1 : M) * ·) = id := by sorry


@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

@[target] theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  sorry


@[target] theorem mul_right_comm (a b c : G) : a * b * c = a * c * b := by
  sorry


@[target] theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  sorry


@[target] theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  sorry


@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]

end CommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section Monoid
variable [Monoid M] {a b : M} {m n : ℕ}

@[target] lemma pow_boole (P : Prop) [Decidable P] (a : M) :
    (a ^ if P then 1 else 0) = if P then a else 1 := by sorry


@[target] lemma pow_mul_pow_sub (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  sorry


@[to_additive sub_nsmul_nsmul_add]
lemma pow_sub_mul_pow (a : M) (h : m ≤ n) : a ^ (n - m) * a ^ m = a ^ n := by
  rw [← pow_add, Nat.sub_add_cancel h]

@[to_additive sub_one_nsmul_add]
lemma mul_pow_sub_one (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

@[to_additive add_sub_one_nsmul]
lemma pow_sub_one_mul (hn : n ≠ 0) (a : M) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ, Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
/-- If `x ^ n = 1`, then `x ^ m` is the same as `x ^ (m % n)` -/
@[target] lemma pow_eq_pow_mod (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  sorry


@[target] lemma pow_mul_pow_eq_one : ∀ n, a * b = 1 → a ^ n * b ^ n = 1
  | 0, _ => by sorry


@[target] lemma mul_left_iterate (a : M) : ∀ n : ℕ, (a * ·)^[n] = (a ^ n * ·)
  | 0 =>  by sorry


@[target] lemma mul_right_iterate (a : M) : ∀ n : ℕ, (· * a)^[n] = (· * a ^ n)
  | 0 =>  by sorry


@[target] lemma mul_left_iterate_apply_one (a : M) : (a * ·)^[n] 1 = a ^ n := by sorry


@[target] lemma mul_right_iterate_apply_one (a : M) : (· * a)^[n] 1 = a ^ n := by sorry


@[target] lemma pow_iterate (k : ℕ) : ∀ n : ℕ, (fun x : M ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by sorry


end Monoid

section CommMonoid
variable [CommMonoid M] {x y z : M}

@[target] theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z := by sorry


@[target] lemma mul_pow (a b : M) : ∀ n, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by sorry


end CommMonoid

section LeftCancelMonoid

variable [LeftCancelMonoid M] {a b : M}

@[to_additive (attr := simp)]
theorem mul_right_eq_self : a * b = a ↔ b = 1 := calc
  a * b = a ↔ a * b = a * 1 := by rw [mul_one]
  _ ↔ b = 1 := mul_left_cancel_iff

@[to_additive (attr := by sorry


@[target] theorem mul_right_ne_self : a * b ≠ a ↔ b ≠ 1 := by sorry


@[target] theorem self_ne_mul_right : a ≠ a * b ↔ b ≠ 1 := by sorry


end LeftCancelMonoid

section RightCancelMonoid

variable [RightCancelMonoid M] {a b : M}

@[target] theorem mul_left_eq_self : a * b = b ↔ a = 1 := calc
  a * b = b ↔ a * b = 1 * b := by sorry


@[target] theorem mul_left_ne_self : a * b ≠ b ↔ a ≠ 1 := by sorry


@[target] theorem self_ne_mul_left : b ≠ a * b ↔ a ≠ 1 := by sorry


end RightCancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid α] {a b c d : α}

@[target] lemma eq_iff_eq_of_mul_eq_mul (h : a * b = c * d) : a = c ↔ b = d := by sorry

@[target] lemma ne_iff_ne_of_mul_eq_mul (h : a * b = c * d) : a ≠ c ↔ b ≠ d := by sorry


end CancelCommMonoid

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

@[to_additive (attr := by sorry


@[to_additive (attr := by sorry


@[target] theorem inv_injective : Function.Injective (Inv.inv : G → G) := by sorry


@[target] theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ := by sorry


variable (G)

@[to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self

@[target] theorem leftInverse_inv : LeftInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ := by sorry


@[to_additive]
theorem rightInverse_inv : RightInverse (fun a : G ↦ a⁻¹) fun a ↦ a⁻¹ :=
  inv_inv

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G]

@[target] theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  sorry


@[to_additive, field_simps] -- The attributes are out of order on purpose
@[target] theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  sorry


@[target] theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by sorry


@[target] theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by sorry


end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

@[target] theorem div_one (a : G) : a / 1 = a := by sorry


@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c d : α}

attribute [local simp] mul_assoc div_eq_mul_inv

@[target] theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ := by sorry


@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]

@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]

@[target] theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by sorry


@[target] lemma eq_of_inv_mul_eq_one (h : a⁻¹ * b = 1) : a = b := by sorry


@[target] lemma eq_of_mul_inv_eq_one (h : a * b⁻¹ = 1) : a = b := by sorry


@[target] theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 := by sorry


variable (a b c)

@[target] theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by sorry


@[target] theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by sorry


@[to_additive (attr := simp)]
theorem inv_div : (a / b)⁻¹ = b / a := by simp

@[target] theorem one_div_div : 1 / (a / b) = b / a := by sorry


@[target] theorem one_div_one_div : 1 / (1 / a) = a := by sorry


@[target] theorem div_eq_div_iff_comm : a / b = c / d ↔ b / a = d / c :=
  inv_inj.symm.trans <| by sorry


@[to_additive]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }

@[target] lemma inv_pow (a : α) : ∀ n : ℕ, a⁻¹ ^ n = (a ^ n)⁻¹
  | 0 => by sorry

@[to_additive zsmul_zero, simp]
lemma one_zpow : ∀ n : ℤ, (1 : α) ^ n = 1
  | (n : ℕ)    => by rw [zpow_natCast, one_pow]
  | .negSucc n => by rw [zpow_negSucc, one_pow, inv_one]

@[target] lemma zpow_neg (a : α) : ∀ n : ℤ, a ^ (-n) = (a ^ n)⁻¹
  | (_ + 1 : ℕ) => DivInvMonoid.zpow_neg' _ _
  | 0 => by sorry


@[to_additive neg_one_zsmul_add]
lemma mul_zpow_neg_one (a b : α) : (a * b) ^ (-1 : ℤ) = b ^ (-1 : ℤ) * a ^ (-1 : ℤ) := by
  simp only [zpow_neg, zpow_one, mul_inv_rev]

@[target] lemma inv_zpow (a : α) : ∀ n : ℤ, a⁻¹ ^ n = (a ^ n)⁻¹
  | (n : ℕ)    => by sorry


@[to_additive (attr := simp) zsmul_neg']
lemma inv_zpow' (a : α) (n : ℤ) : a⁻¹ ^ n = a ^ (-n) := by rw [inv_zpow, zpow_neg]

@[target] lemma one_div_pow (a : α) (n : ℕ) : (1 / a) ^ n = 1 / a ^ n := by sorry


@[target] lemma one_div_zpow (a : α) (n : ℤ) : (1 / a) ^ n = 1 / a ^ n := by sorry


variable {a b c}

@[to_additive (attr := by sorry


@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.not

@[target] theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  sorry

@[target] lemma zpow_mul (a : α) : ∀ m n : ℤ, a ^ (m * n) = (a ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    sorry


@[to_additive mul_zsmul]
lemma zpow_mul' (a : α) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by rw [Int.mul_comm, zpow_mul]

@[target] theorem zpow_comm (a : α) (m n : ℤ) : (a ^ m) ^ n = (a ^ n) ^ m := by sorry


variable (a b c)

@[to_additive, field_simps] -- The attributes are out of order on purpose
@[to_additive, field_simps] -- The attributes are out of order on purpose
@[target] theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by sorry


@[target] theorem div_inv_eq_mul : a / b⁻¹ = a * b := by sorry


@[target] theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  sorry


end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp

@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp

@[target] theorem div_eq_inv_mul : a / b = b⁻¹ * a := by sorry


@[target] theorem inv_mul_eq_div : a⁻¹ * b = b / a := by sorry


@[target] lemma inv_div_comm (a b : α) : a⁻¹ / b = b⁻¹ / a := by sorry


@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp

@[target] theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by sorry


@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp

@[target] theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by sorry


@[target] theorem div_right_comm : a / b / c = a / c / b := by sorry


@[target] theorem div_div : a / b / c = a / (b * c) := by sorry


@[target] theorem div_mul : a / b * c = a / (b / c) := by sorry


@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp

@[target] theorem mul_div_right_comm : a * b / c = a / c * b := by sorry


@[target] theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by sorry


@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp

@[target] theorem one_div_mul_eq_div : 1 / a * b = b / a := by sorry


@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp

@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp

@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp

@[target] theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by sorry


@[target] theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by sorry


@[target] theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by sorry


@[target] theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by sorry


@[target] lemma mul_zpow : ∀ n : ℤ, (a * b) ^ n = a ^ n * b ^ n
  | (n : ℕ) => by sorry


@[target] lemma div_pow (a b : α) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := by
  sorry


@[target] lemma div_zpow (a b : α) (n : ℤ) : (a / b) ^ n = a ^ n / b ^ n := by
  sorry


attribute [field_simps] div_pow div_zpow

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G} {n : ℤ}

@[target] theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by sorry


@[target] theorem mul_left_surjective (a : G) : Surjective (a * ·) := by sorry


@[target] theorem mul_right_surjective (a : G) : Function.Surjective fun x ↦ x * a := by sorry


@[target] theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by sorry


@[target] theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by sorry


@[target] theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by sorry


@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]

@[target] theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by sorry


@[target] theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by sorry


@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]

@[target] theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by sorry


@[target] theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h ↦ by sorry


@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]

/-- Variant of `mul_eq_one_iff_eq_inv` with swapped equality. -/
@[to_additive]
theorem mul_eq_one_iff_eq_inv' : a * b = 1 ↔ b = a⁻¹ := by
  rw [mul_eq_one_iff_inv_eq, eq_comm]

/-- Variant of `mul_eq_one_iff_inv_eq` with swapped equality. -/
@[to_additive]
theorem mul_eq_one_iff_inv_eq' : a * b = 1 ↔ b⁻¹ = a := by
  rw [mul_eq_one_iff_eq_inv, eq_comm]

@[target] theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 := by sorry


@[target] theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 := by sorry


@[target] theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h ↦ by sorry


@[target] theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h ↦ by sorry


@[target] theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h ↦ by sorry


@[target] theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h ↦ by sorry


@[target] theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by sorry


@[target] theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by sorry


@[to_additive (attr := simp)]
theorem conj_eq_one_iff : a * b * a⁻¹ = 1 ↔ b = 1 := by
  rw [mul_inv_eq_one, mul_right_eq_self]

@[target] theorem div_left_injective : Function.Injective fun a ↦ a / b := by
  -- FIXME this could be by `simpa`, but it fails. This is probably a bug in `simpa`.
  sorry


@[target] theorem div_right_injective : Function.Injective fun a ↦ b / a := by
  -- FIXME see above
  sorry


@[target] lemma div_mul_cancel_right (a b : G) : a / (b * a) = b⁻¹ := by sorry


@[target] theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  sorry


@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]

@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]

@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]

@[target] theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by sorry


@[to_additive (attr := simp)]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff

@[target] theorem div_left_inj : b / a = c / a ↔ b = c := by
  sorry


@[target] theorem div_mul_div_cancel (a b c : G) : a / b * (b / c) = a / c := by
  sorry


@[target] theorem div_div_div_cancel_right (a b c : G) : a / c / (b / c) = a / b := by
  sorry


@[deprecated (since := "2024-08-24")] alias div_div_div_cancel_right' := div_div_div_cancel_right

@[target] theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h ↦ by sorry


@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one

@[target] theorem div_eq_self : a / b = a ↔ b = 1 := by sorry


@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[target] theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by sorry


@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]

@[target] theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x ↦ x / c) fun x ↦ x * c := by sorry


@[target] theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x ↦ x * c) fun x ↦ x / c := by sorry


@[target] theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x ↦ c * x) fun x ↦ c⁻¹ * x := by sorry


@[target] theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x ↦ c⁻¹ * x) fun x ↦ c * x := by sorry


@[target] lemma pow_natAbs_eq_one : a ^ n.natAbs = 1 ↔ a ^ n = 1 := by sorry


@[target] lemma pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by sorry


@[target] theorem inv_pow_sub (a : G) {m n : ℕ} (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  sorry


@[target] lemma zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by sorry


@[to_additive sub_one_zsmul]
lemma zpow_sub_one (a : G) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ :=
  calc
    a ^ (n - 1) = a ^ (n - 1) * a * a⁻¹ := (mul_inv_cancel_right _ _).symm
    _ = a ^ n * a⁻¹ := by rw [← zpow_add_one, Int.sub_add_cancel]

@[target] lemma zpow_add (a : G) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  sorry


@[to_additive one_add_zsmul]
lemma zpow_one_add (a : G) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by rw [zpow_add, zpow_one]

@[target] lemma mul_self_zpow (a : G) (n : ℤ) : a * a ^ n = a ^ (n + 1) := by
  sorry


@[target] lemma mul_zpow_self (a : G) (n : ℤ) : a ^ n * a = a ^ (n + 1) := by sorry


@[to_additive sub_zsmul] lemma zpow_sub (a : G) (m n : ℤ) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  rw [Int.sub_eq_add_neg, zpow_add, zpow_neg]

@[to_additive natCast_sub_natCast_zsmul]
lemma zpow_natCast_sub_natCast (a : G) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  simpa [div_eq_mul_inv] using zpow_sub a m n

@[target] lemma zpow_natCast_sub_one (a : G) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  sorry


@[target] lemma zpow_one_sub_natCast (a : G) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  sorry


@[target] lemma zpow_mul_comm (a : G) (m n : ℤ) : a ^ m * a ^ n = a ^ n * a ^ m := by
  sorry


@[target] theorem zpow_eq_zpow_emod {x : G} (m : ℤ) {n : ℤ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % n) :=
  calc
    x ^ m = x ^ (m % n + n * (m / n)) := by sorry


theorem zpow_eq_zpow_emod' {x : G} (m : ℤ) {n : ℕ} (h : x ^ n = 1) :
    x ^ m = x ^ (m % (n : ℤ)) := zpow_eq_zpow_emod m (by simpa)

@[target] lemma zpow_iterate (k : ℤ) : ∀ n : ℕ, (fun x : G ↦ x ^ k)^[n] = (· ^ k ^ n)
  | 0 => by sorry


/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the left. For subgroups generated by more than one element, see
`Subgroup.closure_induction_left`. -/
@[target] lemma zpow_induction_left {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (g * a)) (h_inv : ∀ a, P a → P (g⁻¹ * a)) (n : ℤ) : P (g ^ n) := by
  sorry


/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
/-- To show a property of all powers of `g` it suffices to show it is closed under multiplication
by `g` and `g⁻¹` on the right. For subgroups generated by more than one element, see
`Subgroup.closure_induction_right`. -/
@[target] lemma zpow_induction_right {g : G} {P : G → Prop} (h_one : P (1 : G))
    (h_mul : ∀ a, P a → P (a * g)) (h_inv : ∀ a, P a → P (a * g⁻¹)) (n : ℤ) : P (g ^ n) := by
  sorry


end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

@[target] theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  sorry


@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]

@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]

@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h, div_eq_mul_inv, mul_comm c, mul_inv_cancel_left]

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[target] theorem div_div_self (a : G₀) : a / (a / a) = a := by
  sorry


@[target] theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by sorry


@[to_additive (attr := by sorry


@[target] theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by sorry


@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]

@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]

@[target] theorem mul_div_cancel_left (a b : G) : a * b / a = b := by sorry


@[target] theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  sorry


@[to_additive (attr := simp)]
theorem div_mul_cancel_left (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel_left]

-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined in `Algebra.Group.Commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel a b]

@[target] theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  sorry


@[target] theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  sorry


@[to_additive (attr := simp)]
theorem div_mul_div_cancel' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm]; apply div_mul_div_cancel

@[deprecated (since := "2024-08-24")] alias div_mul_div_cancel'' := div_mul_div_cancel'

@[target] theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  sorry


@[target] theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  sorry


@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]

@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]

end CommGroup

section multiplicative

variable [Monoid β] (p r : α → α → Prop) [IsTotal α r] (f : α → α → β)

@[to_additive additive_of_symmetric_of_isTotal]
lemma multiplicative_of_symmetric_of_isTotal
    (hsymm : Symmetric p) (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c)
    {a b c : α} (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c := by
  have hmul' : ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c := by
    intros b c rbc pab pbc pac
    obtain rab | rba := total_of r a b
    · exact hmul rab rbc pab pbc pac
    rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
    obtain rac | rca := total_of r a c
    · rw [hmul rba rac (hsymm pab) pac pbc]
    · rw [hmul rbc rca pbc (hsymm pac) (hsymm pab), mul_assoc, hf_swap (hsymm pac), mul_one]
  obtain rbc | rcb := total_of r b c
  · exact hmul' rbc pab pbc pac
  · rw [hmul' rcb pac (hsymm pbc) pab, mul_assoc, hf_swap (hsymm pbc), mul_one]

/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[target] theorem multiplicative_of_isTotal (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c := by
  sorry


end multiplicative

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = ⇑f^[n]`. -/
@[to_additive]
lemma hom_coe_pow {F : Type*} [Monoid F] (c : F → M → M) (h1 : c 1 = id)
    (hmul : ∀ f g, c (f * g) = c f ∘ c g) (f : F) : ∀ n, c (f ^ n) = (c f)^[n]
  | 0 => by
    rw [pow_zero, h1]
    rfl
  | n + 1 => by rw [pow_succ, iterate_succ, hmul, hom_coe_pow c h1 hmul f n]
