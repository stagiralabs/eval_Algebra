import VerifiedAgora.tagger
/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Order.Synonym

/-!
# Lemmas about division (semi)rings and (semi)fields

-/

open Function OrderDual Set

universe u

variable {K L : Type*}

section DivisionSemiring

variable [DivisionSemiring K] {a b c d : K}

theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]

@[field_simps]
theorem div_add_div_same (a b c : K) : a / c + b / c = (a + b) / c :=
  (add_div _ _ _).symm

@[target]
theorem same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by sorry

@[target]
theorem div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by sorry

@[target]
theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  sorry

@[target]
theorem div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  sorry
theorem inv_add_inv' (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ :=
  let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b

@[target]
theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by sorry

@[target]
theorem add_div_eq_mul_add_div (a b : K) (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  sorry

@[target, field_simps]
theorem add_div' (a b c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by sorry

@[target, field_simps]
theorem div_add' (a b c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by sorry

variable [NeZero (2 : K)]

@[simp] lemma add_self_div_two (a : K) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel_right₀ a two_ne_zero]

@[simp] lemma add_halves (a : K) : a / 2 + a / 2 = a := by rw [← add_div, add_self_div_two]

end DivisionSemiring

section DivisionRing

variable [DivisionRing K] {a b c d : K}

@[simp]
theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]

@[simp]
theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by rw [neg_div, div_self h]

@[target]
theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by sorry

@[target]
theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by sorry

@[target]
theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  sorry

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

@[target]
theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  sorry

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

/-- See `inv_sub_inv` for the more convenient version when `K` is commutative. -/
theorem inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ :=
  let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b

@[target]
theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by sorry

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _

protected theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d) := by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd

protected theorem Commute.inv_sub_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]

variable [NeZero (2 : K)]

lemma sub_half (a : K) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves]
lemma half_sub (a : K) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]

end DivisionRing

section Semifield

variable [Semifield K] {a b d : K}

@[target]
theorem div_add_div (a : K) (c : K) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) :=
  sorry

theorem one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
  (Commute.all a _).one_div_add_one_div ha hb

@[target]
theorem inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
  sorry

end Semifield

section Field

variable [Field K]

attribute [local simp] mul_assoc mul_comm mul_left_comm

@[field_simps]
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) :=
  (Commute.all b _).div_sub_div (Commute.all _ _) hb hd

@[target]
theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by sorry

@[target, field_simps]
theorem sub_div' {a b c : K} (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by sorry

@[target, field_simps]
theorem div_sub' {a b c : K} (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by sorry

-- see Note [lower instance priority]
instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }

end Field

section NoncomputableDefs

variable {R : Type*} [Nontrivial R]

/-- Constructs a `DivisionRing` structure on a `Ring` consisting only of units and 0. -/
-- See note [reducible non-instances]
noncomputable abbrev DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- Constructs a `Field` structure on a `CommRing` consisting only of units and 0. -/
-- See note [reducible non-instances]
noncomputable abbrev Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

end NoncomputableDefs

namespace Function.Injective
variable [Zero K] [Add K] [Neg K] [Sub K] [One K] [Mul K] [Inv K] [Div K] [SMul ℕ K] [SMul ℤ K]
  [SMul ℚ≥0 K] [SMul ℚ K] [Pow K ℕ] [Pow K ℤ] [NatCast K] [IntCast K] [NNRatCast K] [RatCast K]
  (f : K → L) (hf : Injective f)

/-- Pullback a `DivisionSemiring` along an injective function. -/
-- See note [reducible non-instances]
protected abbrev divisionSemiring [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q) : DivisionSemiring K where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  nnratCast_def q := hf <| by rw [nnratCast, NNRat.cast_def, div, natCast, natCast]
  nnqsmul := (· • ·)
  nnqsmul_def q a := hf <| by rw [nnqsmul, NNRat.smul_def, mul, nnratCast]

/-- Pullback a `DivisionSemiring` along an injective function. -/
-- See note [reducible non-instances]
protected abbrev divisionRing [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) : DivisionRing K where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
  ratCast_def q := hf <| by rw [ratCast, div, intCast, natCast, Rat.cast_def]
  qsmul := (· • ·)
  qsmul_def q a := hf <| by rw [qsmul, mul, Rat.smul_def, ratCast]

/-- Pullback a `Field` along an injective function. -/
-- See note [reducible non-instances]
protected abbrev semifield [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q) : Semifield K where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast

/-- Pullback a `Field` along an injective function. -/
-- See note [reducible non-instances]
protected abbrev field [Field L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) :
    Field K where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow
    natCast intCast nnratCast ratCast

end Function.Injective

/-! ### Order dual -/

namespace OrderDual

instance instRatCast [RatCast K] : RatCast Kᵒᵈ := ‹_›
instance instDivisionSemiring [DivisionSemiring K] : DivisionSemiring Kᵒᵈ := ‹_›
instance instDivisionRing [DivisionRing K] : DivisionRing Kᵒᵈ := ‹_›
instance instSemifield [Semifield K] : Semifield Kᵒᵈ := ‹_›
instance instField [Field K] : Field Kᵒᵈ := ‹_›

end OrderDual

@[simp] lemma toDual_ratCast [RatCast K] (n : ℚ) : toDual (n : K) = n := rfl

@[simp] lemma ofDual_ratCast [RatCast K] (n : ℚ) : (ofDual n : K) = n := rfl

/-! ### Lexicographic order -/

namespace Lex

instance instRatCast [RatCast K] : RatCast (Lex K) := ‹_›
instance instDivisionSemiring [DivisionSemiring K] : DivisionSemiring (Lex K) := ‹_›
instance instDivisionRing [DivisionRing K] : DivisionRing (Lex K) := ‹_›
instance instSemifield [Semifield K] : Semifield (Lex K) := ‹_›
instance instField [Field K] : Field (Lex K) := ‹_›

end Lex

@[simp] lemma toLex_ratCast [RatCast K] (n : ℚ) : toLex (n : K) = n := rfl

@[simp] lemma ofLex_ratCast [RatCast K] (n : ℚ) : (ofLex n : K) = n := rfl
