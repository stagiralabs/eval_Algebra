import VerifiedAgora.tagger
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.
-/


variable {α : Type*}

/-- Left `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
@[target]
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k := by sorry
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k := by
  refine fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ ?_)
  rw [sub_mul, sub_eq_zero, h']

@[target]
theorem isRegular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  sorry

@[target]
theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k ≠ 0 :=
  sorry

section IsDomain

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero [Semiring α] [IsDomain α] :
    CancelMonoidWithZero α :=
  { }

variable [CommSemiring α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  { mul_left_cancel_of_ne_zero := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero }

end IsDomain
