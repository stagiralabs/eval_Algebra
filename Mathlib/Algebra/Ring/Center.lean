import VerifiedAgora.tagger
/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Center
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Centers of rings

-/

assert_not_exists RelIso Finset Subsemigroup Field

variable {M : Type*}

namespace Set

variable (M)

@[target] theorem natCast_mem_center [NonAssocSemiring M] (n : ℕ) : (n : M) ∈ Set.center M where
  comm _ := by sorry


@[target] theorem ofNat_mem_center [NonAssocSemiring M] (n : ℕ) [n.AtLeastTwo] :
    ofNat(n) ∈ Set.center M := by sorry


@[target] theorem intCast_mem_center [NonAssocRing M] (n : ℤ) : (n : M) ∈ Set.center M where
  comm _ := by sorry


variable {M}

@[target] theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M  where
  comm _ := by sorry


@[simp]
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a ∈ Set.center M) :
    -a ∈ Set.center M where
  comm _ := by rw [← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  mid_assoc _ _ := by rw [← neg_mul_comm, ha.mid_assoc, neg_mul_comm, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]

end Set
