import VerifiedAgora.tagger
/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
-- Some proofs and docs came from mathlib3 `src/algebra/commute.lean` (c) Neil Strickland

import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Units.Basic

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`SemiconjBy a x y`), if `a * x = y * a`.
In this file we provide operations on `SemiconjBy _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `Commute a b = SemiconjBy a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

assert_not_exists MonoidWithZero DenselyOrdered

open scoped Int

variable {M : Type*}

namespace SemiconjBy

section Monoid

variable [Monoid M]

/-- If `a` semiconjugates a unit `x` to a unit `y`, then it semiconjugates `x⁻¹` to `y⁻¹`. -/
@[to_additive "If `a` semiconjugates an additive unit `x` to an additive unit `y`, then it
semiconjugates `-x` to `-y`."]
@[target]
theorem units_inv_right {a : M} {x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy a ↑x⁻¹ ↑y⁻¹ :=
  sorry

@[target, to_additive (attr := sorry
@[to_additive "If an additive unit `a` semiconjugates `x` to `y`, then `-a` semiconjugates `y` to
`x`."]
@[target]
theorem units_inv_symm_left {a : Mˣ} {x y : M} (h : SemiconjBy (↑a) x y) : SemiconjBy (↑a⁻¹) y x :=
  sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem units_val {a x y : Mˣ} (h : SemiconjBy a x y) : SemiconjBy (a : M) x y :=
  sorry

@[target, to_additive]
theorem units_of_val {a x y : Mˣ} (h : SemiconjBy (a : M) x y) : SemiconjBy a x y :=
  sorry

@[to_additive (attr := simp)]
theorem units_val_iff {a x y : Mˣ} : SemiconjBy (a : M) x y ↔ SemiconjBy a x y :=
  ⟨units_of_val, units_val⟩

@[target, to_additive (attr := by sorry

lemma conj_pow (u : Mˣ) (x : M) (n : ℕ) :
    ((↑u : M) * x * (↑u⁻¹ : M)) ^ n = (u : M) * x ^ n * (↑u⁻¹ : M) :=
  eq_divp_iff_mul_eq.2 ((u.mk_semiconjBy x).pow_right n).eq.symm

@[target]
lemma conj_pow' (u : Mˣ) (x : M) (n : ℕ) :
    ((↑u⁻¹ : M) * x * (u : M)) ^ n = (↑u⁻¹ : M) * x ^ n * (u : M) := sorry

end Units
