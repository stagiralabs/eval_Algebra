import VerifiedAgora.tagger
/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Star.Basic

/-!
# The *-ring structure on suitable quotients of a *-ring.
-/

namespace RingQuot

universe u

variable {R : Type u} [Semiring R] (r : R → R → Prop)

section StarRing

variable [StarRing R]

@[target]
theorem Rel.star (hr : ∀ a b, r a b → r (star a) (star b))
    ⦃a b : R⦄ (h : Rel r a b) : Rel r (star a) (star b) := by sorry

@[target]
theorem star'_quot (hr : ∀ a b, r a b → r (star a) (star b)) {a} :
    (star' r hr ⟨Quot.mk _ a⟩ : RingQuot r) = ⟨Quot.mk _ (star a)⟩ := sorry
def starRing {R : Type u} [Semiring R] [StarRing R] (r : R → R → Prop)
    (hr : ∀ a b, r a b → r (star a) (star b)) : StarRing (RingQuot r) where
  star := star' r hr
  star_involutive := by
    rintro ⟨⟨⟩⟩
    simp [star'_quot]
  star_mul := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, mul_quot, star_mul]
  star_add := by
    rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩
    simp [star'_quot, add_quot, star_add]

end StarRing

end RingQuot
