import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Rat.Cast.Defs

/-!
# Facts about `algebraMap` when the coefficient ring is a field.
-/

namespace algebraMap

universe u v w u₁ v₁
section FieldNontrivial

variable {R A : Type*} [Field R] [CommSemiring A] [Nontrivial A] [Algebra R A]

@[target, norm_cast, simp]
theorem coe_inj {a b : R} : (↑a : A) = ↑b ↔ a = b :=
  sorry

@[norm_cast]
theorem lift_map_eq_zero_iff (a : R) : (↑a : A) = 0 ↔ a = 0 := map_eq_zero _

end FieldNontrivial

section SemifieldSemidivisionRing

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
theorem coe_inv (r : R) : ↑r⁻¹ = ((↑r)⁻¹ : A) :=
  map_inv₀ (algebraMap R A) r

@[norm_cast]
theorem coe_div (r s : R) : ↑(r / s) = (↑r / ↑s : A) :=
  map_div₀ (algebraMap R A) r s

@[target, norm_cast]
theorem coe_zpow (r : R) (z : ℤ) : ↑(r ^ z) = (r : A) ^ z :=
  sorry

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type*) [Field R] [DivisionRing A] [Algebra R A]

@[target, norm_cast]
theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := sorry

end FieldDivisionRing

end algebraMap
