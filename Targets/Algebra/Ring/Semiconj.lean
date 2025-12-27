import VerifiedAgora.tagger
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Ring.Defs

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib.Algebra.Group.Basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib.Algebra.Ring.Defs`.

-/


universe u

variable {R : Type u}

open Function

namespace SemiconjBy

@[simp]
theorem add_right [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]
theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a + b) x y := by
  simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

@[target]
theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by sorry

@[target, simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  sorry

theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[target, simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  sorry

variable [MulOneClass R] [HasDistribNeg R]

@[target]
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) := by sorry

@[target]
theorem neg_one_left (x : R) : SemiconjBy (-1) x x := by sorry

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

@[simp]
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x - x') (y - y') := by
  simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[target, simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a - b) x y := by sorry

end SemiconjBy
