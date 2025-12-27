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

@[target] theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) := by sorry


@[target] theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c := by sorry


section

variable [Mul R] [HasDistribNeg R] {a x y : R}

@[target] theorem neg_right : Commute a b → Commute a (-b) := by sorry


@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩

@[target] theorem neg_left : Commute a b → Commute (-a) b := by sorry


@[simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩

end

section

variable [MulOneClass R] [HasDistribNeg R]

theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) := by simp

@[target] theorem neg_one_left (a : R) : Commute (-1) a := by sorry


end

section

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

@[target] theorem sub_right : Commute a b → Commute a c → Commute a (b - c) := by sorry


@[simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

end

end SemiconjBy
