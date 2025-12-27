import VerifiedAgora.tagger
/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Logic.Basic

/-!

# Characteristic zero

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`CharZero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## TODO

* Unify with `CharP` (possibly using an out-parameter)
-/

/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.)

*Warning*: for a semiring `R`, `CharZero R` and `CharP R 0` need not coincide.
* `CharZero R` requires an injection `ℕ ↪ R`;
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`.
For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
class CharZero (R) [AddMonoidWithOne R] : Prop where
  /-- An additive monoid with one has characteristic zero if the canonical map `ℕ → R` is
  injective. -/
  cast_injective : Function.Injective (Nat.cast : ℕ → R)

variable {R : Type*}

@[target] theorem charZero_of_inj_zero [AddGroupWithOne R] (H : ∀ n : ℕ, (n : R) = 0 → n = 0) :
    CharZero R :=
  ⟨@fun m n h => by
    sorry


namespace Nat

variable [AddMonoidWithOne R] [CharZero R]

@[target] theorem cast_injective : Function.Injective (Nat.cast : ℕ → R) := by sorry


@[target] theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n := by sorry


@[target] lemma cast_eq_zero : (p : R) = 0 := by sorry


@[target] theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 := by sorry


theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 :=
  mod_cast n.succ_ne_zero

@[target] theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by sorry


@[target] theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 := by sorry


instance (priority := 100) AtLeastTwo.toNeZero (n : ℕ) [n.AtLeastTwo] : NeZero n :=
  ⟨Nat.ne_of_gt (Nat.le_of_lt one_lt)⟩

end Nat

namespace OfNat

variable [AddMonoidWithOne R] [CharZero R]

@[target] lemma ofNat_ne_zero (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R) ≠ 0 := by sorry


@[simp] lemma zero_ne_ofNat (n : ℕ) [n.AtLeastTwo] : 0 ≠ (ofNat(n) : R) :=
  (ofNat_ne_zero n).symm

@[target] lemma ofNat_ne_one (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R) ≠ 1 := by sorry


@[target] lemma one_ne_ofNat (n : ℕ) [n.AtLeastTwo] : (1 : R) ≠ ofNat(n) := by sorry


@[target] lemma ofNat_eq_ofNat {m n : ℕ} [m.AtLeastTwo] [n.AtLeastTwo] :
    (ofNat(m) : R) = ofNat(n) ↔ (ofNat m : ℕ) = ofNat n := by sorry


end OfNat

namespace NeZero

instance charZero {M} {n : ℕ} [NeZero n] [AddMonoidWithOne M] [CharZero M] : NeZero (n : M) :=
  ⟨Nat.cast_ne_zero.mpr out⟩

instance charZero_one {M} [AddMonoidWithOne M] [CharZero M] : NeZero (1 : M) where
  out := by
    rw [← Nat.cast_one, Nat.cast_ne_zero]
    trivial

instance charZero_ofNat {M} {n : ℕ} [n.AtLeastTwo] [AddMonoidWithOne M] [CharZero M] :
    NeZero (OfNat.ofNat n : M) :=
  ⟨OfNat.ofNat_ne_zero n⟩

end NeZero
