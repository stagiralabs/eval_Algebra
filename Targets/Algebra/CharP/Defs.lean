import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Defs

/-!
# Characteristic of semirings

## Main definitions
 * `CharP R p` expresses that the ring (additive monoid with one) `R` has characteristic `p`
 * `ringChar`: the characteristic of a ring
 * `ExpChar R p` expresses that the ring (additive monoid with one) `R` has
    exponential characteristic `p` (which is `1` if `R` has characteristic 0, and `p` if it has
    prime characteristic `p`)
-/

assert_not_exists Field Finset OrderHom

variable (R : Type*)

namespace CharP
section AddMonoidWithOne
variable [AddMonoidWithOne R] (p : ℕ)

/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `CharP R 0` and `CharZero R` need not coincide.
* `CharP R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `CharZero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`CharZero {0, 1}` does not hold and yet `CharP {0, 1} 0` does.
This example is formalized in `Counterexamples/CharPZeroNeCharZero.lean`.
-/
@[mk_iff]
class _root_.CharP : Prop where
  cast_eq_zero_iff' : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x

variable [CharP R p] {a b : ℕ}

-- Porting note: the field of the structure had implicit arguments where they were
-- explicit in Lean 3
lemma cast_eq_zero_iff (a : ℕ) : (a : R) = 0 ↔ p ∣ a := cast_eq_zero_iff' a

variable {R} in
lemma congr {q : ℕ} (h : p = q) : CharP R q := h ▸ ‹CharP R p›

@[simp] lemma cast_eq_zero : (p : R) = 0 := (cast_eq_zero_iff R p p).2 dvd_rfl

-- TODO: This lemma needs to be `@[simp]` for confluence in the presence of `CharP.cast_eq_zero` and
-- `Nat.cast_ofNat`, but with `no_index` on its entire LHS, it matches literally every expression so
-- is too expensive. If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, this can be made `@[simp]`.
--
-- @[simp]
lemma ofNat_eq_zero [p.AtLeastTwo] : (ofNat(p) : R) = 0 := cast_eq_zero R p

lemma eq {p q : ℕ} (_hp : CharP R p) (_hq : CharP R q) : p = q :=
  Nat.dvd_antisymm ((cast_eq_zero_iff R p q).1 (cast_eq_zero _ _))
    ((cast_eq_zero_iff R q p).1 (cast_eq_zero _ _))

instance ofCharZero [CharZero R] : CharP R 0 where
  cast_eq_zero_iff' x := by rw [zero_dvd_iff, ← Nat.cast_zero, Nat.cast_inj]

end AddMonoidWithOne

section AddGroupWithOne
variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

@[target]
lemma intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by sorry

lemma charP_to_charZero [CharP R 0] : CharZero R :=
  charZero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

@[target]
lemma charP_zero_iff_charZero : CharP R 0 ↔ CharZero R :=
  sorry

end AddGroupWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

lemma «exists» : ∃ p, CharP R p :=
  letI := Classical.decEq R
  by_cases
    (fun H : ∀ p : ℕ, (p : R) = 0 → p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_contradiction fun H2 =>
              Nat.find_min (not_forall.1 H)
                (Nat.mod_lt x <|
                  Nat.pos_of_ne_zero <| not_of_not_imp <| Nat.find_spec (not_forall.1 H))
                (not_imp_of_and_not
                  ⟨by
                    rwa [← Nat.mod_add_div x (Nat.find (not_forall.1 H)), Nat.cast_add,
                      Nat.cast_mul,
                      of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
                      zero_mul, add_zero] at H1,
                    H2⟩)),
          fun H1 => by
          rw [← Nat.mul_div_cancel' H1, Nat.cast_mul,
            of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
            zero_mul]⟩⟩⟩

lemma existsUnique : ∃! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

@[deprecated (since := "2024-12-17")] alias exists_unique := existsUnique

end NonAssocSemiring
end CharP

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ringChar [NonAssocSemiring R] : ℕ := Classical.choose (CharP.existsUnique R)

namespace ringChar
variable [NonAssocSemiring R]

lemma spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  letI : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)

lemma eq (p : ℕ) [C : CharP R p] : ringChar R = p :=
  ((Classical.choose_spec (CharP.existsUnique R)).2 p C).symm

instance charP : CharP R (ringChar R) :=
  ⟨spec R⟩

variable {R}

lemma of_eq {p : ℕ} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h

@[target]
lemma eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p :=
  sorry

@[target]
lemma dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x :=
  sorry

@[simp]
lemma eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0

@[target]
lemma Nat.cast_ringChar : (ringChar R : R) = 0 := by sorry

end ringChar

lemma CharP.neg_one_ne_one [Ring R] (p : ℕ) [CharP R p] [Fact (2 < p)] : (-1 : R) ≠ (1 : R) := by
  rw [ne_comm, ← sub_ne_zero, sub_neg_eq_add, one_add_one_eq_two, ← Nat.cast_two, Ne,
    CharP.cast_eq_zero_iff R p 2]
  exact fun h ↦ (Fact.out : 2 < p).not_le <| Nat.le_of_dvd Nat.zero_lt_two h

namespace CharP

section

variable [NonAssocRing R]

lemma cast_eq_mod (p : ℕ) [CharP R p] (k : ℕ) : (k : R) = (k % p : ℕ) :=
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [cast_eq_zero]

lemma ringChar_zero_iff_CharZero : ringChar R = 0 ↔ CharZero R := by
  rw [ringChar.eq_iff, charP_zero_iff_charZero]

end

section Semiring

variable [NonAssocSemiring R]

@[target]
lemma char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := sorry

section NoZeroDivisors

variable [NoZeroDivisors R]

@[target]
lemma char_is_prime_of_two_le (p : ℕ) [CharP R p] (hp : 2 ≤ p) : Nat.Prime p :=
  sorry

section Nontrivial

variable [Nontrivial R]

@[target]
lemma char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  sorry
lemma char_prime_of_ne_zero {p : ℕ} [CharP R p] (hp : p ≠ 0) : p.Prime :=
  (CharP.char_is_prime_or_zero R p).resolve_right hp

@[target]
lemma exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by sorry

@[target]
lemma char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime :=
  sorry

end Nontrivial

end NoZeroDivisors

end Semiring

section NonAssocSemiring

variable {R} [NonAssocSemiring R]

-- This lemma is not an instance, to make sure that trying to prove `α` is a subsingleton does
-- not try to find a ring structure on `α`, which can be expensive.
@[target]
lemma CharOne.subsingleton [CharP R 1] : Subsingleton R :=
  sorry

@[target]
lemma false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by sorry

@[target]
lemma ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by sorry

@[target]
lemma nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R :=
  sorry

end NonAssocSemiring
end CharP

namespace NeZero

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

lemma of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) :=
  ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

lemma not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

end NeZero

/-!
### Exponential characteristic

This section defines the exponential characteristic, which is defined to be 1 for a ring with
characteristic 0 and the same as the ordinary characteristic, if the ordinary characteristic is
prime. This concept is useful to simplify some theorem statements.
This file establishes a few basic results relating it to the (ordinary characteristic).
The definition is stated for a semiring, but the actual results are for nontrivial rings
(as far as exponential characteristic one is concerned), respectively a ring without zero-divisors
(for prime characteristic).
-/

section AddMonoidWithOne
variable [AddMonoidWithOne R]

/-- The definition of the exponential characteristic of a semiring. -/
class inductive ExpChar : ℕ → Prop
  | zero [CharZero R] : ExpChar 1
  | prime {q : ℕ} (hprime : q.Prime) [hchar : CharP R q] : ExpChar q

instance expChar_prime (p) [CharP R p] [Fact p.Prime] : ExpChar R p := ExpChar.prime Fact.out
instance expChar_one [CharZero R] : ExpChar R 1 := ExpChar.zero

@[target]
lemma expChar_ne_zero (p : ℕ) [hR : ExpChar R p] : p ≠ 0 := by sorry

variable {R} in
/-- The exponential characteristic is unique. -/
lemma ExpChar.eq {p q : ℕ} (hp : ExpChar R p) (hq : ExpChar R q) : p = q := by
  rcases hp with ⟨hp⟩ | ⟨hp'⟩
  · rcases hq with hq | hq'
    exacts [rfl, False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hq'))]
  · rcases hq with hq | hq'
    exacts [False.elim (Nat.not_prime_zero (CharP.eq R ‹_› (CharP.ofCharZero R) ▸ hp')),
      CharP.eq R ‹_› ‹_›]

lemma ExpChar.congr {p : ℕ} (q : ℕ) [hq : ExpChar R q] (h : q = p) : ExpChar R p := h ▸ hq

/-- The exponential characteristic is one if the characteristic is zero. -/
@[target]
lemma expChar_one_of_char_zero (q : ℕ) [hp : CharP R 0] [hq : ExpChar R q] : q = 1 := by sorry
@[target]
lemma char_eq_expChar_iff (p q : ℕ) [hp : CharP R p] [hq : ExpChar R q] : p = q ↔ p.Prime := by sorry
@[target]
lemma expChar_is_prime_or_one (q : ℕ) [hq : ExpChar R q] : Nat.Prime q ∨ q = 1 := by sorry
@[target]
lemma expChar_pos (q : ℕ) [ExpChar R q] : 0 < q := by sorry
@[target]
lemma expChar_pow_pos (q : ℕ) [ExpChar R q] (n : ℕ) : 0 < q ^ n :=
  sorry

end AddMonoidWithOne

section NonAssocSemiring
variable [NonAssocSemiring R]

/-- Noncomputable function that outputs the unique exponential characteristic of a semiring. -/
noncomputable def ringExpChar : ℕ := max (ringChar R) 1

lemma ringExpChar.eq (q : ℕ) [h : ExpChar R q] : ringExpChar R = q := by
  rcases h with _ | h
  · haveI := CharP.ofCharZero R
    rw [ringExpChar, ringChar.eq R 0]; rfl
  rw [ringExpChar, ringChar.eq R q]
  exact Nat.max_eq_left h.one_lt.le

@[simp] lemma ringExpChar.eq_one [CharZero R] : ringExpChar R = 1 := by
  rw [ringExpChar, ringChar.eq_zero, max_eq_right (Nat.zero_le _)]

section Nontrivial
variable [Nontrivial R]

/-- The exponential characteristic is one if the characteristic is zero. -/
lemma char_zero_of_expChar_one (p : ℕ) [hp : CharP R p] [hq : ExpChar R 1] : p = 0 := by
  cases hq
  · exact CharP.eq R hp inferInstance
  · exact False.elim (CharP.char_ne_one R 1 rfl)

-- This could be an instance, but there are no `ExpChar R 1` instances in mathlib.
/-- The characteristic is zero if the exponential characteristic is one. -/
@[target]
lemma charZero_of_expChar_one' [hq : ExpChar R 1] : CharZero R := by sorry
@[target]
lemma expChar_one_iff_char_zero (p q : ℕ) [CharP R p] [ExpChar R q] : q = 1 ↔ p = 0 := by sorry

end Nontrivial
end NonAssocSemiring

lemma ExpChar.exists [Ring R] [IsDomain R] : ∃ q, ExpChar R q := by
  obtain _ | ⟨p, ⟨hp⟩, _⟩ := CharP.exists' R
  exacts [⟨1, .zero⟩, ⟨p, .prime hp⟩]

@[target]
lemma ExpChar.exists_unique [Ring R] [IsDomain R] : ∃! q, ExpChar R q :=
  sorry

instance ringExpChar.expChar [Ring R] [IsDomain R] : ExpChar R (ringExpChar R) := by
  obtain ⟨q, _⟩ := ExpChar.exists R
  rwa [ringExpChar.eq R q]

variable {R} in
lemma ringExpChar.of_eq [Ring R] [IsDomain R] {q : ℕ} (h : ringExpChar R = q) : ExpChar R q :=
  h ▸ ringExpChar.expChar R

variable {R} in
@[target]
lemma ringExpChar.eq_iff [Ring R] [IsDomain R] {q : ℕ} : ringExpChar R = q ↔ ExpChar R q :=
  sorry