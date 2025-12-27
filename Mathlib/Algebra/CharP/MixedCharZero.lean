import VerifiedAgora.tagger
/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import Mathlib.Algebra.CharP.LocalRing
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Equal and mixed characteristic

In commutative algebra, some statements are simpler when working over a `ℚ`-algebra `R`, in which
case one also says that the ring has "equal characteristic zero". A ring that is not a
`ℚ`-algebra has either positive characteristic or there exists a prime ideal `I ⊂ R` such that
the quotient `R ⧸ I` has positive characteristic `p > 0`. In this case one speaks of
"mixed characteristic `(0, p)`", where `p` is only unique if `R` is local.

Examples of mixed characteristic rings are `ℤ` or the `p`-adic integers/numbers.

This file provides the main theorem `split_by_characteristic` that splits any proposition `P` into
the following three cases:

1) Positive characteristic: `CharP R p` (where `p ≠ 0`)
2) Equal characteristic zero: `Algebra ℚ R`
3) Mixed characteristic: `MixedCharZero R p` (where `p` is prime)

## Main definitions

- `MixedCharZero` : A ring has mixed characteristic `(0, p)` if it has characteristic zero
  and there exists an ideal such that the quotient `R ⧸ I` has characteristic `p`.

## Main results

- `split_equalCharZero_mixedCharZero` : Split a statement into equal/mixed characteristic zero.

This main theorem has the following three corollaries which include the positive
characteristic case for convenience:

- `split_by_characteristic` : Generally consider positive char `p ≠ 0`.
- `split_by_characteristic_domain` : In a domain we can assume that `p` is prime.
- `split_by_characteristic_localRing` : In a local ring we can assume that `p` is a prime power.

## Implementation Notes

We use the terms `EqualCharZero` and `AlgebraRat` despite not being such definitions in mathlib.
The former refers to the statement `∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)`, the latter
refers to the existence of an instance `[Algebra ℚ R]`. The two are shown to be
equivalent conditions.

## TODO

- Relate mixed characteristic in a local ring to p-adic numbers [NumberTheory.PAdics].
-/

variable (R : Type*) [CommRing R]

/-!
### Mixed characteristic
-/

/--
A ring of characteristic zero is of "mixed characteristic `(0, p)`" if there exists an ideal
such that the quotient `R ⧸ I` has characteristic `p`.

**Remark:** For `p = 0`, `MixedChar R 0` is a meaningless definition (i.e. satisfied by any ring)
as `R ⧸ ⊥ ≅ R` has by definition always characteristic zero.
One could require `(I ≠ ⊥)` in the definition, but then `MixedChar R 0` would mean something
like `ℤ`-algebra of extension degree `≥ 1` and would be completely independent from
whether something is a `ℚ`-algebra or not (e.g. `ℚ[X]` would satisfy it but `ℚ` wouldn't).
-/
class MixedCharZero (p : ℕ) : Prop where
  [toCharZero : CharZero R]
  charP_quotient : ∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p

namespace MixedCharZero

/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
@[target] theorem reduce_to_p_prime {P : Prop} :
    (∀ p > 0, MixedCharZero R p → P) ↔ ∀ p : ℕ, p.Prime → MixedCharZero R p → P := by
  sorry


/--
Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is maximal.
-/
/--
Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is maximal.
-/
@[target] theorem reduce_to_maximal_ideal {p : ℕ} (hp : Nat.Prime p) :
    (∃ I : Ideal R, I ≠ ⊤ ∧ CharP (R ⧸ I) p) ↔ ∃ I : Ideal R, I.IsMaximal ∧ CharP (R ⧸ I) p := by
  sorry


end MixedCharZero

/-!
### Equal characteristic zero

A commutative ring `R` has "equal characteristic zero" if it satisfies one of the following
equivalent properties:

1) `R` is a `ℚ`-algebra.
2) The quotient `R ⧸ I` has characteristic zero for any proper ideal `I ⊂ R`.
3) `R` has characteristic zero and does not have mixed characteristic for any prime `p`.

We show `(1) ↔ (2) ↔ (3)`, and most of the following is concerned with constructing
an explicit algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnatDen`)
for the direction `(1) ← (2)`.

Note: Property `(2)` is denoted as `EqualCharZero` in the statement names below.
-/

namespace EqualCharZero

/-- `ℚ`-algebra implies equal characteristic. -/
/-- `ℚ`-algebra implies equal characteristic. -/
@[target] theorem of_algebraRat [Algebra ℚ R] : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  sorry


section ConstructionAlgebraRat

variable {R}

/-- Internal: Not intended to be used outside this local construction. -/
theorem PNat.isUnit_natCast [h : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))]
    (n : ℕ+) : IsUnit (n : R) := by
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw [← Ideal.span_singleton_eq_top]
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (Ideal.span {↑n}))
  intro h_char_zero
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply h_char_zero.cast_injective.ne n.ne_zero
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

@[coe]
noncomputable def pnatCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ℕ+ → Rˣ :=
  fun n => (PNat.isUnit_natCast n).unit

/-- Internal: Not intended to be used outside this local construction. -/
noncomputable instance coePNatUnits
    [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : Coe ℕ+ Rˣ :=
  ⟨EqualCharZero.pnatCast⟩

/-- Internal: Not intended to be used outside this local construction. -/
/-- Internal: Not intended to be used outside this local construction. -/
@[target] theorem pnatCast_one [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] : ((1 : ℕ+) : Rˣ) = 1 := by
  sorry


/-- Internal: Not intended to be used outside this local construction. -/
/-- Internal: Not intended to be used outside this local construction. -/
@[target] theorem pnatCast_eq_natCast [Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I))] (n : ℕ+) :
    ((n : Rˣ) : R) = ↑n := by
  sorry


/-- Equal characteristic implies `ℚ`-algebra. -/
noncomputable def algebraRat (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    Algebra ℚ R :=
  haveI : Fact (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) := ⟨h⟩
  RingHom.toAlgebra
  { toFun := fun x => x.num /ₚ ↑x.pnatDen
    map_zero' := by simp [divp]
    map_one' := by simp
    map_mul' := by
      intro a b
      field_simp
      trans (↑((a * b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.mul_num_den' a b]
      simp
    map_add' := by
      intro a b
      field_simp
      trans (↑((a + b).num * a.den * b.den) : R)
      · simp_rw [Int.cast_mul, Int.cast_natCast]
        ring
      rw [Rat.add_num_den' a b]
      simp }

end ConstructionAlgebraRat

/-- Not mixed characteristic implies equal characteristic. -/
/-- Not mixed characteristic implies equal characteristic. -/
@[target] theorem of_not_mixedCharZero [CharZero R] (h : ∀ p > 0, ¬MixedCharZero R p) :
    ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  sorry


/-- Equal characteristic implies not mixed characteristic. -/
/-- Equal characteristic implies not mixed characteristic. -/
@[target] theorem to_not_mixedCharZero (h : ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) :
    ∀ p > 0, ¬MixedCharZero R p := by
  sorry


/--
A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
/--
A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
@[target] theorem iff_not_mixedCharZero [CharZero R] :
    (∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I)) ↔ ∀ p > 0, ¬MixedCharZero R p := by sorry


/-- A ring is a `ℚ`-algebra iff it has equal characteristic zero. -/
/-- A ring is a `ℚ`-algebra iff it has equal characteristic zero. -/
@[target] theorem nonempty_algebraRat_iff :
    Nonempty (Algebra ℚ R) ↔ ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  sorry


end EqualCharZero

/--
A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characteristic for some `p`.
-/
/--
A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characteristic for some `p`.
-/
@[target] theorem isEmpty_algebraRat_iff_mixedCharZero [CharZero R] :
    IsEmpty (Algebra ℚ R) ↔ ∃ p > 0, MixedCharZero R p := by
  sorry


section MainStatements

variable {P : Prop}

/-- Split a `Prop` in characteristic zero into equal and mixed characteristic. -/
/-- Split a `Prop` in characteristic zero into equal and mixed characteristic. -/
@[target] theorem split_equalCharZero_mixedCharZero [CharZero R] (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  sorry


example (n : ℕ) (h : n ≠ 0) : 0 < n :=
  zero_lt_iff.mpr h

/--
Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
/--
Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
@[target] theorem split_by_characteristic (h_pos : ∀ p : ℕ, p ≠ 0 → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  sorry


/--
In an `IsDomain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
/--
In an `IsDomain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
@[target] theorem split_by_characteristic_domain [IsDomain R] (h_pos : ∀ p : ℕ, Nat.Prime p → CharP R p → P)
    (h_equal : Algebra ℚ R → P) (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  sorry


/--
In a local ring `R`, split any predicate over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
/--
In a local ring `R`, split any predicate over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
@[target] theorem split_by_characteristic_localRing [IsLocalRing R]
    (h_pos : ∀ p : ℕ, IsPrimePow p → CharP R p → P) (h_equal : Algebra ℚ R → P)
    (h_mixed : ∀ p : ℕ, Nat.Prime p → MixedCharZero R p → P) : P := by
  sorry


end MainStatements
