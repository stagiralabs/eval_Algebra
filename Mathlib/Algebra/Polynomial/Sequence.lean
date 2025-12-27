import VerifiedAgora.tagger
/-
Copyright (c) 2025 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Hill, Julian Berman, Austin Letson, Matej Penciak
-/
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.LinearAlgebra.Basis.Basic

/-!

# Polynomial sequences

We define polynomial sequences – sequences of polynomials `a₀, a₁, ...` such that the polynomial
`aᵢ` has degree `i`.

## Main definitions

* `Polynomial.Sequence R`: the type of polynomial sequences with coefficients in `R`

## Main statements

* `Polynomial.Sequence.basis`: a sequence is a basis for `R[X]`

## TODO

Generalize linear independence to:
  * `IsCancelAdd` semirings
  * just require coefficients are regular
  * arbitrary sets of polynomials which are pairwise different degree.
-/

open Submodule
open scoped Function

variable (R : Type*)

namespace Polynomial

/-- A sequence of polynomials such that the polynomial at index `i` has degree `i`. -/
structure Sequence [Semiring R] where
  /-- The `i`'th element in the sequence. Use `S i` instead, defined via `CoeFun`. -/
  protected elems' : ℕ → R[X]
  /-- The `i`'th element in the sequence has degree `i`. Use `S.degree_eq` instead. -/
  protected degree_eq' (i : ℕ) : (elems' i).degree = i

attribute [coe] Sequence.elems'

namespace Sequence

variable {R}

/-- Make `S i` mean `S.elems' i`. -/
instance coeFun [Semiring R] : CoeFun (Sequence R) (fun _ ↦  ℕ → R[X]) := ⟨Sequence.elems'⟩

section Semiring

variable [Semiring R] (S : Sequence R)

/-- `S i` has degree `i`. -/
@[simp]
lemma degree_eq (i : ℕ) : (S i).degree = i := S.degree_eq' i

/-- `S i` has `natDegree` `i`. -/
/-- `S i` has `natDegree` `i`. -/
@[target] lemma natDegree_eq (i : ℕ) : (S i).natDegree = i := by sorry


/-- No polynomial in the sequence is zero. -/
/-- A left-regular element of a `Nontrivial` `MulZeroClass` is non-zero. -/
@[target] theorem IsLeftRegular.ne_zero [Nontrivial R] (la : IsLeftRegular a) : a ≠ 0 := by
  sorry


/-- `S i` has strictly monotone degree. -/
/-- `S i` has strictly monotone degree. -/
@[target] lemma degree_strictMono : StrictMono <| degree ∘ S := fun _ _  ↦ by sorry


/-- `S i` has strictly monotone natural degree. -/
/-- `S i` has strictly monotone natural degree. -/
@[target] lemma natDegree_strictMono : StrictMono <| natDegree ∘ S := fun _ _  ↦ by sorry


end Semiring

section Ring

variable [Ring R] (S : Sequence R)

/-- A polynomial sequence spans `R[X]` if all of its elements' leading coefficients are units. -/
protected lemma span (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) : span R (Set.range S) = ⊤ := by
  rw [eq_top_iff']
  intro P
  -- we proceed via strong induction on the degree `n`, after getting the 0 polynomial done
  nontriviality R using Subsingleton.eq_zero P
  generalize hp : P.natDegree = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases p_ne_zero : P = 0
    · simp [p_ne_zero]
    -- let u be the inverse of `S n`'s leading coefficient
    obtain ⟨u, leftinv, rightinv⟩ := isUnit_iff_exists.mp <| hCoeff n

    -- We'll show `P` is the difference of two terms in the span:
    --   a polynomial whose leading term matches `P`'s and lower degree terms match `S n`'s
    let head := P.leadingCoeff • u • S n -- a polynomial whose leading term matches P's and whose
    --   and then an error correcting polynomial which gets us to `P`'s actual lower degree terms
    let tail := P - head
    -- `head` is in the span because it's a multiple of `S n`
    have head_mem_span : head ∈ span R (Set.range S) := by
      have in_span : S n ∈ span R (Set.range S) := subset_span (by simp)
      have smul_span := smul_mem (span R (Set.range S)) (P.leadingCoeff • u) in_span
      rwa [smul_assoc] at smul_span
    -- to show the tail is in the span we really need consider only when we needed to "correct" for
    -- some lower degree terms in `P`
    by_cases tail_eq_zero : tail = 0
    · simp [head_mem_span, sub_eq_iff_eq_add.mp tail_eq_zero]
    -- we'll do so via the induction hypothesis,
    -- and once we show we can use it, `P` is a difference of two members of the span
    refine sub_mem_iff_left _ head_mem_span |>.mp <|
      -- so let's prove the tail has degree less than `n`
      ih tail.natDegree (natDegree_lt_iff_degree_lt tail_eq_zero |>.mpr ?_) _ rfl
    -- first we want that `P` and `head` have the same degree
    have isRightRegular_smul_leadingCoeff : IsRightRegular (u • S n).leadingCoeff := by
      simpa [leadingCoeff_smul_of_smul_regular _ <| IsSMulRegular.of_mul_eq_one leftinv, rightinv]
        using isRegular_one.right
    have u_degree_same := degree_smul_of_isRightRegular_leadingCoeff
      (left_ne_zero_of_mul_eq_one rightinv) (hCoeff n).isRegular.right
    have head_degree_eq := degree_smul_of_isRightRegular_leadingCoeff
      (leadingCoeff_ne_zero.mpr p_ne_zero) isRightRegular_smul_leadingCoeff
    rw [u_degree_same, S.degree_eq n, ← hp, eq_comm,
      ← degree_eq_natDegree p_ne_zero, hp] at head_degree_eq
    -- and that this degree is also their `natDegree`
    have head_degree_eq_natDegree : head.degree = head.natDegree := degree_eq_natDegree <| by
      by_cases n_eq_zero : n = 0
      · dsimp [head]
        rw [n_eq_zero, ← coeff_natDegree, natDegree_eq] at rightinv
        rwa [n_eq_zero, eq_C_of_natDegree_eq_zero <| S.natDegree_eq 0,
          smul_C, smul_eq_mul, map_mul, ← C_mul, rightinv, smul_C, smul_eq_mul,
          mul_one, C_eq_zero, leadingCoeff_eq_zero]
      · apply head.ne_zero_of_degree_gt
        rw [← head_degree_eq]
        exact natDegree_pos_iff_degree_pos.mp (by omega)
    -- and that they have matching leading coefficients
    have hPhead : P.leadingCoeff = head.leadingCoeff := by
      rw [degree_eq_natDegree, head_degree_eq_natDegree] at head_degree_eq
      nth_rw 2 [← coeff_natDegree]
      rw_mod_cast [← head_degree_eq, hp]
      dsimp [head]
      nth_rw 2 [← S.natDegree_eq n]
      rwa [coeff_smul, coeff_smul, coeff_natDegree, smul_eq_mul, smul_eq_mul, rightinv, mul_one]
    -- which we can now combine to show that `P - head` must have strictly lower degree,
    -- as its leading term has been cancelled, completing our proof.
    have tail_degree_lt := P.degree_sub_lt head_degree_eq p_ne_zero hPhead
    rwa [degree_eq_natDegree p_ne_zero, hp] at tail_degree_lt

section NoZeroDivisors

variable [NoZeroDivisors R]

/-- Polynomials in a polynomial sequence are linearly independent. -/
/-- Polynomials in a polynomial sequence are linearly independent. -/
@[target] lemma linearIndependent :
    LinearIndependent R S := linearIndependent_iff'.mpr <| fun s g eqzero i hi ↦ by
  sorry


variable (hCoeff : ∀ i, IsUnit (S i).leadingCoeff)

/-- Every polynomial sequence is a basis of `R[X]`. -/
noncomputable def basis : Basis ℕ R R[X] :=
  Basis.mk S.linearIndependent <| eq_top_iff.mp <| S.span hCoeff

/-- The `i`'th basis vector is the `i`'th polynomial in the sequence. -/
/-- The `i`'th basis vector is the `i`'th polynomial in the sequence. -/
@[target] lemma basis_eq_self  (i : ℕ) : S.basis hCoeff i = S i := by sorry


/-- Basis elements have strictly monotone degree. -/
/-- Basis elements have strictly monotone degree. -/
@[target] lemma basis_degree_strictMono : StrictMono <| degree ∘ (S.basis hCoeff) := fun _ _  ↦ by sorry


/-- Basis elements have strictly monotone natural degree. -/
/-- Basis elements have strictly monotone natural degree. -/
@[target] lemma basis_natDegree_strictMono : StrictMono <| natDegree ∘ (S.basis hCoeff) := fun _ _  ↦ by sorry


end NoZeroDivisors

end Ring

end Sequence

end Polynomial
