import VerifiedAgora.tagger
/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Tactic.Positivity.Finset

/-!
# The Schwartz-Zippel lemma

This file contains a proof of the
[Schwartz-Zippel](https://en.wikipedia.org/wiki/Schwartz%E2%80%93Zippel_lemma) lemma.

This lemma tells us that the probability that a nonzero multivariable polynomial over an integral
domain evaluates to zero at a random point is bounded by the degree of the polynomial over the size
of the field, or more generally, that a nonzero multivariable polynomial over any integral domain
has a low probability of being zero when evaluated at points drawn at random from some finite subset
of the field. This lemma is useful as a probabilistic polynomial identity test.

## Main results

- `MvPolynomial.schwartz_zippel_sup_sum`:
  Sharper version of Schwartz-Zippel for a dependent product of sets `S i`, with the RHS being
  the supremum of `∑ i, degᵢ s / #(S i)` ranging over monomials `s` of the polynomial.
- `MvPolynomial.schwartz_zippel_sum_degreeOf`:
  Schwartz-Zippel for a dependent product of sets `S i`,
  with the RHS being the sum of `degᵢ p / #(S i)`.
- `MvPolynomial.schwartz_zippel_totalDegree`:
  Nondependent version of `schwartz_zippel_sup_sum`, with the RHS being `p.totalDegree / #S`.

## TODO

* Generalize to polynomials over arbitrary variable types
* Prove the stronger statement that one can replace the degrees of `p` in the RHS by the degrees of
  the maximal monomial of `p` in some lexicographic order.
* Write a tactic to apply this lemma to a given polynomial

## References

* [demillo_lipton_1978]
* [schwartz_1980]
* [zippel_1979]
-/

open Fin Finset Fintype

local notation:70 s:70 " ^^ " n:71 => piFinset fun i : Fin n ↦ s i

namespace MvPolynomial
variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

-- A user should be able to provide `hp` as a named argument
-- regardless of whether one has used pattern-matching or induction to prove the lemma.
set_option linter.unusedVariables false in
/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from a product of finite subsets `S i` of the integral
domain is bounded by the supremum of `∑ i, degᵢ s / #(S i)` ranging over monomials `s` of `p`. -/
set_option linter.unusedVariables false in
/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from a product of finite subsets `S i` of the integral
domain is bounded by the supremum of `∑ i, degᵢ s / #(S i)` ranging over monomials `s` of `p`. -/
@[target] lemma schwartz_zippel_sup_sum :
    ∀ {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Fin n → Finset R),
      #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤
        p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0)
  | 0, p, hp, S => by
    -- Because `p` is a polynomial over zero variables, it is constant.
    sorry


/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from a product of finite subsets `S i` of the integral
domain is bounded by the sum of `degᵢ p / #(S i)`. -/
/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from a product of finite subsets `S i` of the integral
domain is bounded by the sum of `degᵢ p / #(S i)`. -/
@[target] lemma schwartz_zippel_sum_degreeOf {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (S : Fin n → Finset R) :
    #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0) := by
  sorry


/-- The **Schwartz-Zippel lemma**

For a nonzero multivariable polynomial `p` over an integral domain, the probability that `p`
evaluates to zero at points drawn at random from some finite subset `S` of the integral domain is
bounded by the degree of `p` over `#S`. This version presents this lemma in terms of `Finset`. -/
lemma schwartz_zippel_totalDegree {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Finset R) :
    #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (#S ^ n : ℚ≥0) ≤ p.totalDegree / #S :=
  calc
    _ = #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (∏ i : Fin n, #S : ℚ≥0) := by simp
    _ ≤ p.support.sup fun s ↦ ∑ i, (s i / #S : ℚ≥0) := schwartz_zippel_sup_sum hp _
    _ = p.totalDegree / #S := by
      obtain rfl | hs := S.eq_empty_or_nonempty
      · simp
        simp only [← _root_.bot_eq_zero, sup_bot]
      simp_rw [totalDegree, Nat.cast_finsetSup]
      rw [sup_div₀ (ha := show 0 < (#S : ℚ≥0) by positivity)]
      simp [← sum_div, Finsupp.sum_fintype]

end MvPolynomial
