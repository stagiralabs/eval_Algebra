import VerifiedAgora.tagger
/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Span

/-!
# Bounding the coefficients of the quotient and remainder of polynomials

This file proves that, for polynomials `p q : R[X]`, the coefficients of `p /ₘ q` and `p %ₘ q` can
be written as sums of products of coefficients of `p` and `q`.

Precisely, we show that each summand needs at most one coefficient of `p` and `deg p` coefficients
of `q`.
-/

namespace Polynomial
variable {ι R S : Type*} [CommRing R] [Ring S] [Algebra R S]

local notation "deg("p")" => natDegree p
local notation3 "coeffs("p")" => Set.range (coeff p)
local notation3 "spanCoeffs("p")" => 1 ⊔ Submodule.span R coeffs(p)

open Submodule Set in
@[target]
lemma coeff_divModByMonicAux_mem_span_pow_mul_span : ∀ (p q : S[X]) (hq : q.Monic) (i),
    (p.divModByMonicAux hq).1.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) ∧
    (p.divModByMonicAux hq).2.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p)
  | p, q, hq, i => by
    rw [divModByMonicAux]
    have H₀ (i) : p.coeff i ∈ spanCoeffs(q) ^ deg(p) * spanCoeffs(p) := by sorry
@[target]
lemma coeff_modByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : ∀ i, p.coeff i ∈ Mp) (hp' : 1 ∈ Mp)
    (Mq : Submodule R S) (hq : ∀ i, q.coeff i ∈ Mq) (hq' : 1 ∈ Mq) (i : ℕ) :
    (p %ₘ q).coeff i ∈ Mq ^ p.natDegree * Mp := by sorry
@[target]
lemma coeff_divByMonic_mem_pow_natDegree_mul (p q : S[X])
    (Mp : Submodule R S) (hp : ∀ i, p.coeff i ∈ Mp) (hp' : 1 ∈ Mp)
    (Mq : Submodule R S) (hq : ∀ i, q.coeff i ∈ Mq) (hq' : 1 ∈ Mq) (i : ℕ) :
    (p /ₘ q).coeff i ∈ Mq ^ p.natDegree * Mp := by sorry

variable [DecidableEq ι] {i j : ι}

open Function Ideal in
@[target]
lemma idealSpan_range_update_divByMonic (hij : i ≠ j) (v : ι → R[X]) (hi : (v i).Monic) :
    span (Set.range (Function.update v j (v j %ₘ v i))) = span (Set.range v) := by sorry

end Polynomial
