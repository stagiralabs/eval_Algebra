import VerifiedAgora.tagger
/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.IntervalCases

/-!
# Polynomials of specific degree

Facts about polynomials that have a specific integer degree.
-/

namespace Polynomial

section IsDomain

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
@[target]
theorem Monic.irreducible_iff_roots_eq_zero_of_degree_le_three {p : R[X]} (hp : p.Monic)
    (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by sorry

end IsDomain

section Field

variable {K : Type*} [Field K]

/-- A polynomial of degree 2 or 3 is irreducible iff it doesn't have roots. -/
@[target]
theorem irreducible_iff_roots_eq_zero_of_degree_le_three
    {p : K[X]} (hp2 : 2 ≤ p.natDegree) (hp3 : p.natDegree ≤ 3) : Irreducible p ↔ p.roots = 0 := by sorry

end Field

end Polynomial
