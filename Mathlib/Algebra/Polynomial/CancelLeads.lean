import VerifiedAgora.tagger
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.ComputeDegree

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancelLeads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancelLeads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/


namespace Polynomial

noncomputable section

open Polynomial

variable {R : Type*}

section Ring

variable [Ring R] (p q : R[X])

/-- `cancelLeads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
/-- `cancelLeads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancelLeads : R[X] := by sorry


variable {p q}

@[simp]
theorem neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p :=
  neg_sub _ _

@[target] theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm
    (comm : p.leadingCoeff * q.leadingCoeff = q.leadingCoeff * p.leadingCoeff)
    (h : p.natDegree ≤ q.natDegree) (hq : 0 < q.natDegree) :
    (p.cancelLeads q).natDegree < q.natDegree := by
  sorry


end Ring

section CommRing

variable [CommRing R] {p q : R[X]}

@[target] theorem dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r := by sorry


@[target] theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree ≤ q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree := by sorry


end CommRing

end

end Polynomial
