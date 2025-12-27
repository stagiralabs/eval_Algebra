import VerifiedAgora.tagger
/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `LinearRecurrence` so that
`LinearRecurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `LinearEquiv`
  between the solution space and `Fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equals.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mkSol`), the
interesting part would be to determinate closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/


noncomputable section

open Finset

open Polynomial

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
structure LinearRecurrence (α : Type*) [CommSemiring α] where
  /-- Order of the linear recurrence -/
  order : ℕ
  /-- Coefficients of the linear recurrence -/
  coeffs : Fin order → α

instance (α : Type*) [CommSemiring α] : Inhabited (LinearRecurrence α) :=
  ⟨⟨0, default⟩⟩

namespace LinearRecurrence

section CommSemiring

variable {α : Type*} [CommSemiring α] (E : LinearRecurrence α)

/-- We say that a sequence `u` is solution of `LinearRecurrence order coeffs` when we have
  `u (n + order) = ∑ i : Fin order, coeffs i * u (n + i)` for any `n`. -/
/-- We say that a sequence `u` is solution of `LinearRecurrence order coeffs` when we have
  `u (n + order) = ∑ i : Fin order, coeffs i * u (n + i)` for any `n`. -/
def IsSolution (u : ℕ → α) := by sorry


/-- A solution of a `LinearRecurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
/-- A solution of a `LinearRecurrence` which satisfies certain initial conditions.
  We will prove this is the only such solution. -/
def mkSol (init : Fin E.order → α) : ℕ → α
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by sorry


/-- `E.mkSol` indeed gives solutions to `E`. -/
/-- `E.mkSol` indeed gives solutions to `E`. -/
@[target] theorem is_sol_mkSol (init : Fin E.order → α) : E.IsSolution (E.mkSol init) := by
  sorry


/-- `E.mkSol init`'s first `E.order` terms are `init`. -/
/-- `E.mkSol init`'s first `E.order` terms are `init`. -/
@[target] theorem mkSol_eq_init (init : Fin E.order → α) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  sorry


/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mkSol init n`. -/
/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `∀ n, u n = E.mkSol init n`. -/
@[target] theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → α} {init : Fin E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  sorry


/-- If `u` is a solution to `E` and `init` designates its first `E.order` values,
  then `u = E.mkSol init`. This proves that `E.mkSol init` is the only solution
  of `E` whose first `E.order` values are given by `init`. -/
theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → α} {init : Fin E.order → α} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)

/-- The space of solutions of `E`, as a `Submodule` over `α` of the module `ℕ → α`. -/
/-- The space of solutions of `E`, as a `Submodule` over `α` of the module `ℕ → α`. -/
def solSpace : Submodule α (ℕ → α) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by sorry


/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
/-- Defining property of the solution space : `u` is a solution
  iff it belongs to the solution space. -/
@[target] theorem is_sol_iff_mem_solSpace (u : ℕ → α) : E.IsSolution u ↔ u ∈ E.solSpace := by sorry


/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `LinearEquiv`. -/
/-- The function that maps a solution `u` of `E` to its first
  `E.order` terms as a `LinearEquiv`. -/
def toInit : E.solSpace ≃ₗ[α] Fin E.order → α where
  toFun u x := (u : ℕ → α) x
  map_add' u v := by
    sorry


/-- Two solutions are equal iff they are equal on `range E.order`. -/
/-- Two solutions are equal iff they are equal on `range E.order`. -/
@[target] theorem sol_eq_of_eq_init (u v : ℕ → α) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  sorry



/-- `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
  where `n := E.order`. -/
def tupleSucc : (Fin E.order → α) →ₗ[α] Fin E.order → α where
  toFun X i := if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    simp only
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    simp only
    split_ifs with h <;> simp [h, mul_sum]
    exact sum_congr rfl fun x _ ↦ by ac_rfl

end CommSemiring

section StrongRankCondition

-- note: `StrongRankCondition` is the same as `Nontrivial` on `CommRing`s, but that result,
-- `commRing_strongRankCondition`, is in a much later file.
variable {α : Type*} [CommRing α] [StrongRankCondition α] (E : LinearRecurrence α)

/-- The dimension of `E.solSpace` is `E.order`. -/
/-- The dimension of `E.solSpace` is `E.order`. -/
@[target] theorem solSpace_rank : Module.rank α E.solSpace = E.order := by sorry


end StrongRankCondition

section CommRing

variable {α : Type*} [CommRing α] (E : LinearRecurrence α)

/-- The characteristic polynomial of `E` is
`X ^ E.order - ∑ i : Fin E.order, (E.coeffs i) * X ^ i`. -/
def charPoly : α[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)

/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
/-- The geometric sequence `q^n` is a solution of `E` iff
  `q` is a root of `E`'s characteristic polynomial. -/
@[target] theorem geom_sol_iff_root_charPoly (q : α) :
    (E.IsSolution fun n ↦ q ^ n) ↔ E.charPoly.IsRoot q := by
  sorry


end CommRing

end LinearRecurrence
