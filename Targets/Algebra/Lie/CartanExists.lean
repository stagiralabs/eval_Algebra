import VerifiedAgora.tagger
/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Rank

/-!
# Existence of Cartan subalgebras

In this file we prove existence of Cartan subalgebras in finite-dimensional Lie algebras,
following [barnes1967].

## Main results

* `exists_isCartanSubalgebra_of_finrank_le_card`:
  A Lie algebra `L` over a field `K` has a Cartan subalgebra,
  provided that the dimension of `L` over `K` is less than or equal to the cardinality of `K`.
* `exists_isCartanSubalgebra`:
  A finite-dimensional Lie algebra `L` over an infinite field `K` has a Cartan subalgebra.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

namespace LieAlgebra

section CommRing

variable {K R L M : Type*}
variable [Field K] [CommRing R]
variable [LieRing L] [LieAlgebra K L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [Module.Finite K L]
variable [Module.Finite R L] [Module.Free R L]
variable [Module.Finite R M] [Module.Free R M]

open Module LieSubalgebra Module.Free Polynomial

variable (K)

namespace engel_isBot_of_isMin

/-!
## Implementation details for the proof of `LieAlgebra.engel_isBot_of_isMin`

In this section we provide some auxiliary definitions and lemmas
that are used in the proof of `LieAlgebra.engel_isBot_of_isMin`,
which is the following statement:

Let `L` be a Lie algebra of dimension `n` over a field `K` with at least `n` elements.
Given a Lie subalgebra `U` of `L`, and an element `x ∈ U` such that `U ≤ engel K x`.
Suppose that `engel K x` is minimal amongst the Engel subalgebras `engel K y` for `y ∈ U`.
Then `engel K x ≤ engel K y` for all `y ∈ U`.

We follow the proof strategy of Lemma 2 in [barnes1967].
-/

variable (R M)

variable (x y : L)

open LieModule LinearMap

local notation "φ" => LieModule.toEnd R L M

/-- Let `x` and `y` be elements of a Lie `R`-algebra `L`, and `M` a Lie module over `M`.
Then the characteristic polynomials of the family of endomorphisms `⁅r • y + x, _⁆` of `M`
have coefficients that are polynomial in `r : R`.
In other words, we obtain a polynomial over `R[X]`
that specializes to the characteristic polynomial of `⁅r • y + x, _⁆` under the map `X ↦ r`.
This polynomial is captured in `lieCharpoly R M x y`. -/
private noncomputable
def lieCharpoly : Polynomial R[X] :=
  letI bL := chooseBasis R L
  (polyCharpoly (LieHom.toLinearMap φ) bL).map <| RingHomClass.toRingHom <|
    MvPolynomial.aeval fun i ↦ C (bL.repr y i) * X + C (bL.repr x i)

lemma lieCharpoly_monic : (lieCharpoly R M x y).Monic :=
  (polyCharpoly_monic _ _).map _

@[target]
lemma lieCharpoly_natDegree [Nontrivial R] : (lieCharpoly R M x y).natDegree = finrank R M := by sorry

variable {R} in
lemma lieCharpoly_map_eval (r : R) :
    (lieCharpoly R M x y).map (evalRingHom r) = (φ (r • y + x)).charpoly := by
  rw [lieCharpoly, map_map]
  set b := chooseBasis R L
  have aux : (fun i ↦ (b.repr y) i * r + (b.repr x) i) = b.repr (r • y + x) := by
    ext i; simp [mul_comm r]
  simp_rw [← coe_aeval_eq_evalRingHom, ← AlgHom.comp_toRingHom, MvPolynomial.comp_aeval,
    map_add, map_mul, aeval_C, Algebra.id.map_eq_id, RingHom.id_apply, aeval_X, aux,
    MvPolynomial.coe_aeval_eq_eval, polyCharpoly_map_eq_charpoly, LieHom.coe_toLinearMap]

lemma lieCharpoly_coeff_natDegree [Nontrivial R] (i j : ℕ) (hij : i + j = finrank R M) :
    ((lieCharpoly R M x y).coeff i).natDegree ≤ j := by
  classical
  rw [← mul_one j, lieCharpoly, coeff_map]
  apply MvPolynomial.aeval_natDegree_le
  · apply (polyCharpoly_coeff_isHomogeneous φ (chooseBasis R L) _ _ hij).totalDegree_le
  intro k
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    simp only [natDegree_X, le_rfl]
  · simp only [natDegree_C, zero_le]

end engel_isBot_of_isMin

end CommRing

section Field

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]

open Module LieSubalgebra LieSubmodule Polynomial Cardinal LieModule engel_isBot_of_isMin

/-- Let `L` be a Lie algebra of dimension `n` over a field `K` with at least `n` elements.
Given a Lie subalgebra `U` of `L`, and an element `x ∈ U` such that `U ≤ engel K x`.
Suppose that `engel K x` is minimal amongst the Engel subalgebras `engel K y` for `y ∈ U`.
Then `engel K x ≤ engel K y` for all `y ∈ U`.

Lemma 2 in [barnes1967]. -/
@[target]
lemma engel_isBot_of_isMin (hLK : finrank K L ≤ #K) (U : LieSubalgebra K L)
    (E : {engel K x | x ∈ U}) (hUle : U ≤ E) (hmin : IsMin E) :
    IsBot E := by sorry

variable (K L)

@[target]
lemma exists_isCartanSubalgebra_engel_of_finrank_le_card (h : finrank K L ≤ #K) :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by sorry

@[target]
lemma exists_isCartanSubalgebra_engel [Infinite K] :
    ∃ x : L, IsCartanSubalgebra (engel K x) := by sorry

end Field

end LieAlgebra
