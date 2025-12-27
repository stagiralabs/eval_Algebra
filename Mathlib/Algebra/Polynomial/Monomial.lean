import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Algebra.Polynomial.Basic

/-!
# Univariate monomials
-/


noncomputable section

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}
variable [Semiring R] {p q r : R[X]}

theorem monomial_one_eq_iff [Nontrivial R] {i j : ℕ} :
    (monomial i 1 : R[X]) = monomial j 1 ↔ i = j := by
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  exact AddMonoidAlgebra.of_injective.eq_iff

instance infinite [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h

@[target] theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  sorry


/-- If two ring homomorphisms from `MonoidAlgebra k G` are equal on all `single a 1`
and `single 1 b`, then they are equal. -/
@[target] theorem ringHom_ext {R} [Semiring k] [MulOneClass G] [Semiring R] {f g : MonoidAlgebra k G →+* R}
    (h₁ : ∀ b, f (single 1 b) = g (single 1 b)) (h_of : ∀ a, f (single a 1) = g (single a 1)) :
    f = g :=
  RingHom.coe_addMonoidHom_injective <|
    addHom_ext fun a b => by
      sorry


@[ext high]
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] →+* S} (h₁ : f.comp C = g.comp C)
    (h₂ : f X = g X) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂

end Polynomial
