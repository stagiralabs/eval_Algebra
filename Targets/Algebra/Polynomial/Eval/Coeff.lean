import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluation of polynomials

This file contains results on the interaction of `Polynomial.eval` and `Polynomial.coeff`
-/

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section

variable [Semiring S]
variable (f : R →+* S) (x : S)

@[target, simp]
theorem eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) := by sorry

@[target, simp]
theorem eval₂_C_X : eval₂ C X p = p :=
  sorry

section Eval₂

end Eval₂

section Eval

variable {x : R}

theorem coeff_zero_eq_eval_zero (p : R[X]) : coeff p 0 = p.eval 0 :=
  calc
    coeff p 0 = coeff p 0 * 0 ^ 0 := by simp
    _ = p.eval 0 := by
      symm
      rw [eval_eq_sum]
      exact Finset.sum_eq_single _ (fun b _ hb => by simp [zero_pow hb]) (by simp)

theorem zero_isRoot_of_coeff_zero_eq_zero {p : R[X]} (hp : p.coeff 0 = 0) : IsRoot p 0 := by
  rwa [coeff_zero_eq_eval_zero] at hp

end Eval

section Map

variable [Semiring S]
variable (f : R →+* S)

@[target, simp]
theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) := by sorry

lemma coeff_map_eq_comp (p : R[X]) (f : R →+* S) : (p.map f).coeff = f ∘ p.coeff := by
  ext n; exact coeff_map ..

@[target]
theorem map_map [Semiring T] (g : S →+* T) (p : R[X]) : (p.map f).map g = p.map (g.comp f) :=
  sorry

@[target, simp]
theorem map_id : p.map (RingHom.id _) = p := by sorry
def piEquiv {ι} [Finite ι] (R : ι → Type*) [∀ i, Semiring (R i)] :
    (∀ i, R i)[X] ≃+* ∀ i, (R i)[X] :=
  .ofBijective (Pi.ringHom fun i ↦ mapRingHom (Pi.evalRingHom R i))
    ⟨fun p q h ↦ by ext n i; simpa using congr_arg (fun p ↦ coeff (p i) n) h,
      fun p ↦ ⟨.ofFinsupp (.ofSupportFinite (fun n i ↦ coeff (p i) n) <|
        (Set.finite_iUnion fun i ↦ (p i).support.finite_toSet).subset fun n hn ↦ by
          simp only [Set.mem_iUnion, Finset.mem_coe, mem_support_iff, Function.mem_support] at hn ⊢
          contrapose! hn; exact funext hn), by ext i n; exact coeff_map _ _⟩⟩

@[target]
theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := sorry

@[target]
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := sorry

variable {f}

protected theorem map_eq_zero_iff (hf : Function.Injective f) : p.map f = 0 ↔ p = 0 :=
  map_eq_zero_iff (mapRingHom f) (map_injective f hf)

protected theorem map_ne_zero_iff (hf : Function.Injective f) : p.map f ≠ 0 ↔ p ≠ 0 :=
  (Polynomial.map_eq_zero_iff hf).not

variable (f)

@[target, simp]
theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[X] :=
  sorry

@[target, simp]
theorem mapRingHom_comp [Semiring T] (f : S →+* T) (g : R →+* S) :
    (mapRingHom f).comp (mapRingHom g) = mapRingHom (f.comp g) :=
  sorry

theorem eval₂_map [Semiring T] (g : S →+* T) (x : T) :
    (p.map f).eval₂ g x = p.eval₂ (g.comp f) x := by
  rw [eval₂_eq_eval_map, eval₂_eq_eval_map, map_map]

@[simp]
theorem eval_zero_map (f : R →+* S) (p : R[X]) : (p.map f).eval 0 = f (p.eval 0) := by
  simp [← coeff_zero_eq_eval_zero]

@[target, simp]
theorem eval_one_map (f : R →+* S) (p : R[X]) : (p.map f).eval 1 = f (p.eval 1) := by sorry

@[target, simp]
theorem eval_natCast_map (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).eval (n : S) = f (p.eval n) := by sorry

@[target, simp]
theorem eval_intCast_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (p : R[X]) (i : ℤ) :
    (p.map f).eval (i : S) = f (p.eval i) := by sorry

end Map

section HomEval₂

variable [Semiring S] [Semiring T] (f : R →+* S) (g : S →+* T) (p)

@[target]
theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) := by sorry

end HomEval₂

end Semiring

section CommSemiring

section Eval

section

variable [Semiring R] {p q : R[X]} {x : R} [Semiring S] (f : R →+* S)

theorem eval₂_hom (x : R) : p.eval₂ f (f x) = f (p.eval x) :=
  RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

end

section

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem evalRingHom_zero : evalRingHom 0 = constantCoeff :=
  DFunLike.ext _ _ fun p => p.coeff_zero_eq_eval_zero.symm

end

end Eval

section Map

@[target]
theorem support_map_subset [Semiring R] [Semiring S] (f : R →+* S) (p : R[X]) :
    (map f p).support ⊆ p.support := by sorry

@[target]
theorem support_map_of_injective [Semiring R] [Semiring S] (p : R[X]) {f : R →+* S}
    (hf : Function.Injective f) : (map f p).support = p.support := by sorry

variable [CommSemiring R] [CommSemiring S] (f : R →+* S)

theorem IsRoot.map {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot p x) : IsRoot (p.map f) (f x) := by
  rw [IsRoot, eval_map, eval₂_hom, h.eq_zero, f.map_zero]

@[target]
theorem IsRoot.of_map {R} [CommRing R] {f : R →+* S} {x : R} {p : R[X]} (h : IsRoot (p.map f) (f x))
    (hf : Function.Injective f) : IsRoot p x := by sorry

@[target]
theorem isRoot_map_iff {R : Type*} [CommRing R] {f : R →+* S} {x : R} {p : R[X]}
    (hf : Function.Injective f) : IsRoot (p.map f) (f x) ↔ IsRoot p x :=
  sorry

end Map

end CommSemiring

end Polynomial
