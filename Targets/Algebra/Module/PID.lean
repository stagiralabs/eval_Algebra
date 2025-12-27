import VerifiedAgora.tagger
/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Module.DedekindDomain
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Structure of finitely generated modules over a PID

## Main statements

* `Module.equiv_directSum_of_isTorsion` : A finitely generated torsion module over a PID is
  isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
* `Module.equiv_free_prod_directSum` : A finitely generated module over a PID is isomorphic to the
  product of a free module (its torsion free part) and a direct sum of the form above (its torsion
  submodule).

## Notation

* `R` is a PID and `M` is a (finitely generated for main statements) `R`-module, with additional
  torsion hypotheses in the intermediate lemmas.
* `N` is an `R`-module lying over a higher type universe than `R`. This assumption is needed on the
  final statement for technical reasons.
* `p` is an irreducible element of `R` or a tuple of these.

## Implementation details

We first prove (`Submodule.isInternal_prime_power_torsion_of_pid`) that a finitely generated
torsion module is the internal direct sum of its `p i ^ e i`-torsion submodules for some
(finitely many) prime powers `p i ^ e i`. This is proved in more generality for a Dedekind domain
at `Submodule.isInternal_prime_power_torsion`.

Then we treat the case of a `p ^ ∞`-torsion module (that is, a module where all elements are
cancelled by scalar multiplication by some power of `p`) and apply it to the `p i ^ e i`-torsion
submodules (that are `p i ^ ∞`-torsion) to get the result for torsion modules.

Then we get the general result using that a torsion free module is free (which has been proved at
`Module.free_of_finite_type_torsion_free'` at `LinearAlgebra.FreeModule.PID`.)

## Tags

Finitely generated module, principal ideal domain, classification, structure theorem
-/

-- We shouldn't need to know about topology to prove
-- the structure theorem for finitely generated modules over a PID.
assert_not_exists TopologicalSpace

universe u v

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type max u v} [AddCommGroup N] [Module R N]

open scoped DirectSum

open Submodule

open UniqueFactorizationMonoid

theorem Submodule.isSemisimple_torsionBy_of_irreducible {a : R} (h : Irreducible a) :
    IsSemisimpleModule R (torsionBy R M a) :=
  haveI := PrincipalIdealRing.isMaximal_of_irreducible h
  letI := Ideal.Quotient.field (R ∙ a)
  (submodule_torsionBy_orderIso a).complementedLattice

variable [IsDomain R]

/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`. -/
theorem Submodule.isInternal_prime_power_torsion_of_pid [DecidableEq (Ideal R)] [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBy R M
        (IsPrincipal.generator (p : Ideal R) ^
          (factors (⊤ : Submodule R M).annihilator).count ↑p) := by
  convert isInternal_prime_power_torsion hM
  ext p : 1
  rw [← torsionBySet_span_singleton_eq, Ideal.submodule_span_eq, ← Ideal.span_singleton_pow,
    Ideal.span_singleton_generator]

/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`. -/
@[target]
theorem Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i)
        (e : ι → ℕ), DirectSum.IsInternal fun i => torsionBy R M <| p i ^ e i := by sorry

namespace Module

section PTorsion

variable {p : R} (hp : Irreducible p) (hM : Module.IsTorsion' M (Submonoid.powers p))
variable [dec : ∀ x : M, Decidable (x = 0)]

open Ideal Submodule.IsPrincipal

include hp

@[target]
theorem _root_.Ideal.torsionOf_eq_span_pow_pOrder (x : M) :
    torsionOf R M x = span {p ^ pOrder hM x} := by sorry

@[target]
theorem p_pow_smul_lift {x y : M} {k : ℕ} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
    (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y := by sorry

open Submodule.Quotient

theorem exists_smul_eq_zero_and_mk_eq {z : M} (hz : Module.IsTorsionBy R M (p ^ pOrder hM z))
    {k : ℕ} (f : (R ⧸ R ∙ p ^ k) →ₗ[R] M ⧸ R ∙ z) :
    ∃ x : M, p ^ k • x = 0 ∧ Submodule.Quotient.mk (p := span R {z}) x = f 1 := by
  have f1 := mk_surjective (R ∙ z) (f 1)
  have : p ^ k • f1.choose ∈ R ∙ z := by
    rw [← Quotient.mk_eq_zero, mk_smul, f1.choose_spec, ← f.map_smul]
    convert f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul, Quotient.mk_eq_zero, Algebra.id.smul_eq_mul, mul_one]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := p_pow_smul_lift hp hM hz this
  refine ⟨f1.choose - a • z, by rw [smul_sub, sub_eq_zero, ha], ?_⟩
  rw [mk_sub, mk_smul, (Quotient.mk_eq_zero _).mpr <| Submodule.mem_span_singleton_self _,
    smul_zero, sub_zero, f1.choose_spec]

open Finset Multiset

/-- A finitely generated `p ^ ∞`-torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p ^ e i)` for some `e i`. -/
@[target]
theorem torsion_by_prime_power_decomposition (hN : Module.IsTorsion' N (Submonoid.powers p))
    [h' : Module.Finite R N] :
    ∃ (d : ℕ) (k : Fin d → ℕ), Nonempty <| N ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ (k i : ℕ) := by sorry

end PTorsion

/-- A finitely generated torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers. -/
theorem equiv_directSum_of_isTorsion [h' : Module.Finite R N] (hN : Module.IsTorsion R N) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| N ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hN
  haveI := fI
  have :
    ∀ i,
      ∃ (d : ℕ) (k : Fin d → ℕ),
        Nonempty <| torsionBy R N (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j := by
    haveI := fun i => isNoetherian_submodule' (torsionBy R N <| p i ^ e i)
    exact fun i =>
      torsion_by_prime_power_decomposition.{u, v} (hp i)
        ((isTorsion'_powers_iff <| p i).mpr fun x => ⟨e i, smul_torsionBy _ _⟩)
  classical
  refine
    ⟨Σ i, Fin (this i).choose, inferInstance, fun ⟨i, _⟩ => p i, fun ⟨i, _⟩ => hp i, fun ⟨i, j⟩ =>
      (this i).choose_spec.choose j,
      ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h).symm.trans <|
          (DFinsupp.mapRange.linearEquiv fun i => (this i).choose_spec.choose_spec.some).trans <|
            (DirectSum.sigmaLcurryEquiv R).symm.trans
              (DFinsupp.mapRange.linearEquiv fun i => quotEquivOfEq _ _ ?_)⟩⟩
  obtain ⟨i, j⟩ := i
  simp only

/-- **Structure theorem of finitely generated modules over a PID** : A finitely generated
  module over a PID is isomorphic to the product of a free module and a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers. -/
theorem equiv_free_prod_directSum [h' : Module.Finite R N] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| N ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  haveI := isNoetherian_submodule' (torsion R N)
  haveI := Module.Finite.of_surjective _ (torsion R N).mkQ_surjective
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R N _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ (N ⧸ torsion R N) _ _ _ _ _ _
  haveI : Module.Projective R (N ⧸ torsion R N) := Module.Projective.of_basis ⟨g⟩
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R N).mkQ_surjective
  refine
    ⟨n, I, fI, p, hp, e,
      ⟨(lequivProdOfRightSplitExact (torsion R N).injective_subtype ?_ hf).symm.trans <|
          (h.prod g).trans <| LinearEquiv.prodComm.{u, u} R _ (Fin n →₀ R) ⟩⟩
  rw [range_subtype, ker_mkQ]

end Module
