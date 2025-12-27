import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monomial

/-!
# Theory of univariate polynomials

We show that `A[X]` is an R-algebra when `A` is an R-algebra.
We promote `eval₂` to an algebra hom in `aeval`.
-/

assert_not_exists Ideal

noncomputable section

open Finset

open Polynomial

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

section CommSemiring

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable {p q r : R[X]}

/-- Note that this instance also provides `Algebra R R[X]`. -/
instance algebraOfAlgebra : Algebra R A[X] where
  smul_def' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]
      exact Algebra.smul_def' _ _
  commutes' r p :=
    toFinsupp_injective <| by
      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]
      simp_rw [toFinsupp_mul, toFinsupp_C]
      convert Algebra.commutes' r p.toFinsupp
  algebraMap := C.comp (algebraMap R A)

@[simp]
theorem algebraMap_apply (r : R) : algebraMap R A[X] r = C (algebraMap R A r) :=
  rfl

@[target, simp]
theorem toFinsupp_algebraMap (r : R) : (algebraMap R A[X] r).toFinsupp = algebraMap R _ r :=
  sorry

theorem ofFinsupp_algebraMap (r : R) : (⟨algebraMap R _ r⟩ : A[X]) = algebraMap R A[X] r :=
  toFinsupp_injective (toFinsupp_algebraMap _).symm

/-- When we have `[CommSemiring R]`, the function `C` is the same as `algebraMap R R[X]`.

(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebraMap` is not available.)
-/
@[target]
theorem C_eq_algebraMap (r : R) : C r = algebraMap R R[X] r :=
  sorry

@[target, simp]
theorem algebraMap_eq : algebraMap R R[X] = C :=
  sorry
@[simps! apply]
def CAlgHom : A →ₐ[R] A[X] where
  toRingHom := C
  commutes' _ := rfl

/-- Extensionality lemma for algebra maps out of `A'[X]` over a smaller base ring than `A'`
-/
@[ext 1100]
theorem algHom_ext' {f g : A[X] →ₐ[R] B}
    (hC : f.comp CAlgHom = g.comp CAlgHom)
    (hX : f X = g X) : f = g :=
  AlgHom.coe_ringHom_injective (ringHom_ext' (congr_arg AlgHom.toRingHom hC) hX)

variable (R) in
open AddMonoidAlgebra in
/-- Algebra isomorphism between `R[X]` and `R[ℕ]`. This is just an
implementation detail, but it can be useful to transfer results from `Finsupp` to polynomials. -/
@[simps!]
def toFinsuppIsoAlg : R[X] ≃ₐ[R] R[ℕ] :=
  { toFinsuppIso R with
    commutes' := fun r => by
      dsimp }

instance subalgebraNontrivial [Nontrivial A] : Nontrivial (Subalgebra R A[X]) :=
  ⟨⟨⊥, ⊤, by
      rw [Ne, SetLike.ext_iff, not_forall]
      refine ⟨X, ?_⟩
      simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_true, Algebra.mem_top,
        algebraMap_apply, not_forall]
      intro x
      rw [ext_iff, not_forall]
      refine ⟨1, ?_⟩
      simp [coeff_C]⟩⟩

@[target, simp]
theorem algHom_eval₂_algebraMap {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (p : R[X]) (f : A →ₐ[R] B) (a : A) :
    f (eval₂ (algebraMap R A) a p) = eval₂ (algebraMap R B) (f a) p := by sorry

@[simp]
theorem eval₂_algebraMap_X {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] (p : R[X])
    (f : R[X] →ₐ[R] A) : eval₂ (algebraMap R A) (f X) p = f p := by
  conv_rhs => rw [← Polynomial.sum_C_mul_X_pow_eq p]
  simp only [eval₂_eq_sum, sum_def]
  simp only [map_sum, map_mul, map_pow, eq_intCast, map_intCast]
  simp [Polynomial.C_eq_algebraMap]

-- these used to be about `algebraMap ℤ R`, but now the simp-normal form is `Int.castRingHom R`.
@[target, simp]
theorem ringHom_eval₂_intCastRingHom {R S : Type*} [Ring R] [Ring S] (p : ℤ[X]) (f : R →+* S)
    (r : R) : f (eval₂ (Int.castRingHom R) r p) = eval₂ (Int.castRingHom S) (f r) p :=
  sorry

@[target, simp]
theorem eval₂_intCastRingHom_X {R : Type*} [Ring R] (p : ℤ[X]) (f : ℤ[X] →+* R) :
    eval₂ (Int.castRingHom R) (f X) p = f p :=
  sorry
@[simps!]
def eval₂AlgHom' (f : A →ₐ[R] B) (b : B) (hf : ∀ a, Commute (f a) b) : A[X] →ₐ[R] B where
  toRingHom := eval₂RingHom' f b hf
  commutes' _ := (eval₂_C _ _).trans (f.commutes _)

section Map

/-- `Polynomial.map` as an `AlgHom` for noncommutative algebras.

  This is the algebra version of `Polynomial.mapRingHom`. -/
def mapAlgHom (f : A →ₐ[R] B) : Polynomial A →ₐ[R] Polynomial B where
  toRingHom := mapRingHom f.toRingHom
  commutes' := by simp

@[target, simp]
theorem coe_mapAlgHom (f : A →ₐ[R] B) : ⇑(mapAlgHom f) = map f :=
  sorry

@[target, simp]
theorem mapAlgHom_id : mapAlgHom (AlgHom.id R A) = AlgHom.id R (Polynomial A) :=
  sorry

@[simp]
theorem mapAlgHom_coe_ringHom (f : A →ₐ[R] B) :
    ↑(mapAlgHom f : _ →ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[target, simp]
theorem mapAlgHom_comp (C : Type z) [Semiring C] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (mapAlgHom f).comp (mapAlgHom g) = mapAlgHom (f.comp g) := by sorry

theorem mapAlgHom_eq_eval₂AlgHom'_CAlgHom (f : A →ₐ[R] B) : mapAlgHom f = eval₂AlgHom'
    (CAlgHom.comp f) X (fun a => (commute_X (C (f a))).symm) := by
  apply AlgHom.ext
  intro x
  congr

/-- If `A` and `B` are isomorphic as `R`-algebras, then so are their polynomial rings -/
def mapAlgEquiv (f : A ≃ₐ[R] B) : Polynomial A ≃ₐ[R] Polynomial B :=
  AlgEquiv.ofAlgHom (mapAlgHom f.toAlgHom) (mapAlgHom f.symm.toAlgHom) (by simp) (by simp)

@[target, simp]
theorem coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEquiv f) = map f :=
  sorry

@[target, simp]
theorem mapAlgEquiv_id : mapAlgEquiv (@AlgEquiv.refl R A _ _ _) = AlgEquiv.refl :=
  sorry

@[simp]
theorem mapAlgEquiv_coe_ringHom (f : A ≃ₐ[R] B) :
    ↑(mapAlgEquiv f : _ ≃ₐ[R] Polynomial B) = (mapRingHom ↑f : Polynomial A →+* Polynomial B) :=
  rfl

@[simp]
theorem mapAlgEquiv_comp (C : Type z) [Semiring C] [Algebra R C] (f : A ≃ₐ[R] B) (g : B ≃ₐ[R] C) :
    (mapAlgEquiv f).trans (mapAlgEquiv g) = mapAlgEquiv (f.trans g) := by
  apply AlgEquiv.ext
  intro x
  simp [AlgEquiv.trans_apply, map_map]
  congr

end Map

end CommSemiring

section aeval

variable [CommSemiring R] [Semiring A] [CommSemiring A'] [Semiring B]
variable [Algebra R A] [Algebra R B]
variable {p q : R[X]} (x : A)

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
  eval₂AlgHom' (Algebra.ofId _ _) x (Algebra.commutes · _)

@[target, ext 1200]
theorem algHom_ext {f g : R[X] →ₐ[R] B} (hX : f X = g X) :
    f = g :=
  sorry

@[target]
theorem aeval_def (p : R[X]) : aeval x p = eval₂ (algebraMap R A) x p :=
  sorry

@[target]
theorem aeval_zero : aeval x (0 : R[X]) = 0 :=
  sorry

@[simp]
theorem aeval_X : aeval x (X : R[X]) = x :=
  eval₂_X _ x

@[target, simp]
theorem aeval_C (r : R) : aeval x (C r) = algebraMap R A r :=
  sorry

@[target, simp]
theorem aeval_monomial {n : ℕ} {r : R} : aeval x (monomial n r) = algebraMap _ _ r * x ^ n :=
  sorry

theorem aeval_X_pow {n : ℕ} : aeval x ((X : R[X]) ^ n) = x ^ n :=
  eval₂_X_pow _ _

@[target]
theorem aeval_add : aeval x (p + q) = aeval x p + aeval x q :=
  sorry

@[target]
theorem aeval_one : aeval x (1 : R[X]) = 1 :=
  sorry

@[target]
theorem aeval_natCast (n : ℕ) : aeval x (n : R[X]) = n :=
  sorry

theorem aeval_mul : aeval x (p * q) = aeval x p * aeval x q :=
  map_mul _ _ _

theorem comp_eq_aeval : p.comp q = aeval q p := rfl

@[target]
theorem aeval_comp {A : Type*} [Semiring A] [Algebra R A] (x : A) :
    aeval x (p.comp q) = aeval (aeval x q) p :=
  sorry
@[simps!]
def algEquivOfCompEqX (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) : R[X] ≃ₐ[R] R[X] := by
  refine AlgEquiv.ofAlgHom (aeval p) (aeval q) ?_ ?_ <;>
    exact AlgHom.ext fun _ ↦ by simp [← comp_eq_aeval, comp_assoc, hpq, hqp]

@[target, simp]
theorem algEquivOfCompEqX_eq_iff (p q p' q' : R[X])
    (hpq : p.comp q = X) (hqp : q.comp p = X) (hpq' : p'.comp q' = X) (hqp' : q'.comp p' = X) :
    algEquivOfCompEqX p q hpq hqp = algEquivOfCompEqX p' q' hpq' hqp' ↔ p = p' :=
  sorry

@[target, simp]
theorem algEquivOfCompEqX_symm (p q : R[X]) (hpq : p.comp q = X) (hqp : q.comp p = X) :
    (algEquivOfCompEqX p q hpq hqp).symm = algEquivOfCompEqX q p hqp hpq := sorry
@[simps!]
def algEquivCMulXAddC {R : Type*} [CommRing R] (a b : R) [Invertible a] : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (C a * X + C b) (C ⅟ a * (X - C b))
    (by simp [← C_mul, ← mul_assoc]) (by simp [← C_mul, ← mul_assoc])

@[target]
theorem algEquivCMulXAddC_symm_eq {R : Type*} [CommRing R] (a b : R) [Invertible a] :
    (algEquivCMulXAddC a b).symm =  algEquivCMulXAddC (⅟ a) (- ⅟ a * b) := by sorry
@[simps!]
def algEquivAevalXAddC {R : Type*} [CommRing R] (t : R) : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (X + C t) (X - C t) (by simp) (by simp)

@[target, simp]
theorem algEquivAevalXAddC_eq_iff {R : Type*} [CommRing R] (t t' : R) :
    algEquivAevalXAddC t = algEquivAevalXAddC t' ↔ t = t' := by sorry

@[target, simp]
theorem algEquivAevalXAddC_symm {R : Type*} [CommRing R] (t : R) :
    (algEquivAevalXAddC t).symm = algEquivAevalXAddC (-t) := by sorry
@[simps!]
def algEquivAevalNegX {R : Type*} [CommRing R] : R[X] ≃ₐ[R] R[X] :=
  algEquivOfCompEqX (-X) (-X) (by simp) (by simp)

@[target]
theorem comp_neg_X_comp_neg_X {R : Type*} [CommRing R] (p : R[X]) :
    (p.comp (-X)).comp (-X) = p := by sorry

theorem aeval_algHom (f : A →ₐ[R] B) (x : A) : aeval (f x) = f.comp (aeval x) :=
  algHom_ext <| by simp only [aeval_X, AlgHom.comp_apply]

@[target, simp]
theorem aeval_X_left : aeval (X : R[X]) = AlgHom.id R R[X] :=
  sorry

theorem aeval_X_left_apply (p : R[X]) : aeval X p = p :=
  AlgHom.congr_fun (@aeval_X_left R _) p

@[target]
theorem eval_unique (φ : R[X] →ₐ[R] A) (p) : φ p = eval₂ (algebraMap R A) (φ X) p := by sorry

theorem aeval_algHom_apply {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (x : A) (p : R[X]) :
    aeval (f x) p = f (aeval x p) := by
  refine Polynomial.induction_on p (by simp [AlgHomClass.commutes]) (fun p q hp hq => ?_)
    (by simp [AlgHomClass.commutes])
  rw [map_add, hp, hq, ← map_add, ← map_add]

@[target, simp]
lemma coe_aeval_mk_apply {S : Subalgebra R A} (h : x ∈ S) :
    (aeval (⟨x, h⟩ : S) p : A) = aeval x p :=
  sorry

@[target]
theorem aeval_algEquiv (f : A ≃ₐ[R] B) (x : A) : aeval (f x) = (f : A →ₐ[R] B).comp (aeval x) :=
  sorry

theorem aeval_algebraMap_apply_eq_algebraMap_eval (x : R) (p : R[X]) :
    aeval (algebraMap R A x) p = algebraMap R A (p.eval x) :=
  aeval_algHom_apply (Algebra.ofId R A) x p

/-- Polynomial evaluation on a pair is a product of the evaluations on the components. -/
@[target]
theorem aeval_prod (x : A × B) : aeval (R := sorry
theorem aeval_prod_apply (x : A × B) (p : Polynomial R) :
    p.aeval x = (p.aeval x.1, p.aeval x.2) := by simp [aeval_prod]

section Pi

variable {I : Type*} {A : I → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]
variable (x : Π i, A i) (p : R[X])

/-- Polynomial evaluation on an indexed tuple is the indexed product of the evaluations
on the components.
Generalizes `Polynomial.aeval_prod` to indexed products. -/
@[target]
theorem aeval_pi (x : Π i, A i) : aeval (R := sorry

theorem aeval_pi_apply₂ (j : I) : p.aeval x j = p.aeval (x j) :=
  aeval_pi (R := R) x ▸ Pi.algHom_apply R A (fun i ↦ aeval (x i)) p j

/-- Polynomial evaluation on an indexed tuple is the indexed tuple of the evaluations
on the components.
Generalizes `Polynomial.aeval_prod_apply` to indexed products. -/
@[target]
theorem aeval_pi_apply : p.aeval x = fun j ↦ p.aeval (x j) :=
  sorry

end Pi

@[target, simp]
theorem coe_aeval_eq_eval (r : R) : (aeval r : R[X] → R) = eval r :=
  sorry

@[simp]
theorem coe_aeval_eq_evalRingHom (x : R) :
    ((aeval x : R[X] →ₐ[R] R) : R[X] →+* R) = evalRingHom x :=
  rfl

@[target, simp]
theorem aeval_fn_apply {X : Type*} (g : R[X]) (f : X → R) (x : X) :
    ((aeval f) g) x = aeval (f x) g :=
  sorry

@[target, norm_cast]
theorem aeval_subalgebra_coe (g : R[X]) {A : Type*} [Semiring A] [Algebra R A] (s : Subalgebra R A)
    (f : s) : (aeval f g : A) = aeval (f : A) g :=
  sorry

theorem coeff_zero_eq_aeval_zero (p : R[X]) : p.coeff 0 = aeval 0 p := by
  simp [coeff_zero_eq_eval_zero]

@[target]
theorem coeff_zero_eq_aeval_zero' (p : R[X]) : algebraMap R A (p.coeff 0) = aeval (0 : A) p := by sorry

theorem map_aeval_eq_aeval_map {S T U : Type*} [Semiring S] [CommSemiring T] [Semiring U]
    [Algebra R S] [Algebra T U] {φ : R →+* T} {ψ : S →+* U}
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) (p : R[X]) (a : S) :
    ψ (aeval a p) = aeval (ψ a) (p.map φ) := by
  conv_rhs => rw [aeval_def, ← eval_map]
  rw [map_map, h, ← map_map, eval_map, eval₂_at_apply, aeval_def, eval_map]

@[target]
theorem aeval_eq_zero_of_dvd_aeval_eq_zero [CommSemiring S] [CommSemiring T] [Algebra S T]
    {p q : S[X]} (h₁ : p ∣ q) {a : T} (h₂ : aeval a p = 0) : aeval a q = 0 := by sorry

section Semiring

variable [Semiring S] {f : R →+* S}

theorem aeval_eq_sum_range [Algebra R S] {p : R[X]} (x : S) :
    aeval x p = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range (algebraMap R S) x

theorem aeval_eq_sum_range' [Algebra R S] {p : R[X]} {n : ℕ} (hn : p.natDegree < n) (x : S) :
    aeval x p = ∑ i ∈ Finset.range n, p.coeff i • x ^ i := by
  simp_rw [Algebra.smul_def]
  exact eval₂_eq_sum_range' (algebraMap R S) hn x

@[target]
theorem isRoot_of_eval₂_map_eq_zero (hf : Function.Injective f) {r : R} :
    eval₂ f (f r) p = 0 → p.IsRoot r := by sorry

@[target]
theorem isRoot_of_aeval_algebraMap_eq_zero [Algebra R S] {p : R[X]}
    (inj : Function.Injective (algebraMap R S)) {r : R} (hr : aeval (algebraMap R S r) p = 0) :
    p.IsRoot r :=
  sorry

end Semiring

section CommSemiring

section aevalTower

variable [CommSemiring S] [Algebra S R] [Algebra S A'] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `R[X]` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A') (x : A') : R[X] →ₐ[S] A' :=
  eval₂AlgHom' f x fun _ => Commute.all _ _

variable (g : R →ₐ[S] A') (y : A')

@[simp]
theorem aevalTower_X : aevalTower g y X = y :=
  eval₂_X _ _

@[target, simp]
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  sorry

@[simp]
theorem aevalTower_comp_C : (aevalTower g y : R[X] →+* A').comp C = g :=
  RingHom.ext <| aevalTower_C _ _

theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R R[X] x) = g x :=
  eval₂_C _ _

@[target]
theorem aevalTower_comp_algebraMap : (aevalTower g y : R[X] →+* A').comp (algebraMap R R[X]) = g :=
  sorry

@[target]
theorem aevalTower_toAlgHom (x : R) : aevalTower g y (IsScalarTower.toAlgHom S R R[X] x) = g x :=
  sorry

@[target, simp]
theorem aevalTower_comp_toAlgHom : (aevalTower g y).comp (IsScalarTower.toAlgHom S R R[X]) = g :=
  sorry

@[target, simp]
theorem aevalTower_id : aevalTower (AlgHom.id S S) = aeval := by sorry

@[target, simp]
theorem aevalTower_ofId : aevalTower (Algebra.ofId S A') = aeval := by sorry

end aevalTower

end CommSemiring

section CommRing

variable [CommRing S] {f : R →+* S}

@[target]
theorem dvd_term_of_dvd_eval_of_dvd_terms {z p : S} {f : S[X]} (i : ℕ) (dvd_eval : p ∣ f.eval z)
    (dvd_terms : ∀ j ≠ i, p ∣ f.coeff j * z ^ j) : p ∣ f.coeff i * z ^ i := by sorry

@[target]
theorem dvd_term_of_isRoot_of_dvd_terms {r p : S} {f : S[X]} (i : ℕ) (hr : f.IsRoot r)
    (h : ∀ j ≠ i, p ∣ f.coeff j * r ^ j) : p ∣ f.coeff i * r ^ i :=
  sorry

end CommRing

end aeval

section Ring

variable [Ring R]

/-- The evaluation map is not generally multiplicative when the coefficient ring is noncommutative,
but nevertheless any polynomial of the form `p * (X - monomial 0 r)` is sent to zero
when evaluated at `r`.

This is the key step in our proof of the Cayley-Hamilton theorem.
-/
@[target]
theorem eval_mul_X_sub_C {p : R[X]} (r : R) : (p * (X - C r)).eval r = 0 := by sorry

@[target]
theorem not_isUnit_X_sub_C [Nontrivial R] (r : R) : ¬IsUnit (X - C r) :=
  sorry

end Ring

section CommRing
variable [CommRing R] {p : R[X]} {t : R}

theorem aeval_endomorphism {M : Type*} [AddCommGroup M] [Module R M] (f : M →ₗ[R] M)
    (v : M) (p : R[X]) : aeval f p v = p.sum fun n b => b • (f ^ n) v := by
  rw [aeval_def, eval₂_eq_sum]
  exact map_sum (LinearMap.applyₗ v) _ _

lemma X_sub_C_pow_dvd_iff {n : ℕ} : (X - C t) ^ n ∣ p ↔ X ^ n ∣ p.comp (X + C t) := by
  convert (map_dvd_iff <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

lemma comp_X_add_C_eq_zero_iff : p.comp (X + C t) = 0 ↔ p = 0 :=
  EmbeddingLike.map_eq_zero_iff (f := algEquivAevalXAddC t)

lemma comp_X_add_C_ne_zero_iff : p.comp (X + C t) ≠ 0 ↔ p ≠ 0 := comp_X_add_C_eq_zero_iff.not

@[target]
lemma dvd_comp_C_mul_X_add_C_iff (p q : R[X]) (a b : R) [Invertible a] :
    p ∣ q.comp (C a * X + C b) ↔ p.comp (C ⅟ a * (X - C b)) ∣ q := by sorry

lemma dvd_comp_X_sub_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (X - C a) ↔ p.comp (X + C a) ∣ q := by
  let _ := invertibleOne (α := R)
  simpa using dvd_comp_C_mul_X_add_C_iff p q 1 (-a)

@[target]
lemma dvd_comp_X_add_C_iff (p q : R[X]) (a : R) :
    p ∣ q.comp (X + C a) ↔ p.comp (X - C a) ∣ q := by sorry

@[target]
lemma dvd_comp_neg_X_iff (p q : R[X]) : p ∣ q.comp (-X) ↔ p.comp (-X) ∣ q := by sorry

variable [IsDomain R]

lemma units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

end CommRing

section StableSubmodule

variable {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {q : Submodule R M} {m : M}

lemma aeval_apply_smul_mem_of_le_comap'
    [Semiring A] [Algebra R A] [Module A M] [IsScalarTower R A M] (hm : m ∈ q) (p : R[X]) (a : A)
    (hq : q ≤ q.comap (Algebra.lsmul R R M a)) :
    aeval a p • m ∈ q := by
  refine p.induction_on (M := fun f ↦ aeval a f • m ∈ q) (by simpa) (fun f₁ f₂ h₁ h₂ ↦ ?_)
    (fun n t hmq ↦ ?_)
  · simp_rw [map_add, add_smul]
    exact Submodule.add_mem q h₁ h₂
  · dsimp only at hmq ⊢
    rw [pow_succ', mul_left_comm, map_mul, aeval_X, mul_smul]
    rw [← q.map_le_iff_le_comap] at hq
    exact hq ⟨_, hmq, rfl⟩

@[target]
lemma aeval_apply_smul_mem_of_le_comap
    (hm : m ∈ q) (p : R[X]) (f : Module.End R M) (hq : q ≤ q.comap f) :
    aeval f p m ∈ q :=
  sorry

end StableSubmodule

section CommSemiring

variable [CommSemiring R] {a p : R[X]}

theorem eq_zero_of_mul_eq_zero_of_smul (P : R[X]) (h : ∀ r : R, r • P = 0 → r = 0) (Q : R[X])
    (hQ : P * Q = 0) : Q = 0 := by
  suffices ∀ i, P.coeff i • Q = 0 by
    rw [← leadingCoeff_eq_zero]
    apply h
    simpa [ext_iff, mul_comm Q.leadingCoeff] using fun i ↦ congr_arg (·.coeff Q.natDegree) (this i)
  apply Nat.strong_decreasing_induction
  · use P.natDegree
    intro i hi
    rw [coeff_eq_zero_of_natDegree_lt hi, zero_smul]
  intro l IH
  obtain _|hl := (natDegree_smul_le (P.coeff l) Q).lt_or_eq
  · apply eq_zero_of_mul_eq_zero_of_smul _ h (P.coeff l • Q)
    rw [smul_eq_C_mul, mul_left_comm, hQ, mul_zero]
  suffices P.coeff l * Q.leadingCoeff = 0 by
    rwa [← leadingCoeff_eq_zero, ← coeff_natDegree, coeff_smul, hl, coeff_natDegree, smul_eq_mul]
  let m := Q.natDegree
  suffices (P * Q).coeff (l + m) = P.coeff l * Q.leadingCoeff by rw [← this, hQ, coeff_zero]
  rw [coeff_mul]
  apply Finset.sum_eq_single (l, m) _ (by simp)
  simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
  intro i j hij H
  obtain hi|rfl|hi := lt_trichotomy i l
  · have hj : m < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt hj, mul_zero]
  · omega
  · rw [← coeff_C_mul, ← smul_eq_C_mul, IH _ hi, coeff_zero]
termination_by Q.natDegree

open nonZeroDivisors in
/-- *McCoy theorem*: a polynomial `P : R[X]` is a zerodivisor if and only if there is `a : R`
such that `a ≠ 0` and `a • P = 0`. -/
theorem nmem_nonZeroDivisors_iff {P : R[X]} : P ∉ R[X]⁰ ↔ ∃ a : R, a ≠ 0 ∧ a • P = 0 := by
  refine ⟨fun hP ↦ ?_, fun ⟨a, ha, h⟩ h1 ↦ ha <| C_eq_zero.1 <| (h1 _) <| smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := _root_.nmem_nonZeroDivisors_iff.1 hP
  refine hQ.2 (eq_zero_of_mul_eq_zero_of_smul P (fun a ha ↦ ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha

open nonZeroDivisors in
protected lemma mem_nonZeroDivisors_iff {P : R[X]} : P ∈ R[X]⁰ ↔ ∀ a : R, a • P = 0 → a = 0 := by
  simpa [not_imp_not] using (nmem_nonZeroDivisors_iff (P := P)).not

end CommSemiring

end Polynomial
