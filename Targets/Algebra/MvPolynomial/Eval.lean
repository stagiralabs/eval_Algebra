import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Multivariate polynomials

This file defines functions for evaluating multivariate polynomials.
These include generically evaluating a polynomial given a valuation of all its variables,
and more advanced evaluations that allow one to map the coefficients to different rings.

### Notation

In the definitions below, we use the following notation:

+ `σ : Type*` (indexing the variables)
+ `R : Type*` `[CommSemiring R]` (the coefficients)
+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
  This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`
+ `a : R`
+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians
+ `p : MvPolynomial σ R`

### Definitions

* `eval₂ (f : R → S₁) (g : σ → S₁) p` : given a semiring homomorphism from `R` to another
  semiring `S₁`, and a map `σ → S₁`, evaluates `p` at this valuation, returning a term of type `S₁`.
  Note that `eval₂` can be made using `eval` and `map` (see below), and it has been suggested
  that sticking to `eval` and `map` might make the code less brittle.
* `eval (g : σ → R) p` : given a map `σ → R`, evaluates `p` at this valuation,
  returning a term of type `R`
* `map (f : R → S₁) p` : returns the multivariate polynomial obtained from `p` by the change of
  coefficient semiring corresponding to `f`
* `aeval (g : σ → S₁) p` : evaluates the multivariate polynomial obtained from `p` by the change
  of coefficient semiring corresponding to `g` (`a` stands for `Algebra`)

-/

noncomputable section

open Set Function Finsupp AddMonoidAlgebra
open scoped Pointwise

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

section Eval₂

variable (f : R →+* S₁) (g : σ → S₁)

/-- Evaluate a polynomial `p` given a valuation `g` of all the variables
  and a ring hom `f` from the scalar ring to the target -/
def eval₂ (p : MvPolynomial σ R) : S₁ :=
  p.sum fun s a => f a * s.prod fun n e => g n ^ e

theorem eval₂_eq (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i ∈ d.support, X i ^ d i :=
  rfl

@[target]
theorem eval₂_eq' [Fintype σ] (g : R →+* S₁) (X : σ → S₁) (f : MvPolynomial σ R) :
    f.eval₂ g X = ∑ d ∈ f.support, g (f.coeff d) * ∏ i, X i ^ d i := by sorry

@[simp]
theorem eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g = 0 :=
  Finsupp.sum_zero_index

section

@[target, simp]
theorem eval₂_add : (p + q).eval₂ f g = p.eval₂ f g + q.eval₂ f g := by sorry

@[target, simp]
theorem eval₂_monomial : (monomial s a).eval₂ f g = f a * s.prod fun n e => g n ^ e :=
  sorry

@[simp]
theorem eval₂_C (a) : (C a).eval₂ f g = f a := by
  rw [C_apply, eval₂_monomial, prod_zero_index, mul_one]

@[simp]
theorem eval₂_one : (1 : MvPolynomial σ R).eval₂ f g = 1 :=
  (eval₂_C _ _ _).trans f.map_one

@[simp] theorem eval₂_natCast (n : Nat) : (n : MvPolynomial σ R).eval₂ f g = n :=
  (eval₂_C _ _ _).trans (map_natCast f n)

@[simp] theorem eval₂_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval₂ f g = ofNat(n) :=
  eval₂_natCast f g n

@[target, simp]
theorem eval₂_X (n) : (X n).eval₂ f g = g n := by sorry

@[target]
theorem eval₂_mul_monomial :
    ∀ {s a}, (p * monomial s a).eval₂ f g = p.eval₂ f g * f a * s.prod fun n e => g n ^ e := by sorry

@[target]
theorem eval₂_mul_C : (p * C a).eval₂ f g = p.eval₂ f g * f a :=
  sorry

@[simp]
theorem eval₂_mul : ∀ {p}, (p * q).eval₂ f g = p.eval₂ f g * q.eval₂ f g := by
  apply MvPolynomial.induction_on q
  · simp [eval₂_C, eval₂_mul_C]
  · simp +contextual [mul_add, eval₂_add]
  · simp +contextual [X, eval₂_monomial, eval₂_mul_monomial, ← mul_assoc]

@[simp]
theorem eval₂_pow {p : MvPolynomial σ R} : ∀ {n : ℕ}, (p ^ n).eval₂ f g = p.eval₂ f g ^ n
  | 0 => by
    rw [pow_zero, pow_zero]
    exact eval₂_one _ _
  | n + 1 => by rw [pow_add, pow_one, pow_add, pow_one, eval₂_mul, eval₂_pow]

/-- `MvPolynomial.eval₂` as a `RingHom`. -/
def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁ where
  toFun := eval₂ f g
  map_one' := eval₂_one _ _
  map_mul' _ _ := eval₂_mul _ _
  map_zero' := eval₂_zero f g
  map_add' _ _ := eval₂_add _ _

@[target, simp]
theorem coe_eval₂Hom (f : R →+* S₁) (g : σ → S₁) : ⇑(eval₂Hom f g) = eval₂ f g :=
  sorry

@[target]
theorem eval₂Hom_congr {f₁ f₂ : R →+* S₁} {g₁ g₂ : σ → S₁} {p₁ p₂ : MvPolynomial σ R} :
    f₁ = f₂ → g₁ = g₂ → p₁ = p₂ → eval₂Hom f₁ g₁ p₁ = eval₂Hom f₂ g₂ p₂ := by sorry

@[target, simp]
theorem eval₂Hom_C (f : R →+* S₁) (g : σ → S₁) (r : R) : eval₂Hom f g (C r) = f r :=
  sorry

@[simp]
theorem eval₂Hom_X' (f : R →+* S₁) (g : σ → S₁) (i : σ) : eval₂Hom f g (X i) = g i :=
  eval₂_X f g i

@[simp]
theorem comp_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂) :
    φ.comp (eval₂Hom f g) = eval₂Hom (φ.comp f) fun i => φ (g i) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, eval₂Hom_C, eval₂Hom_C, RingHom.comp_apply]
  · intro i
    rw [RingHom.comp_apply, eval₂Hom_X', eval₂Hom_X']

@[target]
theorem map_eval₂Hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₁) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : φ (eval₂Hom f g p) = eval₂Hom (φ.comp f) (fun i => φ (g i)) p := by sorry

@[target]
theorem eval₂Hom_monomial (f : R →+* S₁) (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    eval₂Hom f g (monomial d r) = f r * d.prod fun i k => g i ^ k := by sorry

theorem eval₂_comp_left {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p := by
  apply MvPolynomial.induction_on p <;>
    simp +contextual [eval₂_add, k.map_add, eval₂_mul, k.map_mul]

end

@[target, simp]
theorem eval₂_eta (p : MvPolynomial σ R) : eval₂ C X p = p := by sorry

theorem eval₂_congr (g₁ g₂ : σ → S₁)
    (h : ∀ {i : σ} {c : σ →₀ ℕ}, i ∈ c.support → coeff c p ≠ 0 → g₁ i = g₂ i) :
    p.eval₂ f g₁ = p.eval₂ f g₂ := by
  apply Finset.sum_congr rfl
  intro C hc; dsimp; congr 1
  apply Finset.prod_congr rfl
  intro i hi; dsimp; congr 1
  apply h hi
  rwa [Finsupp.mem_support_iff] at hc

@[target]
theorem eval₂_sum (s : Finset S₂) (p : S₂ → MvPolynomial σ R) :
    eval₂ f g (∑ x ∈ s, p x) = ∑ x ∈ s, eval₂ f g (p x) :=
  sorry

@[target, to_additive existing (attr := sorry

@[target]
theorem eval₂_assoc (q : S₂ → MvPolynomial σ R) (p : MvPolynomial S₂ R) :
    eval₂ f (fun t => eval₂ f g (q t)) p = eval₂ f g (eval₂ C q p) := by sorry

end Eval₂

section Eval

variable {f : σ → R}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → R) : MvPolynomial σ R →+* R :=
  eval₂Hom (RingHom.id _) f

theorem eval_eq (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i ∈ d.support, X i ^ d i :=
  rfl

@[target]
theorem eval_eq' [Fintype σ] (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i, X i ^ d i :=
  sorry

theorem eval_monomial : eval f (monomial s a) = a * s.prod fun n e => f n ^ e :=
  eval₂_monomial _ _

@[target, simp]
theorem eval_C : ∀ a, eval f (C a) = a :=
  sorry

@[target, simp]
theorem eval_X : ∀ n, eval f (X n) = f n :=
  sorry

@[simp] theorem eval_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).eval f = ofNat(n) :=
  map_ofNat _ n

@[target, simp]
theorem smul_eval (x) (p : MvPolynomial σ R) (s) : eval x (s • p) = s * eval x p := by sorry

@[target]
theorem eval_add : eval f (p + q) = eval f p + eval f q :=
  sorry

@[target]
theorem eval_mul : eval f (p * q) = eval f p * eval f q :=
  sorry

theorem eval_pow : ∀ n, eval f (p ^ n) = eval f p ^ n :=
  fun _ => eval₂_pow _ _

@[target]
theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∑ i ∈ s, f i) = ∑ i ∈ s, eval g (f i) :=
  sorry

@[target, to_additive existing]
theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∏ i ∈ s, f i) = ∏ i ∈ s, eval g (f i) :=
  sorry

@[target]
theorem eval_assoc {τ} (f : σ → MvPolynomial τ R) (g : τ → R) (p : MvPolynomial σ R) :
    eval (eval g ∘ f) p = eval g (eval₂ C f p) := by sorry

@[target, simp]
theorem eval₂_id {g : σ → R} (p : MvPolynomial σ R) : eval₂ (RingHom.id _) g p = eval g p :=
  sorry

@[target]
theorem eval_eval₂ {S τ : Type*} {x : τ → S} [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S) (p : MvPolynomial σ R) :
    eval x (eval₂ f g p) = eval₂ ((eval x).comp f) (fun s => eval x (g s)) p := by sorry

end Eval

section Map

variable (f : R →+* S₁)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : MvPolynomial σ R →+* MvPolynomial σ S₁ :=
  eval₂Hom (C.comp f) X

@[target, simp]
theorem map_monomial (s : σ →₀ ℕ) (a : R) : map f (monomial s a) = monomial s (f a) :=
  sorry

@[simp]
theorem map_C : ∀ a : R, map f (C a : MvPolynomial σ R) = C (f a) :=
  map_monomial _ _

@[simp] protected theorem map_ofNat (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : MvPolynomial σ R).map f = ofNat(n) :=
  _root_.map_ofNat _ _

@[simp]
theorem map_X : ∀ n : σ, map f (X n : MvPolynomial σ R) = X n :=
  eval₂_X _ _

theorem map_id : ∀ p : MvPolynomial σ R, map (RingHom.id R) p = p :=
  eval₂_eta

theorem map_map [CommSemiring S₂] (g : S₁ →+* S₂) (p : MvPolynomial σ R) :
    map g (map f p) = map (g.comp f) p :=
  (eval₂_comp_left (map g) (C.comp f) X p).trans <| by
    congr
    · ext1 a
      simp only [map_C, comp_apply, RingHom.coe_comp]
    · ext1 n
      simp only [map_X, comp_apply]

@[target]
theorem eval₂_eq_eval_map (g : σ → S₁) (p : MvPolynomial σ R) : p.eval₂ f g = eval g (map f p) := by sorry

theorem eval₂_comp_right {S₂} [CommSemiring S₂] (k : S₁ →+* S₂) (f : R →+* S₁) (g : σ → S₁) (p) :
    k (eval₂ f g p) = eval₂ k (k ∘ g) (map f p) := by
  apply MvPolynomial.induction_on p
  · intro r
    rw [eval₂_C, map_C, eval₂_C]
  · intro p q hp hq
    rw [eval₂_add, k.map_add, (map f).map_add, eval₂_add, hp, hq]
  · intro p s hp
    rw [eval₂_mul, k.map_mul, (map f).map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X]
    rfl

@[target]
theorem map_eval₂ (f : R →+* S₁) (g : S₂ → MvPolynomial S₃ R) (p : MvPolynomial S₂ R) :
    map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) := by sorry

@[target]
theorem coeff_map (p : MvPolynomial σ R) : ∀ m : σ →₀ ℕ, coeff m (map f p) = f (coeff m p) := by sorry

@[target]
theorem map_injective (hf : Function.Injective f) :
    Function.Injective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := by sorry

@[target]
theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (map f : MvPolynomial σ R → MvPolynomial σ S₁) := sorry
theorem map_leftInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) := fun X => by
  rw [map_map, (RingHom.ext hf : f.comp g = RingHom.id _), map_id]

/-- If `f` is a right-inverse of `g` then `map f` is a right-inverse of `map g`. -/
theorem map_rightInverse {f : R →+* S₁} {g : S₁ →+* R} (hf : Function.RightInverse f g) :
    Function.RightInverse (map f : MvPolynomial σ R → MvPolynomial σ S₁) (map g) :=
  (map_leftInverse hf.leftInverse).rightInverse

@[target, simp]
theorem eval_map (f : R →+* S₁) (g : σ → S₁) (p : MvPolynomial σ R) :
    eval g (map f p) = eval₂ f g p := by sorry

@[target]
theorem eval₂_comp (f : R →+* S₁) (g : σ → R) (p : MvPolynomial σ R) :
    f (eval g p) = eval₂ f (f ∘ g) p := by sorry

@[target, simp]
theorem eval₂_map [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : eval₂ φ g (map f p) = eval₂ (φ.comp f) g p := by sorry

@[simp]
theorem eval₂Hom_map_hom [CommSemiring S₂] (f : R →+* S₁) (g : σ → S₂) (φ : S₁ →+* S₂)
    (p : MvPolynomial σ R) : eval₂Hom φ g (map f p) = eval₂Hom (φ.comp f) g p :=
  eval₂_map f g φ p

@[target, simp]
theorem constantCoeff_map (f : R →+* S₁) (φ : MvPolynomial σ R) :
    constantCoeff (MvPolynomial.map f φ) = f (constantCoeff φ) :=
  sorry

theorem constantCoeff_comp_map (f : R →+* S₁) :
    (constantCoeff : MvPolynomial σ S₁ →+* S₁).comp (MvPolynomial.map f) = f.comp constantCoeff :=
  by ext <;> simp

theorem support_map_subset (p : MvPolynomial σ R) : (map f p).support ⊆ p.support := by
  intro x
  simp only [mem_support_iff]
  contrapose!
  change p.coeff x = 0 → (map f p).coeff x = 0
  rw [coeff_map]
  intro hx
  rw [hx]
  exact RingHom.map_zero f

@[target]
theorem support_map_of_injective (p : MvPolynomial σ R) {f : R →+* S₁} (hf : Injective f) :
    (map f p).support = p.support := by sorry

@[target]
theorem C_dvd_iff_map_hom_eq_zero (q : R →+* S₁) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
    (φ : MvPolynomial σ R) : C r ∣ φ ↔ map q φ = 0 := by sorry

@[target]
theorem map_mapRange_eq_iff (f : R →+* S₁) (g : S₁ → R) (hg : g 0 = 0) (φ : MvPolynomial σ S₁) :
    map f (Finsupp.mapRange g hg φ) = φ ↔ ∀ d, f (g (coeff d φ)) = coeff d φ := by sorry
@[simps!]
def mapAlgHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    MvPolynomial σ S₁ →ₐ[R] MvPolynomial σ S₂ :=
  { map (↑f : S₁ →+* S₂) with
    commutes' := fun r => by
      have h₁ : algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) := rfl
      have h₂ : algebraMap R (MvPolynomial σ S₂) r = C (algebraMap R S₂ r) := rfl
      simp_rw [OneHom.toFun_eq_coe]
      -- Porting note: we're missing some `simp` lemmas like `MonoidHom.coe_toOneHom`
      change @DFunLike.coe (_ →+* _) _ _ _ _ _ = _
      rw [h₁, h₂, map, eval₂Hom_C, RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.commutes] }

@[target, simp]
theorem mapAlgHom_id [Algebra R S₁] :
    mapAlgHom (AlgHom.id R S₁) = AlgHom.id R (MvPolynomial σ S₁) :=
  sorry

@[target, simp]
theorem mapAlgHom_coe_ringHom [CommSemiring S₂] [Algebra R S₁] [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    ↑(mapAlgHom f : _ →ₐ[R] MvPolynomial σ S₂) =
      (map ↑f : MvPolynomial σ S₁ →+* MvPolynomial σ S₂) :=
  sorry

end Map

section Aeval

/-! ### The algebra of multivariate polynomials -/


variable [Algebra R S₁] [CommSemiring S₂]
variable (f : σ → S₁)

@[target, simp]
theorem algebraMap_apply (r : R) : algebraMap R (MvPolynomial σ S₁) r = C (algebraMap R S₁ r) := sorry
def aeval : MvPolynomial σ R →ₐ[R] S₁ :=
  { eval₂Hom (algebraMap R S₁) f with commutes' := fun _r => eval₂_C _ _ _ }

@[target]
theorem aeval_def (p : MvPolynomial σ R) : aeval f p = eval₂ (algebraMap R S₁) f p :=
  sorry

theorem aeval_eq_eval₂Hom (p : MvPolynomial σ R) : aeval f p = eval₂Hom (algebraMap R S₁) f p :=
  rfl

@[target, simp]
lemma coe_aeval_eq_eval : RingHomClass.toRingHom (MvPolynomial.aeval f) = MvPolynomial.eval f :=
  sorry

@[target, simp]
theorem aeval_X (s : σ) : aeval f (X s : MvPolynomial _ R) = f s :=
  sorry

@[target]
theorem aeval_C (r : R) : aeval f (C r) = algebraMap R S₁ r :=
  sorry

@[simp] theorem aeval_ofNat (n : Nat) [n.AtLeastTwo] :
    aeval f (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  map_ofNat _ _

@[target]
theorem aeval_unique (φ : MvPolynomial σ R →ₐ[R] S₁) : φ = aeval (φ ∘ X) := by sorry

@[target]
theorem aeval_X_left : aeval X = AlgHom.id R (MvPolynomial σ R) :=
  sorry

@[target]
theorem aeval_X_left_apply (p : MvPolynomial σ R) : aeval X p = p :=
  sorry

@[target]
theorem comp_aeval {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B) :
    φ.comp (aeval f) = aeval fun i => φ (f i) := by sorry

@[target]
lemma comp_aeval_apply {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B)
    (p : MvPolynomial σ R) :
    φ (aeval f p) = aeval (fun i ↦ φ (f i)) p := by sorry

@[simp]
theorem map_aeval {B : Type*} [CommSemiring B] (g : σ → S₁) (φ : S₁ →+* B) (p : MvPolynomial σ R) :
    φ (aeval g p) = eval₂Hom (φ.comp (algebraMap R S₁)) (fun i => φ (g i)) p := by
  rw [← comp_eval₂Hom]
  rfl

@[simp]
theorem eval₂Hom_zero (f : R →+* S₂) : eval₂Hom f (0 : σ → S₂) = f.comp constantCoeff := by
  ext <;> simp

@[simp]
theorem eval₂Hom_zero' (f : R →+* S₂) : eval₂Hom f (fun _ => 0 : σ → S₂) = f.comp constantCoeff :=
  eval₂Hom_zero f

theorem eval₂Hom_zero_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (0 : σ → S₂) p = f (constantCoeff p) :=
  RingHom.congr_fun (eval₂Hom_zero f) p

@[target]
theorem eval₂Hom_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂Hom f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  sorry

@[target, simp]
theorem eval₂_zero_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (0 : σ → S₂) p = f (constantCoeff p) :=
  sorry

@[simp]
theorem eval₂_zero'_apply (f : R →+* S₂) (p : MvPolynomial σ R) :
    eval₂ f (fun _ => 0 : σ → S₂) p = f (constantCoeff p) :=
  eval₂_zero_apply f p

@[simp]
theorem aeval_zero (p : MvPolynomial σ R) :
    aeval (0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  eval₂Hom_zero_apply (algebraMap R S₁) p

@[target, simp]
theorem aeval_zero' (p : MvPolynomial σ R) :
    aeval (fun _ => 0 : σ → S₁) p = algebraMap _ _ (constantCoeff p) :=
  sorry

@[simp]
theorem eval_zero : eval (0 : σ → R) = constantCoeff :=
  eval₂Hom_zero _

@[target, simp]
theorem eval_zero' : eval (fun _ => 0 : σ → R) = constantCoeff :=
  sorry

theorem aeval_monomial (g : σ → S₁) (d : σ →₀ ℕ) (r : R) :
    aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ k :=
  eval₂Hom_monomial _ _ _ _

theorem eval₂Hom_eq_zero (f : R →+* S₂) (g : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, g i = 0) : eval₂Hom f g φ = 0 := by
  rw [φ.as_sum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  obtain ⟨i, hi, hgi⟩ : ∃ i ∈ d.support, g i = 0 := h d (Finsupp.mem_support_iff.mp hd)
  rw [eval₂Hom_monomial, Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
  rw [hgi, zero_pow]
  rwa [← Finsupp.mem_support_iff]

@[target]
theorem aeval_eq_zero [Algebra R S₂] (f : σ → S₂) (φ : MvPolynomial σ R)
    (h : ∀ d, φ.coeff d ≠ 0 → ∃ i ∈ d.support, f i = 0) : aeval f φ = 0 :=
  sorry

theorem aeval_sum {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∑ i ∈ s, φ i) = ∑ i ∈ s, aeval f (φ i) :=
  map_sum (MvPolynomial.aeval f) _ _

@[target, to_additive existing]
theorem aeval_prod {ι : Type*} (s : Finset ι) (φ : ι → MvPolynomial σ R) :
    aeval f (∏ i ∈ s, φ i) = ∏ i ∈ s, aeval f (φ i) :=
  sorry

variable (R)

theorem _root_.Algebra.adjoin_range_eq_range_aeval :
    Algebra.adjoin R (Set.range f) = (MvPolynomial.aeval f).range := by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]

@[target]
theorem _root_.Algebra.adjoin_eq_range (s : Set S₁) :
    Algebra.adjoin R s = (MvPolynomial.aeval ((↑) : s → S₁)).range := by sorry

end Aeval

section AevalTower

variable {S A B : Type*} [CommSemiring S] [CommSemiring A] [CommSemiring B]
variable [Algebra S R] [Algebra S A] [Algebra S B]

/-- Version of `aeval` for defining algebra homs out of `MvPolynomial σ R` over a smaller base ring
  than `R`. -/
def aevalTower (f : R →ₐ[S] A) (X : σ → A) : MvPolynomial σ R →ₐ[S] A :=
  { eval₂Hom (↑f) X with
    commutes' := fun r => by
      simp [IsScalarTower.algebraMap_eq S R (MvPolynomial σ R), algebraMap_eq] }

variable (g : R →ₐ[S] A) (y : σ → A)

@[target, simp]
theorem aevalTower_X (i : σ) : aevalTower g y (X i) = y i :=
  sorry

@[target, simp]
theorem aevalTower_C (x : R) : aevalTower g y (C x) = g x :=
  sorry

@[target, simp]
theorem aevalTower_ofNat (n : Nat) [n.AtLeastTwo] :
    aevalTower g y (ofNat(n) : MvPolynomial σ R) = ofNat(n) :=
  sorry

@[target, simp]
theorem aevalTower_comp_C : (aevalTower g y : MvPolynomial σ R →+* A).comp C = g :=
  sorry

@[target]
theorem aevalTower_algebraMap (x : R) : aevalTower g y (algebraMap R (MvPolynomial σ R) x) = g x :=
  sorry

theorem aevalTower_comp_algebraMap :
    (aevalTower g y : MvPolynomial σ R →+* A).comp (algebraMap R (MvPolynomial σ R)) = g :=
  aevalTower_comp_C _ _

theorem aevalTower_toAlgHom (x : R) :
    aevalTower g y (IsScalarTower.toAlgHom S R (MvPolynomial σ R) x) = g x :=
  aevalTower_algebraMap _ _ _

@[simp]
theorem aevalTower_comp_toAlgHom :
    (aevalTower g y).comp (IsScalarTower.toAlgHom S R (MvPolynomial σ R)) = g :=
  AlgHom.coe_ringHom_injective <| aevalTower_comp_algebraMap _ _

@[simp]
theorem aevalTower_id :
    aevalTower (AlgHom.id S S) = (aeval : (σ → S) → MvPolynomial σ S →ₐ[S] S) := by
  ext
  simp only [aevalTower_X, aeval_X]

@[simp]
theorem aevalTower_ofId :
    aevalTower (Algebra.ofId S A) = (aeval : (σ → A) → MvPolynomial σ S →ₐ[S] A) := by
  ext
  simp only [aeval_X, aevalTower_X]

end AevalTower

section EvalMem

variable {S subS : Type*} [CommSemiring S] [SetLike subS S] [SubsemiringClass subS S]

@[target]
theorem eval₂_mem {f : R →+* S} {p : MvPolynomial σ R} {s : subS}
    (hs : ∀ i ∈ p.support, f (p.coeff i) ∈ s) {v : σ → S} (hv : ∀ i, v i ∈ s) :
    MvPolynomial.eval₂ f v p ∈ s := by sorry

theorem eval_mem {p : MvPolynomial σ S} {s : subS} (hs : ∀ i ∈ p.support, p.coeff i ∈ s) {v : σ → S}
    (hv : ∀ i, v i ∈ s) : MvPolynomial.eval v p ∈ s :=
  eval₂_mem hs hv

end EvalMem

variable {S T : Type*} [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

@[target]
lemma aeval_sumElim {σ τ : Type*} (p : MvPolynomial (σ ⊕ τ) R) (f : τ → S) (g : σ → T) :
    (aeval (Sum.elim g (algebraMap S T ∘ f))) p =
      (aeval g) ((aeval (Sum.elim X (C ∘ f))) p) := by sorry

@[deprecated (since := "2025-02-21")] alias aeval_sum_elim := aeval_sumElim

end CommSemiring

end MvPolynomial
