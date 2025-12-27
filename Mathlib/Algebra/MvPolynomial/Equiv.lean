import VerifiedAgora.tagger
/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Finsupp.Fin
import Mathlib.Logic.Equiv.Fin

/-!
# Equivalences between polynomial rings

This file establishes a number of equivalences between polynomial rings,
based on equivalences between the underlying types.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `a : R`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ R`

## Tags

equivalence, isomorphism, morphism, ring hom, hom

-/


noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

section Equiv

variable (R) [CommSemiring R]

/-- The ring isomorphism between multivariable polynomials in a single variable and
polynomials over the ground ring.
-/
@[simps]
def pUnitAlgEquiv : MvPolynomial PUnit R ≃ₐ[R] R[X] where
  toFun := eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X PUnit.unit)
  left_inv := by
    let f : R[X] →+* MvPolynomial PUnit R := Polynomial.eval₂RingHom MvPolynomial.C (X PUnit.unit)
    let g : MvPolynomial PUnit R →+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    show ∀ p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C, Polynomial.eval₂_C]
    · rintro ⟨⟩
      dsimp [f, g]
      rw [eval₂_X, Polynomial.eval₂_X]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _

section Map

variable {R} (σ)

/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def mapEquiv [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    MvPolynomial σ S₁ ≃+* MvPolynomial σ S₂ := by sorry


@[target] theorem mapEquiv_refl : mapEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ := by sorry


@[target] theorem mapEquiv_symm [CommSemiring S₁] [CommSemiring S₂] (e : S₁ ≃+* S₂) :
    (mapEquiv σ e).symm = mapEquiv σ e.symm := by sorry


@[simp]
theorem mapEquiv_trans [CommSemiring S₁] [CommSemiring S₂] [CommSemiring S₃] (e : S₁ ≃+* S₂)
    (f : S₂ ≃+* S₃) : (mapEquiv σ e).trans (mapEquiv σ f) = mapEquiv σ (e.trans f) :=
  RingEquiv.ext fun p => by
    simp only [RingEquiv.coe_trans, comp_apply, mapEquiv_apply, RingEquiv.coe_ringHom_trans,
      map_map]

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def mapAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPolynomial σ A₁ ≃ₐ[R] MvPolynomial σ A₂ := by sorry


@[simp]
theorem mapAlgEquiv_refl : mapAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext map_id

@[simp]
theorem mapAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (mapAlgEquiv σ e).symm = mapAlgEquiv σ e.symm :=
  rfl

@[target] theorem mapAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (mapAlgEquiv σ e).trans (mapAlgEquiv σ f) = mapAlgEquiv σ (e.trans f) := by
  sorry


end Map

section

variable (S₁ S₂ S₃)

/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
/-- The function from multivariable polynomials in a sum of two types,
to multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.

See `sumRingEquiv` for the ring isomorphism.
-/
def sumToIter : MvPolynomial (S₁ ⊕ S₂) R →+* MvPolynomial S₁ (MvPolynomial S₂ R) := by sorry


@[target] theorem sumToIter_C (a : R) : sumToIter R S₁ S₂ (C a) = C (C a) := by sorry


@[target] theorem sumToIter_Xl (b : S₁) : sumToIter R S₁ S₂ (X (Sum.inl b)) = X b := by sorry


@[target] theorem sumToIter_Xr (c : S₂) : sumToIter R S₁ S₂ (X (Sum.inr c)) = C (X c) := by sorry


/-- The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
/-- The function from multivariable polynomials in one type,
with coefficients in multivariable polynomials in another type,
to multivariable polynomials in the sum of the two types.

See `sumRingEquiv` for the ring isomorphism.
-/
def iterToSum : MvPolynomial S₁ (MvPolynomial S₂ R) →+* MvPolynomial (S₁ ⊕ S₂) R := by sorry


@[target] theorem iterToSum_C_C (a : R) : iterToSum R S₁ S₂ (C (C a)) = C a := by sorry


@[target] theorem iterToSum_X (b : S₁) : iterToSum R S₁ S₂ (X b) = X (Sum.inl b) := by sorry


@[target] theorem iterToSum_C_X (c : S₂) : iterToSum R S₁ S₂ (C (X c)) = X (Sum.inr c) := by sorry


section isEmptyRingEquiv
variable [IsEmpty σ]

variable (σ) in
/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
variable (σ) in
/-- The algebra isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
def isEmptyAlgEquiv : MvPolynomial σ R ≃ₐ[R] R :=
  .ofAlgHom (aeval isEmptyElim) (Algebra.ofId _ _) (by sorry


variable {R S₁} in
@[simp]
lemma aeval_injective_iff_of_isEmpty [CommSemiring S₁] [Algebra R S₁] {f : σ → S₁} :
    Function.Injective (aeval f : MvPolynomial σ R →ₐ[R] S₁) ↔
      Function.Injective (algebraMap R S₁) := by
  have : aeval f = (Algebra.ofId R S₁).comp (@isEmptyAlgEquiv R σ _ _).toAlgHom := by
    ext i
    exact IsEmpty.elim' ‹IsEmpty σ› i
  rw [this, ← Injective.of_comp_iff' _ (@isEmptyAlgEquiv R σ _ _).bijective]
  rfl

variable (σ) in
/-- The ring isomorphism between multivariable polynomials in no variables
and the ground ring. -/
@[simps! apply]
def isEmptyRingEquiv : MvPolynomial σ R ≃+* R := (isEmptyAlgEquiv R σ).toRingEquiv

@[target] lemma isEmptyRingEquiv_symm_toRingHom : (isEmptyRingEquiv R σ).symm.toRingHom = C := by sorry

@[simp] lemma isEmptyRingEquiv_symm_apply (r : R) : (isEmptyRingEquiv R σ).symm r = C r := rfl

@[target] lemma isEmptyRingEquiv_eq_coeff_zero {σ R : Type*} [CommSemiring R] [IsEmpty σ] {x} :
    isEmptyRingEquiv R σ x = x.coeff 0 := by
  sorry


end isEmptyRingEquiv

/-- A helper function for `sumRingEquiv`. -/
/-- A helper function for `sumRingEquiv`. -/
@[simps]
def mvPolynomialEquivMvPolynomial [CommSemiring S₃] (f : MvPolynomial S₁ R →+* MvPolynomial S₂ S₃)
    (g : MvPolynomial S₂ S₃ →+* MvPolynomial S₁ R) (hfgC : (f.comp g).comp C = C)
    (hfgX : ∀ n, f (g (X n)) = X n) (hgfC : (g.comp f).comp C = C) (hgfX : ∀ n, g (f (X n)) = X n) :
    MvPolynomial S₁ R ≃+* MvPolynomial S₂ S₃ where
  toFun := by sorry


/-- The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
/-- The ring isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
def sumRingEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃+* MvPolynomial S₁ (MvPolynomial S₂ R) := by
  sorry


/-- The algebra isomorphism between multivariable polynomials in a sum of two types,
and multivariable polynomials in one of the types,
with coefficients in multivariable polynomials in the other type.
-/
@[simps!]
def sumAlgEquiv : MvPolynomial (S₁ ⊕ S₂) R ≃ₐ[R] MvPolynomial S₁ (MvPolynomial S₂ R) :=
  { sumRingEquiv R S₁ S₂ with
    commutes' := by
      intro r
      have A : algebraMap R (MvPolynomial S₁ (MvPolynomial S₂ R)) r = (C (C r) :) := rfl
      have B : algebraMap R (MvPolynomial (S₁ ⊕ S₂) R) r = C r := rfl
      simp only [sumRingEquiv, mvPolynomialEquivMvPolynomial, Equiv.toFun_as_coe,
        Equiv.coe_fn_mk, B, sumToIter_C, A] }

lemma sumAlgEquiv_comp_rename_inr :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inr) = IsScalarTower.toAlgHom R
        (MvPolynomial S₂ R) (MvPolynomial S₁ (MvPolynomial S₂ R)) := by
  ext i
  simp

@[target] lemma sumAlgEquiv_comp_rename_inl :
    (sumAlgEquiv R S₁ S₂).toAlgHom.comp (rename Sum.inl) =
      MvPolynomial.mapAlgHom (Algebra.ofId _ _) := by
  sorry


section commAlgEquiv
variable {R S₁ S₂ : Type*} [CommSemiring R]

variable (R S₁ S₂) in
/-- The algebra isomorphism between multivariable polynomials in variables `S₁` of multivariable
polynomials in variables `S₂` and multivariable polynomials in variables `S₂` of multivariable
polynomials in variables `S₁`. -/
variable (R S₁ S₂) in
/-- The algebra isomorphism between multivariable polynomials in variables `S₁` of multivariable
polynomials in variables `S₂` and multivariable polynomials in variables `S₂` of multivariable
polynomials in variables `S₁`. -/
noncomputable
def commAlgEquiv : MvPolynomial S₁ (MvPolynomial S₂ R) ≃ₐ[R] MvPolynomial S₂ (MvPolynomial S₁ R) := by sorry


@[target] lemma commAlgEquiv_C (p) : commAlgEquiv R S₁ S₂ (.C p) = .map C p := by
  sorry


@[target] lemma commAlgEquiv_C_X (i) : commAlgEquiv R S₁ S₂ (.C (.X i)) = .X i := by sorry


@[target] lemma commAlgEquiv_X (i) : commAlgEquiv R S₁ S₂ (.X i) = .C (.X i) := by sorry


end commAlgEquiv

section

-- this speeds up typeclass search in the lemma below
attribute [local instance] IsScalarTower.right

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
polynomials with coefficients in `MvPolynomial S₁ R`.
-/
@[simps!]
def optionEquivLeft : MvPolynomial (Option S₁) R ≃ₐ[R] Polynomial (MvPolynomial S₁ R) :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim Polynomial.X fun s => Polynomial.C (X s))
    (Polynomial.aevalTower (MvPolynomial.rename some) (X none))
    (by sorry


@[target] lemma optionEquivLeft_X_some (x : S₁) : optionEquivLeft R S₁ (X (some x)) = Polynomial.C (X x) := by
  sorry


lemma optionEquivLeft_X_none : optionEquivLeft R S₁ (X none) = Polynomial.X := by
  simp [optionEquivLeft_apply, aeval_X]

@[target] lemma optionEquivLeft_C (r : R) : optionEquivLeft R S₁ (C r) = Polynomial.C (C r) := by
  sorry


end

/-- The algebra isomorphism between multivariable polynomials in `Option S₁` and
multivariable polynomials with coefficients in polynomials.
-/
@[simps!]
def optionEquivRight : MvPolynomial (Option S₁) R ≃ₐ[R] MvPolynomial S₁ R[X] :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun o => o.elim (C Polynomial.X) X)
    (MvPolynomial.aevalTower (Polynomial.aeval (X none)) fun i => X (Option.some i))
    (by
      ext : 2 <;>
        simp only [MvPolynomial.algebraMap_eq, Option.elim, AlgHom.coe_comp, AlgHom.id_comp,
          IsScalarTower.coe_toAlgHom', comp_apply, aevalTower_C, Polynomial.aeval_X, aeval_X,
          Option.elim', aevalTower_X, AlgHom.coe_id, id, eq_self_iff_true, imp_true_iff])
    (by
      ext ⟨i⟩ : 2 <;>
        simp only [Option.elim, AlgHom.coe_comp, comp_apply, aeval_X, aevalTower_C,
          Polynomial.aeval_X, AlgHom.coe_id, id, aevalTower_X])

lemma optionEquivRight_X_some (x : S₁) : optionEquivRight R S₁ (X (some x)) = X x := by
  simp [optionEquivRight_apply, aeval_X]

@[target] lemma optionEquivRight_X_none : optionEquivRight R S₁ (X none) = C Polynomial.X := by
  sorry


@[target] lemma optionEquivRight_C (r : R) : optionEquivRight R S₁ (C r) = C (Polynomial.C r) := by
  sorry


variable (n : ℕ)

/-- The algebra isomorphism between multivariable polynomials in `Fin (n + 1)` and
polynomials over multivariable polynomials in `Fin n`.
-/
def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
  (renameEquiv R (_root_.finSuccEquiv n)).trans (optionEquivLeft R (Fin n))

@[target] theorem finSuccEquiv_eq :
    (finSuccEquiv R n : MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin n) R)) =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R)) fun i : Fin (n + 1) =>
        Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i := by
  sorry


@[target] theorem finSuccEquiv_apply (p : MvPolynomial (Fin (n + 1)) R) :
    finSuccEquiv R n p =
      eval₂Hom (Polynomial.C.comp (C : R →+* MvPolynomial (Fin n) R))
        (fun i : Fin (n + 1) => Fin.cases Polynomial.X (fun k => Polynomial.C (X k)) i) p := by
  sorry


@[target] theorem finSuccEquiv_comp_C_eq_C {R : Type u} [CommSemiring R] (n : ℕ) :
    (↑(MvPolynomial.finSuccEquiv R n).symm : Polynomial (MvPolynomial (Fin n) R) →+* _).comp
        (Polynomial.C.comp MvPolynomial.C) =
      (MvPolynomial.C : R →+* MvPolynomial (Fin n.succ) R) := by
  sorry


variable {n} {R}

theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp [finSuccEquiv_apply]

theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j) := by
  simp [finSuccEquiv_apply]

/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals the
    coefficient of `Finsupp.cons i m` in `f`. -/
/-- The coefficient of `m` in the `i`-th coefficient of `finSuccEquiv R n f` equals the
    coefficient of `Finsupp.cons i m` in `f`. -/
@[target] theorem finSuccEquiv_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  sorry


theorem eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
    eval (Fin.cons y s : Fin (n + 1) → R) f =
      Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f)) := by
  -- turn this into a def `Polynomial.mapAlgHom`
  let φ : (MvPolynomial (Fin n) R)[X] →ₐ[R] R[X] :=
    { Polynomial.mapRingHom (eval s) with
      commutes' := fun r => by
        convert Polynomial.map_C (eval s)
        exact (eval_C _).symm }
  show
    aeval (Fin.cons y s : Fin (n + 1) → R) f =
      (Polynomial.aeval y).comp (φ.comp (finSuccEquiv R n).toAlgHom) f
  congr 2
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_iff_succ]
  simp only [φ, aeval_X, Fin.cons_zero, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp,
    Polynomial.coe_aeval_eq_eval, Polynomial.map_C, AlgHom.coe_mk, RingHom.toFun_eq_coe,
    Polynomial.coe_mapRingHom, comp_apply, finSuccEquiv_apply, eval₂Hom_X',
    Fin.cases_zero, Polynomial.map_X, Polynomial.eval_X, Fin.cons_succ,
    Fin.cases_succ, eval_X, Polynomial.eval_C,
    RingHom.coe_mk, MonoidHom.coe_coe, AlgHom.coe_coe, implies_true, and_self,
    RingHom.toMonoidHom_eq_coe]

@[target] theorem coeff_eval_eq_eval_coeff (s' : Fin n → R) (f : Polynomial (MvPolynomial (Fin n) R))
    (i : ℕ) : Polynomial.coeff (Polynomial.map (eval s') f) i = eval s' (Polynomial.coeff f i) := by
  sorry


@[target] theorem support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {m : Fin n →₀ ℕ} :
    m ∈ ((finSuccEquiv R n f).coeff i).support ↔ m.cons i ∈ f.support := by
  sorry


/--
The `totalDegree` of a multivariable polynomial `p` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquiv` applied to `p`, if this is nonzero.
-/
/--
The `totalDegree` of a multivariable polynomial `p` is at least `i` more than the `totalDegree` of
the `i`th coefficient of `finSuccEquiv` applied to `p`, if this is nonzero.
-/
@[target] lemma totalDegree_coeff_finSuccEquiv_add_le (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ)
    (hi : (finSuccEquiv R n f).coeff i ≠ 0) :
    totalDegree ((finSuccEquiv R n f).coeff i) + i ≤ totalDegree f := by
  sorry


@[target] theorem support_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).support = Finset.image (fun m : Fin (n + 1) →₀ ℕ => m 0) f.support := by
  sorry


@[deprecated (since := "2024-11-05")] alias finSuccEquiv_support := support_finSuccEquiv

@[target] theorem mem_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {x} :
    x ∈ (finSuccEquiv R n f).support ↔ x ∈ (fun m : Fin (n + 1) →₀ _ ↦ m 0) '' f.support := by
  sorry


theorem image_support_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} :
    ((finSuccEquiv R n f).coeff i).support.image (Finsupp.cons i) = {m ∈ f.support | m 0 = i} := by
  ext m
  rw [Finset.mem_filter, Finset.mem_image, mem_support_iff]
  conv_lhs =>
    congr
    ext
    rw [mem_support_iff, finSuccEquiv_coeff_coeff, Ne]
  constructor
  · rintro ⟨m', ⟨h, hm'⟩⟩
    simp only [← hm']
    exact ⟨h, by rw [cons_zero]⟩
  · intro h
    use tail m
    rw [← h.2, cons_tail]
    simp [h.1]

@[deprecated (since := "2024-11-05")] alias finSuccEquiv_support' := image_support_finSuccEquiv

@[target] lemma mem_image_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ Finsupp.cons i '' ((finSuccEquiv R n f).coeff i).support ↔
      x ∈ f.support ∧ x 0 = i := by
  sorry


@[target] lemma mem_support_coeff_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} {i : ℕ} {x} :
    x ∈ ((finSuccEquiv R n f).coeff i).support ↔ x.cons i ∈ f.support := by
  sorry

@[target] theorem support_finSuccEquiv_nonempty {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).support.Nonempty := by
  sorry


theorem degree_finSuccEquiv {f : MvPolynomial (Fin (n + 1)) R} (h : f ≠ 0) :
    (finSuccEquiv R n f).degree = degreeOf 0 f := by
  -- TODO: these should be lemmas
  have h₀ : ∀ {α β : Type _} (f : α → β), (fun x => x) ∘ f = f := fun f => rfl
  have h₁ : ∀ {α β : Type _} (f : α → β), f ∘ (fun x => x) = f := fun f => rfl

  have h' : ((finSuccEquiv R n f).support.sup fun x => x) = degreeOf 0 f := by
    rw [degreeOf_eq_sup, support_finSuccEquiv, Finset.sup_image, h₀]
  rw [Polynomial.degree, ← h', Nat.cast_withBot,
    Finset.coe_sup_of_nonempty (support_finSuccEquiv_nonempty h), Finset.max_eq_sup_coe, h₁]

@[target] theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  sorry


@[target] theorem degreeOf_coeff_finSuccEquiv (p : MvPolynomial (Fin (n + 1)) R) (j : Fin n) (i : ℕ) :
    degreeOf j (Polynomial.coeff (finSuccEquiv R n p) i) ≤ degreeOf j.succ p := by
  sorry


/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `0`-th variable
    via `MvPolynomial.finSuccEquiv`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This lemma shows that both constructions are the same. -/
/-- Consider a multivariate polynomial `φ` whose variables are indexed by `Option σ`,
and suppose that `σ ≃ Fin n`.
Then one may view `φ` as a polynomial over `MvPolynomial (Fin n) R`, by

1. renaming the variables via `Option σ ≃ Fin (n+1)`, and then singling out the `0`-th variable
    via `MvPolynomial.finSuccEquiv`;
2. first viewing it as polynomial over `MvPolynomial σ R` via `MvPolynomial.optionEquivLeft`,
    and then renaming the variables.

This lemma shows that both constructions are the same. -/
@[target] lemma finSuccEquiv_rename_finSuccEquiv (e : σ ≃ Fin n) (φ : MvPolynomial (Option σ) R) :
    ((finSuccEquiv R n) ((rename ((Equiv.optionCongr e).trans (_root_.finSuccEquiv n).symm)) φ)) =
      Polynomial.map (rename e).toRingHom (optionEquivLeft R σ φ) := by
  sorry


end

@[target] theorem rename_polynomial_aeval_X {σ τ : Type*} (f : σ → τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ R) p := by
  sorry


end Equiv

end MvPolynomial
