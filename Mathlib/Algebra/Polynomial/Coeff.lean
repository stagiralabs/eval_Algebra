import VerifiedAgora.tagger
/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Regular.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/



noncomputable section

open Finsupp Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}
variable [Semiring R] {p q r : R[X]}

section Coeff

@[target] theorem coeff_add (A B : HVertexOperator Γ R V W) : (A + B).coeff = A.coeff + B.coeff := by
  sorry


@[target] theorem coeff_smul (A : HVertexOperator Γ R V W) (r : R) : (r • A).coeff = r • (A.coeff) := by
  sorry


@[target] lemma support_smul [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] (f : α → R)
    (g : α → M) : support (f • g) = support f ∩ support g := by sorry


open scoped Pointwise in
open scoped Pointwise in
@[target] theorem card_support_mul_le : #(p * q).support ≤ #p.support * #q.support := by
  sorry


/-- `Polynomial.sum` as a linear map. -/
/-- `Polynomial.sum` as a linear map. -/
@[simps]
def lsum {R A M : Type*} [Semiring R] [Semiring A] [AddCommMonoid M] [Module R A] [Module R M]
    (f : ℕ → A →ₗ[R] M) : A[X] →ₗ[R] M where
  toFun p := p.sum (f · ·)
  map_add' p q := sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _
  map_smul' c p := by
    sorry


variable (R) in
/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : R[X] →ₗ[R] R where
  toFun p := coeff p n
  map_add' p q := coeff_add p q n
  map_smul' r p := coeff_smul r p n

@[target] theorem lcoeff_apply (n : ℕ) (f : R[X]) : lcoeff R n f = coeff f n := by sorry


@[target] theorem finset_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    coeff (∑ b ∈ s, f b) n = ∑ b ∈ s, coeff (f b) n := by sorry


@[target] lemma coeff_list_sum (l : List R[X]) (n : ℕ) :
    l.sum.coeff n = (l.map (lcoeff R n)).sum := by sorry


@[target] lemma coeff_list_sum_map {ι : Type*} (l : List ι) (f : ι → R[X]) (n : ℕ) :
    (l.map f).sum.coeff n = (l.map (fun a => (f a).coeff n)).sum := by
  sorry


@[target] theorem coeff_sum [Semiring S] (n : ℕ) (f : ℕ → R → S[X]) :
    coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n := by
  sorry


/-- Decomposes the coefficient of the product `p * q` as a sum
over `antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`. -/
/-- Decomposes the coefficient of the product `p * q` as a sum
over `antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`. -/
@[target] theorem coeff_mul (p q : R[X]) (n : ℕ) :
    coeff (p * q) n = ∑ x ∈ antidiagonal n, coeff p x.1 * coeff q x.2 := by
  sorry


@[simp]
theorem mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := by simp [coeff_mul]

@[target] theorem mul_coeff_one (p q : R[X]) :
    coeff (p * q) 1 = coeff p 0 * coeff q 1 + coeff p 1 * coeff q 0 := by
  sorry


/-- `constantCoeff p` returns the constant term of the polynomial `p`,
  defined as `coeff p 0`. This is a ring homomorphism. -/
/-- `constantCoeff p` returns the constant term of the polynomial `p`,
  defined as `coeff p 0`. This is a ring homomorphism. -/
@[simps]
def constantCoeff : R[X] →+* R where
  toFun p := by sorry


@[target] theorem isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x := by sorry


@[target] theorem coeff_mul_X_zero (p : R[X]) : coeff (p * X) 0 = 0 := by sorry


@[target] theorem coeff_X_mul_zero (p : R[X]) : coeff (X * p) 0 = 0 := by sorry


@[target] theorem coeff_C_mul_X_pow (x : R) (k n : ℕ) :
    coeff (C x * X ^ k : R[X]) n = if n = k then x else 0 := by
  sorry


@[target] theorem coeff_C_mul_X (x : R) (n : ℕ) : coeff (C x * X : R[X]) n = if n = 1 then x else 0 := by
  sorry


@[target] theorem coeff_C_mul (p : R[X]) : coeff (C a * p) n = a * coeff p n := by
  sorry


theorem C_mul' (a : R) (f : R[X]) : C a * f = a • f := by
  ext
  rw [coeff_C_mul, coeff_smul, smul_eq_mul]

@[target] theorem coeff_mul_C (p : R[X]) (n : ℕ) (a : R) : coeff (p * C a) n = coeff p n * a := by
  sorry


@[target] lemma coeff_mul_natCast {a k : ℕ} :
  coeff (p * (a : R[X])) k = coeff p k * (↑a : R) := by sorry


@[target] lemma coeff_natCast_mul {a k : ℕ} :
  coeff ((a : R[X]) * p) k = a * coeff p k := by sorry


@[target] lemma coeff_mul_ofNat {a k : ℕ} [Nat.AtLeastTwo a] :
  coeff (p * (ofNat(a) : R[X])) k = coeff p k * ofNat(a) := by sorry


@[target] lemma coeff_ofNat_mul {a k : ℕ} [Nat.AtLeastTwo a] :
  coeff ((ofNat(a) : R[X]) * p) k = ofNat(a) * coeff p k := by sorry


@[target] lemma coeff_mul_intCast [Ring S] {p : S[X]} {a : ℤ} {k : ℕ} :
  coeff (p * (a : S[X])) k = coeff p k * (↑a : S) := by sorry


@[target] lemma coeff_intCast_mul [Ring S] {p : S[X]} {a : ℤ} {k : ℕ} :
  coeff ((a : S[X]) * p) k = a * coeff p k := by sorry


@[simp]
theorem coeff_X_pow (k n : ℕ) : coeff (X ^ k : R[X]) n = if n = k then 1 else 0 := by
  simp only [one_mul, RingHom.map_one, ← coeff_C_mul_X_pow]

@[target] theorem coeff_X_pow_self (n : ℕ) : coeff (X ^ n : R[X]) n = 1 := by sorry


section Fewnomials

open Finset

@[target] theorem support_binomial {k m : ℕ} (hkm : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    support (C x * X ^ k + C y * X ^ m) = {k, m} := by
  sorry


@[target] theorem support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) :
    support (C x * X ^ k + C y * X ^ m + C z * X ^ n) = {k, m, n} := by
  sorry


@[target] theorem card_support_binomial {k m : ℕ} (h : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    #(support (C x * X ^ k + C y * X ^ m)) = 2 := by
  sorry


@[target] theorem card_support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hz : z ≠ 0) : #(support (C x * X ^ k + C y * X ^ m + C z * X ^ n)) = 3 := by
  sorry


end Fewnomials

@[target] theorem coeff_mul_X_pow (p : R[X]) (n d : ℕ) :
    coeff (p * Polynomial.X ^ n) (d + n) = coeff p d := by
  sorry


@[target] theorem coeff_X_pow_mul (p : R[X]) (n d : ℕ) :
    coeff (Polynomial.X ^ n * p) (d + n) = coeff p d := by
  sorry


theorem coeff_mul_X_pow' (p : R[X]) (n d : ℕ) :
    (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  split_ifs with h
  · rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
  · refine (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => ?_)
    rw [coeff_X_pow, if_neg, mul_zero]
    exact ((le_of_add_le_right (mem_antidiagonal.mp hx).le).trans_lt <| not_le.mp h).ne

theorem coeff_X_pow_mul' (p : R[X]) (n d : ℕ) :
    (X ^ n * p).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 := by
  rw [(commute_X_pow p n).eq, coeff_mul_X_pow']

@[simp]
theorem coeff_mul_X (p : R[X]) (n : ℕ) : coeff (p * X) (n + 1) = coeff p n := by
  simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[target] theorem coeff_X_mul (p : R[X]) (n : ℕ) : coeff (X * p) (n + 1) = coeff p n := by
  sorry


theorem coeff_mul_monomial (p : R[X]) (n d : ℕ) (r : R) :
    coeff (p * monomial n r) (d + n) = coeff p d * r := by
  rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul, ← mul_assoc, coeff_mul_C, coeff_mul_X_pow]

@[target] theorem coeff_monomial_mul (p : R[X]) (n d : ℕ) (r : R) :
    coeff (monomial n r * p) (d + n) = r * coeff p d := by
  sorry

@[target] theorem coeff_mul_monomial_zero (p : R[X]) (d : ℕ) (r : R) :
    coeff (p * monomial 0 r) d = coeff p d * r := by sorry

theorem coeff_monomial_zero_mul (p : R[X]) (d : ℕ) (r : R) :
    coeff (monomial 0 r * p) d = r * coeff p d :=
  coeff_monomial_mul p 0 d r

@[target] theorem mul_X_pow_eq_zero {p : R[X]} {n : ℕ} (H : p * X ^ n = 0) : p = 0 := by sorry


@[target] theorem isRegular_X_pow (n : ℕ) : IsRegular (X ^ n : R[X]) := by
  sorry


@[target] theorem isRegular_X : IsRegular (X : R[X]) := by sorry


@[target] theorem coeff_X_add_C_pow (r : R) (n k : ℕ) :
    ((X + C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) := by
  sorry


theorem coeff_X_add_one_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((X + 1) ^ n).coeff k = (n.choose k : R) := by rw [← C_1, coeff_X_add_C_pow, one_pow, one_mul]

@[target] theorem coeff_one_add_X_pow (R : Type*) [Semiring R] (n k : ℕ) :
    ((1 + X) ^ n).coeff k = (n.choose k : R) := by sorry


@[target] theorem C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) : C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i := by
  sorry

    classical
      let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
      let ψ : R[X] := ∑ i ∈ φ.support, monomial i (c' i)
      use ψ
      ext i
      simp only [c', ψ, coeff_C_mul, mem_support_iff, coeff_monomial, finset_sum_coeff,
        Finset.sum_ite_eq']
      split_ifs with hi
      · rw [hc]
      · rw [Classical.not_not] at hi
        rwa [mul_zero]

theorem smul_eq_C_mul (a : R) : a • p = C a * p := by simp [ext_iff]

@[target] theorem update_eq_add_sub_coeff {R : Type*} [Ring R] (p : R[X]) (n : ℕ) (a : R) :
    p.update n a = p + Polynomial.C (a - p.coeff n) * Polynomial.X ^ n := by
  sorry


end Coeff

section cast

theorem natCast_coeff_zero {n : ℕ} {R : Type*} [Semiring R] : (n : R[X]).coeff 0 = n := by
  simp only [coeff_natCast_ite, ite_true]

@[target] theorem natCast_inj {m n : ℕ} {R : Type*} [Semiring R] [CharZero R] :
    (↑m : R[X]) = ↑n ↔ m = n := by
  sorry


@[target] theorem intCast_coeff_zero {i : ℤ} {R : Type*} [Ring R] : (i : R[X]).coeff 0 = i := by
  sorry


@[norm_cast]
theorem intCast_inj {m n : ℤ} {R : Type*} [Ring R] [CharZero R] : (↑m : R[X]) = ↑n ↔ m = n := by
  constructor
  · intro h
    apply_fun fun p => p.coeff 0 at h
    simpa using h
  · rintro rfl
    rfl

end cast

instance charZero [CharZero R] : CharZero R[X] where cast_injective _x _y := natCast_inj.mp

end Polynomial
