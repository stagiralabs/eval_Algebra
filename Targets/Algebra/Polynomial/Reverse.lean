import VerifiedAgora.tagger
/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : R[X]` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.natDegree * f(1/X)`.

The main result is that `reverse (f * g) = reverse f * reverse g`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/


namespace Polynomial

open Finsupp Finset

open scoped Polynomial

section Semiring

variable {R : Type*} [Semiring R] {f : R[X]}

/-- If `i ≤ N`, then `revAtFun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `revAt`.
-/
def revAtFun (N i : ℕ) : ℕ :=
  ite (i ≤ N) (N - i) i

@[target]
theorem revAtFun_invol {N i : ℕ} : revAtFun N (revAtFun N i) = i := by sorry

@[target]
theorem revAtFun_inj {N : ℕ} : Function.Injective (revAtFun N) := by sorry
def revAt (N : ℕ) : Function.Embedding ℕ ℕ where
  toFun i := ite (i ≤ N) (N - i) i
  inj' := revAtFun_inj

/-- We prefer to use the bundled `revAt` over unbundled `revAtFun`. -/
@[target, simp]
theorem revAtFun_eq (N i : ℕ) : revAtFun N i = revAt N i :=
  sorry

@[simp]
theorem revAt_invol {N i : ℕ} : (revAt N) (revAt N i) = i :=
  revAtFun_invol

@[target, simp]
theorem revAt_le {N i : ℕ} (H : i ≤ N) : revAt N i = N - i :=
  sorry

@[target]
lemma revAt_eq_self_of_lt {N i : ℕ} (h : N < i) : revAt N i = i := by sorry

@[target]
theorem revAt_add {N O n o : ℕ} (hn : n ≤ N) (ho : o ≤ O) :
    revAt (N + O) (n + o) = revAt N n + revAt O o := by sorry

@[target]
theorem revAt_zero (N : ℕ) : revAt N 0 = N := by sorry

theorem reflect_support (N : ℕ) (f : R[X]) :
    (reflect N f).support = Finset.image (revAt N) f.support := by
  rcases f with ⟨⟩
  ext1
  simp only [reflect, support_ofFinsupp, support_embDomain, Finset.mem_map, Finset.mem_image]

@[simp]
theorem coeff_reflect (N : ℕ) (f : R[X]) (i : ℕ) : coeff (reflect N f) i = f.coeff (revAt N i) := by
  rcases f with ⟨f⟩
  simp only [reflect, coeff]
  calc
    Finsupp.embDomain (revAt N) f i = Finsupp.embDomain (revAt N) f (revAt N (revAt N i)) := by
      rw [revAt_invol]
    _ = f (revAt N i) := Finsupp.embDomain_apply _ _ _

@[target, simp]
theorem reflect_zero {N : ℕ} : reflect N (0 : R[X]) = 0 :=
  sorry

@[target, simp]
theorem reflect_eq_zero_iff {N : ℕ} {f : R[X]} : reflect N (f : R[X]) = 0 ↔ f = 0 := by sorry

@[target, simp]
theorem reflect_add (f g : R[X]) (N : ℕ) : reflect N (f + g) = reflect N f + reflect N g := by sorry

@[simp]
theorem reflect_C_mul (f : R[X]) (r : R) (N : ℕ) : reflect N (C r * f) = C r * reflect N f := by
  ext
  simp only [coeff_reflect, coeff_C_mul]

theorem reflect_C_mul_X_pow (N n : ℕ) {c : R} : reflect N (C c * X ^ n) = C c * X ^ revAt N n := by
  ext
  rw [reflect_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_reflect]
  split_ifs with h
  · rw [h, revAt_invol, coeff_X_pow_self]
  · rw [not_mem_support_iff.mp]
    intro a
    rw [← one_mul (X ^ n), ← C_1] at a
    apply h
    rw [← mem_support_C_mul_X_pow a, revAt_invol]

@[simp]
theorem reflect_C (r : R) (N : ℕ) : reflect N (C r) = C r * X ^ N := by
  conv_lhs => rw [← mul_one (C r), ← pow_zero X, reflect_C_mul_X_pow, revAt_zero]

@[simp]
theorem reflect_monomial (N n : ℕ) : reflect N ((X : R[X]) ^ n) = X ^ revAt N n := by
  rw [← one_mul (X ^ n), ← one_mul (X ^ revAt N n), ← C_1, reflect_C_mul_X_pow]

@[simp] lemma reflect_one_X : reflect 1 (X : R[X]) = 1 := by
  simpa using reflect_monomial 1 1 (R := R)

@[target]
lemma reflect_map {S : Type*} [Semiring S] (f : R →+* S) (p : R[X]) (n : ℕ) :
    (p.map f).reflect n = (p.reflect n).map f := by sorry

@[target, simp]
lemma reflect_one (n : ℕ) : (1 : R[X]).reflect n = Polynomial.X ^ n := by sorry

@[target]
theorem reflect_mul_induction (cf cg : ℕ) :
    ∀ N O : ℕ,
      ∀ f g : R[X],
        #f.support ≤ cf.succ →
          #g.support ≤ cg.succ →
            f.natDegree ≤ N →
              g.natDegree ≤ O → reflect (N + O) (f * g) = reflect N f * reflect O g := by sorry

@[target, simp]
theorem reflect_mul (f g : R[X]) {F G : ℕ} (Ff : f.natDegree ≤ F) (Gg : g.natDegree ≤ G) :
    reflect (F + G) (f * g) = reflect F f * reflect G g :=
  sorry

section Eval₂

variable {S : Type*} [CommSemiring S]

@[target]
theorem eval₂_reflect_mul_pow (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟ x) (reflect N f) * x ^ N = eval₂ i x f := by sorry

theorem eval₂_reflect_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟ x) (reflect N f) = 0 ↔ eval₂ i x f = 0 := by
  conv_rhs => rw [← eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h, zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟ x) _), ← one_pow N, ← mul_invOf_self x, mul_pow, ← mul_assoc, h,
      zero_mul]

end Eval₂

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, `reverse f = f (1/X) * X ^ f.natDegree`. -/
noncomputable def reverse (f : R[X]) : R[X] :=
  reflect f.natDegree f

@[target]
theorem coeff_reverse (f : R[X]) (n : ℕ) : f.reverse.coeff n = f.coeff (revAt f.natDegree n) := by sorry

@[target, simp]
theorem coeff_zero_reverse (f : R[X]) : coeff (reverse f) 0 = leadingCoeff f := by sorry

@[simp]
theorem reverse_zero : reverse (0 : R[X]) = 0 :=
  rfl

@[target, simp]
theorem reverse_eq_zero : f.reverse = 0 ↔ f = 0 := by sorry

theorem reverse_natDegree_le (f : R[X]) : f.reverse.natDegree ≤ f.natDegree := by
  rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
  intro n hn
  rw [Nat.cast_lt] at hn
  rw [coeff_reverse, revAt, Function.Embedding.coeFn_mk, if_neg (not_le_of_gt hn),
    coeff_eq_zero_of_natDegree_lt hn]

@[target]
theorem natDegree_eq_reverse_natDegree_add_natTrailingDegree (f : R[X]) :
    f.natDegree = f.reverse.natDegree + f.natTrailingDegree := by sorry

theorem reverse_natDegree (f : R[X]) : f.reverse.natDegree = f.natDegree - f.natTrailingDegree := by
  rw [f.natDegree_eq_reverse_natDegree_add_natTrailingDegree, add_tsub_cancel_right]

@[target]
theorem reverse_leadingCoeff (f : R[X]) : f.reverse.leadingCoeff = f.trailingCoeff := by sorry

theorem natTrailingDegree_reverse (f : R[X]) : f.reverse.natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero, reverse_eq_zero, coeff_zero_reverse, leadingCoeff_ne_zero]
  exact eq_or_ne _ _

@[target]
theorem reverse_trailingCoeff (f : R[X]) : f.reverse.trailingCoeff = f.leadingCoeff := by sorry

@[target]
theorem reverse_mul {f g : R[X]} (fg : f.leadingCoeff * g.leadingCoeff ≠ 0) :
    reverse (f * g) = reverse f * reverse g := by sorry

@[simp]
theorem reverse_mul_of_domain {R : Type*} [Ring R] [NoZeroDivisors R] (f g : R[X]) :
    reverse (f * g) = reverse f * reverse g := by
  by_cases f0 : f = 0
  · simp only [f0, zero_mul, reverse_zero]
  by_cases g0 : g = 0
  · rw [g0, mul_zero, reverse_zero, mul_zero]
  simp [reverse_mul, *]

@[target]
theorem trailingCoeff_mul {R : Type*} [Ring R] [NoZeroDivisors R] (p q : R[X]) :
    (p * q).trailingCoeff = p.trailingCoeff * q.trailingCoeff := by sorry

@[target, simp]
theorem coeff_one_reverse (f : R[X]) : coeff (reverse f) 1 = nextCoeff f := by sorry

@[simp] lemma reverse_C (t : R) :
    reverse (C t) = C t := by
  simp [reverse]

@[simp] lemma reverse_mul_X (p : R[X]) : reverse (p * X) = reverse p := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · simp [reverse, hp]

@[simp] lemma reverse_X_mul (p : R[X]) : reverse (X * p) = reverse p := by
  rw [commute_X p, reverse_mul_X]

@[simp] lemma reverse_mul_X_pow (p : R[X]) (n : ℕ) : reverse (p * X ^ n) = reverse p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, reverse_mul_X, ih]

@[simp] lemma reverse_X_pow_mul (p : R[X]) (n : ℕ) : reverse (X ^ n * p) = reverse p := by
  rw [commute_X_pow p, reverse_mul_X_pow]

@[simp] lemma reverse_add_C (p : R[X]) (t : R) :
    reverse (p + C t) = reverse p + C t * X ^ p.natDegree := by
  simp [reverse]

@[simp] lemma reverse_C_add (p : R[X]) (t : R) :
    reverse (C t + p) = C t * X ^ p.natDegree + reverse p := by
  rw [add_comm, reverse_add_C, add_comm]

section Eval₂

variable {S : Type*} [CommSemiring S]

theorem eval₂_reverse_mul_pow (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟ x) (reverse f) * x ^ f.natDegree = eval₂ i x f :=
  eval₂_reflect_mul_pow i _ _ f le_rfl

@[target, simp]
theorem eval₂_reverse_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (f : R[X]) :
    eval₂ i (⅟ x) (reverse f) = 0 ↔ eval₂ i x f = 0 :=
  sorry

end Eval₂

end Semiring

section Ring

variable {R : Type*} [Ring R]

@[target, simp]
theorem reflect_neg (f : R[X]) (N : ℕ) : reflect N (-f) = -reflect N f := by sorry

@[target, simp]
theorem reflect_sub (f g : R[X]) (N : ℕ) : reflect N (f - g) = reflect N f - reflect N g := by sorry

@[target, simp]
theorem reverse_neg (f : R[X]) : reverse (-f) = -reverse f := by sorry

end Ring

end Polynomial
