import VerifiedAgora.tagger
/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.IntervalCases

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

 * `Cubic`: the structure representing a cubic polynomial.
 * `Cubic.disc`: the discriminant of a cubic polynomial.

## Main statements

 * `Cubic.disc_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
    the cubic has no duplicate roots.

## References

 * https://en.wikipedia.org/wiki/Cubic_equation
 * https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/


noncomputable section

/-- The structure representing a cubic polynomial. -/
@[ext]
structure Cubic (R : Type*) where
  /-- The degree-3 coefficient -/
  a : R
  /-- The degree-2 coefficient -/
  b : R
  /-- The degree-1 coefficient -/
  c : R
  /-- The degree-0 coefficient -/
  d : R

namespace Cubic

open Polynomial

variable {R S F K : Type*}

instance [Inhabited R] : Inhabited (Cubic R) :=
  ⟨⟨default, default, default, default⟩⟩

instance [Zero R] : Zero (Cubic R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

section Basic

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

/-- Convert a cubic polynomial to a polynomial. -/
/-- Convert a cubic polynomial to a polynomial. -/
def toPoly (P : Cubic R) : R[X] := by sorry


@[target] theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    C w * (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  sorry


@[target] theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  sorry



section Coeff

private theorem coeffs : (∀ n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [toPoly, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow]
  norm_num
  intro n hn
  repeat' rw [if_neg]
  any_goals omega
  repeat' rw [zero_add]

@[target] theorem coeff_eq_zero {n : ℕ} (hn : 3 < n) : P.toPoly.coeff n = 0 := by sorry


@[target] theorem coeff_eq_a : P.toPoly.coeff 3 = P.a := by sorry


@[target] theorem coeff_eq_b : P.toPoly.coeff 2 = P.b := by sorry


@[target] theorem coeff_eq_c : P.toPoly.coeff 1 = P.c := by sorry


@[target] theorem coeff_eq_d : P.toPoly.coeff 0 = P.d := by sorry


@[target] theorem a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a := by sorry


@[target] theorem b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b := by sorry


@[target] theorem c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c := by sorry


@[target] theorem d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d := by sorry


@[target] theorem toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q := by sorry


@[target] theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d := by
  sorry


theorem of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d :=
  of_a_eq_zero rfl

@[target] theorem of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d := by
  sorry


theorem of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d :=
  of_b_eq_zero rfl rfl

@[target] theorem of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P.d := by
  sorry


theorem of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d :=
  of_c_eq_zero rfl rfl rfl

@[target] theorem of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly = 0 := by
  sorry


theorem of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0 :=
  of_d_eq_zero rfl rfl rfl rfl

@[simp]
protected lemma zero :
    (0 : End R M).invtSubmodule = ⊤ :=
  eq_top_iff.mpr fun x ↦ by sorry


theorem toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero, toPoly_injective]

private theorem ne_zero (h0 : P.a ≠ 0 ∨ P.b ≠ 0 ∨ P.c ≠ 0 ∨ P.d ≠ 0) : P.toPoly ≠ 0 := by
  contrapose! h0
  rw [(toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩

@[target] theorem ne_zero_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly ≠ 0 := by sorry


@[target] theorem ne_zero_of_b_ne_zero (hb : P.b ≠ 0) : P.toPoly ≠ 0 := by sorry


@[target] theorem ne_zero_of_c_ne_zero (hc : P.c ≠ 0) : P.toPoly ≠ 0 := by sorry


@[target] theorem ne_zero_of_d_ne_zero (hd : P.d ≠ 0) : P.toPoly ≠ 0 := by sorry


@[target] theorem leadingCoeff_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.leadingCoeff = P.a := by sorry


@[simp]
theorem leadingCoeff_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).leadingCoeff = a :=
  leadingCoeff_of_a_ne_zero ha

@[target] theorem leadingCoeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.leadingCoeff = P.b := by
  sorry


@[simp]
theorem leadingCoeff_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).leadingCoeff = b :=
  leadingCoeff_of_b_ne_zero rfl hb

@[target] theorem leadingCoeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.leadingCoeff = P.c := by
  sorry


@[simp]
theorem leadingCoeff_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c :=
  leadingCoeff_of_c_ne_zero rfl rfl hc

@[target] theorem leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.leadingCoeff = P.d := by
  sorry


theorem leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d :=
  leadingCoeff_of_c_eq_zero rfl rfl rfl

@[target] theorem monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic := by
  sorry


theorem monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic :=
  monic_of_a_eq_one rfl

@[target] theorem monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic := by
  sorry


theorem monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic :=
  monic_of_b_eq_one rfl rfl

@[target] theorem monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.Monic := by
  sorry


theorem monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic :=
  monic_of_c_eq_one rfl rfl rfl

@[target] theorem monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
    P.toPoly.Monic := by
  sorry


theorem monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic :=
  monic_of_d_eq_one rfl rfl rfl rfl

end Coeff

/-! ### Degrees -/


section Degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
open Submodule in
/-- Every module is the direct limit of its finitely generated submodules. -/
noncomputable def equiv : DirectLimit _ (fgSystem R M) ≃ₗ[R] M :=
  .ofBijective (lift _ _ _ _ (fun _ ↦ Submodule.subtype _) fun _ _ _ _ ↦ rfl)
    ⟨lift_injective _ _ fun _ ↦ Subtype.val_injective, fun x ↦
      ⟨of _ _ _ _ ⟨_, fg_span_singleton x⟩ ⟨x, subset_span <| by sorry


@[target] theorem degree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.degree = 3 := by sorry


@[simp]
theorem degree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).degree = 3 :=
  degree_of_a_ne_zero ha

@[target] theorem degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree ≤ 2 := by
  sorry


theorem degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree ≤ 2 :=
  degree_of_a_eq_zero rfl

@[target] theorem degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.degree = 2 := by
  sorry


@[simp]
theorem degree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).degree = 2 :=
  degree_of_b_ne_zero rfl hb

@[target] theorem degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree ≤ 1 := by
  sorry


theorem degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree ≤ 1 :=
  degree_of_b_eq_zero rfl rfl

@[target] theorem degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) : P.toPoly.degree = 1 := by
  sorry


@[simp]
theorem degree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).degree = 1 :=
  degree_of_c_ne_zero rfl rfl hc

@[target] theorem degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.degree ≤ 0 := by
  sorry


theorem degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree ≤ 0 :=
  degree_of_c_eq_zero rfl rfl rfl

@[target] theorem degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d ≠ 0) :
    P.toPoly.degree = 0 := by
  sorry


@[simp]
theorem degree_of_d_ne_zero' (hd : d ≠ 0) : (toPoly ⟨0, 0, 0, d⟩).degree = 0 :=
  degree_of_d_ne_zero rfl rfl rfl hd

@[target] theorem degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly.degree = ⊥ := by
  sorry


theorem degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero rfl rfl rfl rfl

@[target] theorem degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥ := by sorry


@[target] theorem natDegree_of_a_ne_zero (ha : P.a ≠ 0) : P.toPoly.natDegree = 3 := by sorry


@[simp]
theorem natDegree_of_a_ne_zero' (ha : a ≠ 0) : (toPoly ⟨a, b, c, d⟩).natDegree = 3 :=
  natDegree_of_a_ne_zero ha

@[target] theorem natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree ≤ 2 := by
  sorry


theorem natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree ≤ 2 :=
  natDegree_of_a_eq_zero rfl

@[target] theorem natDegree_of_b_ne_zero (ha : P.a = 0) (hb : P.b ≠ 0) : P.toPoly.natDegree = 2 := by
  sorry


@[simp]
theorem natDegree_of_b_ne_zero' (hb : b ≠ 0) : (toPoly ⟨0, b, c, d⟩).natDegree = 2 :=
  natDegree_of_b_ne_zero rfl hb

@[target] theorem natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree ≤ 1 := by
  sorry


theorem natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree ≤ 1 :=
  natDegree_of_b_eq_zero rfl rfl

@[target] theorem natDegree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c ≠ 0) :
    P.toPoly.natDegree = 1 := by
  sorry


@[simp]
theorem natDegree_of_c_ne_zero' (hc : c ≠ 0) : (toPoly ⟨0, 0, c, d⟩).natDegree = 1 :=
  natDegree_of_c_ne_zero rfl rfl hc

@[target] theorem natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.natDegree = 0 := by
  sorry


theorem natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0 :=
  natDegree_of_c_eq_zero rfl rfl rfl

@[target] theorem natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0 := by sorry


end Degree

/-! ### Map across a homomorphism -/


section Map

variable [Semiring S] {φ : R →+* S}

/-- Map a cubic polynomial across a semiring homomorphism. -/
/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun l := by sorry


@[target] theorem map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  sorry


end Map

end Basic

section Roots

open Multiset

/-! ### Roots over an extension -/


section Extension

variable {P : Cubic R} [CommRing R] [CommRing S] {φ : R →+* S}

/-- The roots of a cubic polynomial. -/
def roots [IsDomain R] (P : Cubic R) : Multiset R :=
  P.toPoly.roots

@[target] theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  sorry


theorem mem_roots_iff [IsDomain R] (h0 : P.toPoly ≠ 0) (x : R) :
    x ∈ P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [roots, mem_roots h0, IsRoot, toPoly]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]

@[target] theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card ≤ 3 := by
  sorry


end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F →+* K} {x y z : K}

/-! ### Roots over a splitting field -/


section Split

/-- A polynomial splits if and only if it has as many roots as its degree. -/
@[target] theorem splits_iff_card_roots {p : K[X]} :
    Splits (RingHom.id K) p ↔ Multiset.card p.roots = p.natDegree := by
  sorry


@[target] theorem splits_iff_roots_eq_three (ha : P.a ≠ 0) :
    Splits φ P.toPoly ↔ ∃ x y z : K, (map φ P).roots = {x, y, z} := by
  sorry


@[target] theorem eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    (map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) := by
  sorry


@[target] theorem eq_sum_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    map φ P =
      ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ := by
  sorry


@[target] theorem b_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.b = φ P.a * -(x + y + z) := by
  sorry


@[target] theorem c_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.c = φ P.a * (x * y + x * z + y * z) := by
  sorry


@[target] theorem d_eq_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.d = φ P.a * -(x * y * z) := by
  sorry


end Split

/-! ### Discriminant over a splitting field -/


section Discriminant

/-- The discriminant of a cubic polynomial. -/
/-- The discriminant of a cubic polynomial. -/
def disc {R : Type*} [Ring R] (P : Cubic R) : R := by sorry


@[target] theorem disc_eq_prod_three_roots (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.disc = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
  sorry


@[target] theorem disc_ne_zero_iff_roots_ne (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.disc ≠ 0 ↔ x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  sorry


@[target] theorem disc_ne_zero_iff_roots_nodup (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.disc ≠ 0 ↔ (map φ P).roots.Nodup := by
  sorry


@[target] theorem card_roots_of_disc_ne_zero [DecidableEq K] (ha : P.a ≠ 0) (h3 : (map φ P).roots = {x, y, z})
    (hd : P.disc ≠ 0) : (map φ P).roots.toFinset.card = 3 := by
  sorry


end Discriminant

end Roots

end Cubic
