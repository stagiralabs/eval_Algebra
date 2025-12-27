import VerifiedAgora.tagger
/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Choose.Sum

/-!
# Characteristic of semirings
-/

assert_not_exists Algebra LinearMap orderOf

open Finset

variable {R S : Type*}

namespace Commute

variable [Semiring R] {p : ℕ} (hp : p.Prime) {x y : R}
include hp

protected theorem add_pow_prime_pow_eq (h : Commute x y) (n : ℕ) :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) := by
  trans x ^ p ^ n + y ^ p ^ n + ∑ k ∈ Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * (p ^ n).choose k
  · simp_rw [h.add_pow, ← Nat.Ico_zero_eq_range, Nat.Ico_succ_right, Icc_eq_cons_Ico (zero_le _),
      Finset.sum_cons, Ico_eq_cons_Ioo (pow_pos hp.pos _), Finset.sum_cons, tsub_self, tsub_zero,
      pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one, one_mul, ← add_assoc]
  · congr 1
    simp_rw [Finset.mul_sum, Nat.cast_comm, mul_assoc _ _ (p : R), ← Nat.cast_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_Ioo] at hi
    rw [Nat.div_mul_cancel (hp.dvd_choose_pow hi.1.ne' hi.2.ne)]

protected theorem add_pow_prime_eq (h : Commute x y) :
    (x + y) ^ p =
      x ^ p + y ^ p + p * ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) := by
  simpa using h.add_pow_prime_pow_eq hp 1

protected theorem exists_add_pow_prime_pow_eq (h : Commute x y) (n : ℕ) :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
  ⟨_, h.add_pow_prime_pow_eq hp n⟩

protected theorem exists_add_pow_prime_eq (h : Commute x y) :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
  ⟨_, h.add_pow_prime_eq hp⟩

end Commute

section CommSemiring

variable [CommSemiring R] {p : ℕ} (hp : p.Prime) (x y : R) (n : ℕ)
include hp

@[target]
theorem add_pow_prime_pow_eq :
    (x + y) ^ p ^ n =
      x ^ p ^ n + y ^ p ^ n +
        p * ∑ k ∈ Finset.Ioo 0 (p ^ n), x ^ k * y ^ (p ^ n - k) * ↑((p ^ n).choose k / p) :=
  sorry

theorem add_pow_prime_eq :
    (x + y) ^ p =
      x ^ p + y ^ p + p * ∑ k ∈ Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(p.choose k / p) :=
  (Commute.all x y).add_pow_prime_eq hp

theorem exists_add_pow_prime_pow_eq :
    ∃ r, (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n + p * r :=
  (Commute.all x y).exists_add_pow_prime_pow_eq hp n

theorem exists_add_pow_prime_eq :
    ∃ r, (x + y) ^ p = x ^ p + y ^ p + p * r :=
  (Commute.all x y).exists_add_pow_prime_eq hp

end CommSemiring

section Semiring
variable [Semiring R] {x y : R} (p n : ℕ)

section ExpChar
variable [hR : ExpChar R p]

@[target]
lemma add_pow_expChar_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p := by sorry

@[target]
lemma add_pow_expChar_pow_of_commute (h : Commute x y) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by sorry

lemma add_pow_eq_mul_pow_add_pow_div_expChar_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) := by
  rw [← add_pow_expChar_of_commute _ h, ← pow_mul, ← pow_add, Nat.mod_add_div]

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

lemma add_pow_char_of_commute (h : Commute x y) : (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_expChar_of_commute _ h

@[target]
lemma add_pow_char_pow_of_commute (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  sorry

lemma add_pow_eq_mul_pow_add_pow_div_char_of_commute (h : Commute x y) :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ h

end CharP
end Semiring

section CommSemiring
variable [CommSemiring R] (x y : R) (p n : ℕ)

section ExpChar
variable [hR : ExpChar R p]

@[target]
lemma add_pow_expChar : (x + y) ^ p = x ^ p + y ^ p := sorry

lemma add_pow_expChar_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_expChar_pow_of_commute _ _ <| .all ..

lemma add_pow_eq_mul_pow_add_pow_div_expChar :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  add_pow_eq_mul_pow_add_pow_div_expChar_of_commute _ _ <| .all ..

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

@[target]
lemma add_pow_char : (x + y) ^ p = x ^ p + y ^ p := sorry
lemma add_pow_char_pow : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := add_pow_expChar_pow ..

@[target]
lemma add_pow_eq_mul_pow_add_pow_div_char :
    (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p) :=
  sorry

@[deprecated (since := "2024-10-21")]
alias add_pow_eq_add_pow_mod_mul_pow_add_pow_div := add_pow_eq_mul_pow_add_pow_div_char

end CharP
end CommSemiring

section Ring
variable [Ring R] {x y : R} (p n : ℕ)

section ExpChar
variable [hR : ExpChar R p]
include hR

lemma sub_pow_expChar_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_of_commute _ (h.sub_left rfl)]

lemma sub_pow_expChar_pow_of_commute (h : Commute x y) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  simp [eq_sub_iff_add_eq, ← add_pow_expChar_pow_of_commute _ _ (h.sub_left rfl)]

@[target]
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) := by sorry

variable (R)

@[target]
lemma neg_one_pow_expChar : (-1 : R) ^ p = -1 := by sorry

@[target]
lemma neg_one_pow_expChar_pow : (-1 : R) ^ p ^ n = -1 := by sorry

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

@[target]
lemma sub_pow_char_of_commute (h : Commute x y) : (x - y) ^ p = x ^ p - y ^ p :=
  sorry

@[target]
lemma sub_pow_char_pow_of_commute (h : Commute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sorry

variable (R)

lemma neg_one_pow_char : (-1 : R) ^ p = -1 := neg_one_pow_expChar ..

lemma neg_one_pow_char_pow : (-1 : R) ^ p ^ n = -1 := neg_one_pow_expChar_pow ..

lemma sub_pow_eq_mul_pow_sub_pow_div_char_of_commute (h : Commute x y) :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar_of_commute _ _ h

end CharP
end Ring

section CommRing
variable [CommRing R] (x y : R) (n : ℕ) {p : ℕ}

section ExpChar
variable [hR : ExpChar R p]

lemma sub_pow_expChar : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar_of_commute _ <| .all ..

lemma sub_pow_expChar_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_expChar_pow_of_commute _ _ <| .all ..

@[target]
lemma sub_pow_eq_mul_pow_sub_pow_div_expChar :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sorry

end ExpChar

section CharP
variable [hp : Fact p.Prime] [CharP R p]

lemma sub_pow_char : (x - y) ^ p = x ^ p - y ^ p := sub_pow_expChar ..
@[target]
lemma sub_pow_char_pow : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := sorry

lemma sub_pow_eq_mul_pow_sub_pow_div_char :
    (x - y) ^ n = (x - y) ^ (n % p) * (x ^ p - y ^ p) ^ (n / p) :=
  sub_pow_eq_mul_pow_sub_pow_div_expChar ..

end CharP

lemma Nat.Prime.dvd_add_pow_sub_pow_of_dvd (hpri : p.Prime) {r : R} (h₁ : r ∣ x ^ p)
    (h₂ : r ∣ p * x) : r ∣ (x + y) ^ p - y ^ p := by
  rw [add_pow_prime_eq hpri, add_right_comm, add_assoc, add_sub_assoc, add_sub_cancel_right]
  apply dvd_add h₁ (h₂.trans <| mul_dvd_mul_left _ <| Finset.dvd_sum _)
  simp only [Finset.mem_Ioo, and_imp, mul_assoc]
  intro i hi0 _
  exact dvd_mul_of_dvd_left (dvd_rfl.pow hi0.ne') _

end CommRing


namespace CharP

section

variable (R) [NonAssocRing R]

/-- The characteristic of a finite ring cannot be zero. -/
@[target]
theorem char_ne_zero_of_finite (p : ℕ) [CharP R p] [Finite R] : p ≠ 0 := by sorry

@[target]
theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 :=
  sorry

section Ring

variable (R) [Ring R] [NoZeroDivisors R] [Nontrivial R] [Finite R]

theorem char_is_prime (p : ℕ) [CharP R p] : p.Prime :=
  Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_finite R p)

@[target]
lemma prime_ringChar : Nat.Prime (ringChar R) := by sorry

end Ring
end CharP

/-! ### The Frobenius automorphism -/

section frobenius
section CommSemiring
variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →* S) (g : R →+* S) (p m n : ℕ)
  [ExpChar R p] [ExpChar S p] (x y : R)

open ExpChar

variable (R) in
/-- The frobenius map `x ↦ x ^ p`. -/
def frobenius : R →+* R where
  __ := powMonoidHom p
  map_zero' := zero_pow (expChar_pos R p).ne'
  map_add' _ _ := add_pow_expChar ..

variable (R) in
/-- The iterated frobenius map `x ↦ x ^ p ^ n`. -/
def iterateFrobenius : R →+* R where
  __ := powMonoidHom (p ^ n)
  map_zero' := zero_pow (expChar_pow_pos R p n).ne'
  map_add' _ _ := add_pow_expChar_pow ..


@[target]
lemma frobenius_def : frobenius R p x = x ^ p := sorry

@[target]
lemma iterateFrobenius_def : iterateFrobenius R p n x = x ^ p ^ n := sorry

@[target]
lemma iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n := sorry

variable (R)

@[target]
lemma coe_iterateFrobenius : iterateFrobenius R p n = (frobenius R p)^[n] :=
  sorry

@[target]
lemma iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p := by sorry

@[target, simp]
lemma iterateFrobenius_one : iterateFrobenius R p 1 = frobenius R p :=
  sorry

@[target]
lemma iterateFrobenius_zero_apply : iterateFrobenius R p 0 x = x := by sorry

@[simp]
lemma iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R :=
  RingHom.ext (iterateFrobenius_zero_apply R p)

@[target]
lemma iterateFrobenius_add_apply :
    iterateFrobenius R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x) := by sorry

lemma iterateFrobenius_add :
    iterateFrobenius R p (m + n) = (iterateFrobenius R p m).comp (iterateFrobenius R p n) :=
  RingHom.ext (iterateFrobenius_add_apply R p m n)

@[target]
lemma iterateFrobenius_mul_apply :
    iterateFrobenius R p (m * n) x = (iterateFrobenius R p m)^[n] x := by sorry

@[target]
lemma coe_iterateFrobenius_mul : iterateFrobenius R p (m * n) = (iterateFrobenius R p m)^[n] :=
  sorry

variable {R}

lemma frobenius_mul : frobenius R p (x * y) = frobenius R p x * frobenius R p y :=
  map_mul (frobenius R p) x y

@[target]
lemma frobenius_one : frobenius R p 1 = 1 := sorry

lemma MonoidHom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) := map_pow f x p
lemma RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) := map_pow g x p

lemma MonoidHom.map_iterate_frobenius (n : ℕ) :
    f ((frobenius R p)^[n] x) = (frobenius S p)^[n] (f x) :=
  Function.Semiconj.iterate_right (f.map_frobenius p) n x

lemma RingHom.map_iterate_frobenius (n : ℕ) :
    g ((frobenius R p)^[n] x) = (frobenius S p)^[n] (g x) :=
  g.toMonoidHom.map_iterate_frobenius p x n

@[target]
lemma MonoidHom.iterate_map_frobenius (f : R →* R) (p : ℕ) [ExpChar R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
  sorry

@[target]
lemma RingHom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [ExpChar R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) := sorry

@[target]
lemma list_sum_pow_char (l : List R) : l.sum ^ p = (l.map (· ^ p : R → R)).sum :=
  sorry

@[target]
lemma multiset_sum_pow_char (s : Multiset R) : s.sum ^ p = (s.map (· ^ p : R → R)).sum :=
  sorry

@[target]
lemma sum_pow_char {ι : Type*} (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p :=
  sorry

variable (n : ℕ)

@[target]
lemma list_sum_pow_char_pow (l : List R) : l.sum ^ p ^ n = (l.map (· ^ p ^ n : R → R)).sum :=
  sorry

@[target]
lemma multiset_sum_pow_char_pow (s : Multiset R) :
    s.sum ^ p ^ n = (s.map (· ^ p ^ n : R → R)).sum := sorry

@[target]
lemma sum_pow_char_pow {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ p ^ n = ∑ i ∈ s, f i ^ p ^ n := sorry

end CommSemiring

section CommRing
variable [CommRing R] (p : ℕ) [ExpChar R p] (x y : R)

@[target]
lemma frobenius_neg : frobenius R p (-x) = -frobenius R p x := sorry

lemma frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y := map_sub ..

end CommRing
end frobenius
