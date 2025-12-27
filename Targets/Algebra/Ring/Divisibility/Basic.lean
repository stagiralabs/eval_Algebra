import VerifiedAgora.tagger
/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic

/-!
# Lemmas about divisibility in rings

Note that this file is imported by basic tactics like `linarith` and so must have only minimal
imports. Further results about divisibility in rings may be found in
`Mathlib.Algebra.Ring.Divisibility.Lemmas` which is not subject to this import constraint.
-/


variable {α β : Type*}

section Semigroup

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

@[target]
theorem map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b :=
  sorry

@[target]
theorem MulEquiv.decompositionMonoid (f : F) [DecompositionMonoid β] : DecompositionMonoid α where
  primal a b c h := by sorry

end Semigroup

section DistribSemigroup

variable [Add α] [Semigroup α]

theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])

alias Dvd.dvd.add := dvd_add

end DistribSemigroup

section Semiring
variable [Semiring α] {a b c : α} {m n : ℕ}

lemma min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b :=
  ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

end Semiring

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

@[target]
theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  sorry

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b : α}

/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[target, simp]
theorem dvd_neg : a ∣ -b ↔ a ∣ b :=
  sorry
@[target, simp]
theorem neg_dvd : -a ∣ b ↔ a ∣ b :=
  sorry

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right

alias Dvd.dvd.sub := dvd_sub

/-- If an element `a` divides another element `c` in a ring, `a` divides the sum of another element
`b` with `c` iff `a` divides `b`. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

/-- If an element `a` divides another element `b` in a ring, `a` divides the sum of `b` and another
element `c` iff `a` divides `c`. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm]; exact dvd_add_left h

/-- If an element `a` divides another element `c` in a ring, `a` divides the difference of another
element `b` with `c` iff `a` divides `b`. -/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

/-- If an element `a` divides another element `b` in a ring, `a` divides the difference of `b` and
another element `c` iff `a` divides `c`. -/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  rw [sub_eq_add_neg, dvd_add_right h, dvd_neg]

theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c, dvd_add_right h]

@[target]
theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by sorry

end NonUnitalRing

section Ring

variable [Ring α] {a b : α}

/-- An element a divides the sum a + b if and only if a divides b. -/
@[target, simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  sorry
@[target, simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  sorry
@[target, simp]
theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b :=
  sorry
@[target, simp]
theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b :=
  sorry

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α]

@[target]
theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
    k ∣ a * x - b * y := by sorry

end NonUnitalCommRing
