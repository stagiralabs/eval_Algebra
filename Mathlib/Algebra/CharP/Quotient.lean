import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Characteristic of quotients rings
-/


universe u v

namespace CharP

@[target] theorem quotient (R : Type u) [CommRing R] (p : ℕ) [hp1 : Fact p.Prime] (hp2 : ↑p ∈ nonunits R) :
    CharP (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p := by sorry


/-- If an ideal does not contain any coercions of natural numbers other than zero, then its quotient
inherits the characteristic of the underlying ring. -/
theorem quotient' {R : Type*} [CommRing R] (p : ℕ) [CharP R p] (I : Ideal R)
    (h : ∀ x : ℕ, (x : R) ∈ I → (x : R) = 0) : CharP (R ⧸ I) p :=
  ⟨fun x => by
    rw [← cast_eq_zero_iff R p x, ← map_natCast (Ideal.Quotient.mk I)]
    refine Ideal.Quotient.eq.trans (?_ : ↑x - 0 ∈ I ↔ _)
    rw [sub_zero]
    exact ⟨h x, fun h' => h'.symm ▸ I.zero_mem⟩⟩

/-- `CharP.quotient'` as an `Iff`. -/
/-- `CharP.quotient'` as an `Iff`. -/
@[target] theorem quotient_iff {R : Type*} [CommRing R] (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  sorry


/-- `CharP.quotient_iff`, but stated in terms of inclusions of ideals. -/
theorem quotient_iff_le_ker_natCast {R : Type*} [CommRing R] (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) := by
  rw [CharP.quotient_iff, RingHom.ker_eq_comap_bot]; rfl

end CharP

theorem Ideal.Quotient.index_eq_zero {R : Type*} [CommRing R] (I : Ideal R) :
    (↑I.toAddSubgroup.index : R ⧸ I) = 0 := by
  rw [AddSubgroup.index, Nat.card_eq]
  split_ifs with hq; swap
  · simp
  letI : Fintype (R ⧸ I) := @Fintype.ofFinite _ hq
  exact Nat.cast_card_eq_zero (R ⧸ I)
