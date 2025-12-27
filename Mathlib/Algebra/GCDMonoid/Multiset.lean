import VerifiedAgora.tagger
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Multiset.Fold

/-!
# GCD and LCM operations on multisets

## Main definitions

- `Multiset.gcd` - the greatest common denominator of a `Multiset` of elements of a `GCDMonoid`
- `Multiset.lcm` - the least common multiple of a `Multiset` of elements of a `GCDMonoid`

## Implementation notes

TODO: simplify with a tactic and `Data.Multiset.Lattice`

## Tags

multiset, gcd
-/

namespace Multiset

variable {α : Type*} [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### LCM -/


section lcm

/-- Least common multiple of a multiset -/
def lcm (s : Multiset α) : α :=
  s.fold GCDMonoid.lcm 1

@[target] theorem lcm_zero : (0 : Multiset α).lcm = 1 := by sorry


@[target] theorem lcm_cons (a : α) (s : Multiset α) : (a ::ₘ s).lcm = GCDMonoid.lcm a s.lcm := by sorry


@[target] theorem lcm_singleton {a : α} : ({a} : Multiset α).lcm = normalize a := by sorry


@[target] theorem lcm_add (s₁ s₂ : Multiset α) : (s₁ + s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm :=
  Eq.trans (by sorry


@[target] theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  sorry


theorem dvd_lcm {s : Multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm :=
  lcm_dvd.1 dvd_rfl _ h

@[target] theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm := by sorry


@[target] theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  Multiset.induction_on s (by sorry


@[simp]
nonrec theorem lcm_eq_zero_iff [Nontrivial α] (s : Multiset α) : s.lcm = 0 ↔ (0 : α) ∈ s := by
  induction s using Multiset.induction_on with
  | empty => simp only [lcm_zero, one_ne_zero, not_mem_zero]
  | cons a s ihs => simp only [mem_cons, lcm_cons, lcm_eq_zero_iff, ihs, @eq_comm _ a]

variable [DecidableEq α]

@[simp]
theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm :=
  Multiset.induction_on s (by simp) fun a s IH ↦ by
    by_cases h : a ∈ s <;> simp [IH, h]
    unfold lcm
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)

@[target] theorem lcm_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  sorry


@[target] theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  sorry


@[target] theorem lcm_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).lcm = GCDMonoid.lcm a s.lcm := by
  sorry


end lcm

/-! ### GCD -/


section gcd

/-- Greatest common divisor of a multiset -/
def gcd (s : Multiset α) : α :=
  s.fold GCDMonoid.gcd 0

@[target] theorem gcd_zero : (0 : Multiset α).gcd = 0 := by sorry


@[target] theorem gcd_cons (a : α) (s : Multiset α) : (a ::ₘ s).gcd = GCDMonoid.gcd a s.gcd := by sorry


@[target] theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a := by sorry


@[target] theorem gcd_add (s₁ s₂ : Multiset α) : (s₁ + s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd :=
  Eq.trans (by sorry


theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])

theorem gcd_dvd {s : Multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a :=
  dvd_gcd.1 dvd_rfl _ h

theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd :=
  dvd_gcd.2 fun _ hb ↦ gcd_dvd (h hb)

@[simp]
theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  Multiset.induction_on s (by simp) fun a s _ ↦ by simp

theorem gcd_eq_zero_iff (s : Multiset α) : s.gcd = 0 ↔ ∀ x : α, x ∈ s → x = 0 := by
  constructor
  · intro h x hx
    apply eq_zero_of_zero_dvd
    rw [← h]
    apply gcd_dvd hx
  · refine s.induction_on ?_ ?_
    · simp
    intro a s sgcd h
    simp [h a (mem_cons_self a s), sgcd fun x hx ↦ h x (mem_cons_of_mem hx)]

@[target] theorem gcd_map_mul (a : α) (s : Multiset α) : (s.map (a * ·)).gcd = normalize a * s.gcd := by
  sorry


section

variable [DecidableEq α]

@[target] theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd :=
  Multiset.induction_on s (by sorry


@[target] theorem gcd_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  sorry


@[simp]
theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add]
  simp

@[target] theorem gcd_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).gcd = GCDMonoid.gcd a s.gcd := by
  sorry


end

@[target] theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map (s.gcd * ·) ∧ t.gcd = 1 := by
  sorry


theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map (s.gcd * ·) ∧ t.gcd = 1 := by
  classical
    by_cases h : ∀ x ∈ s, x = (0 : α)
    · use replicate (card s) 1
      rw [map_replicate, eq_replicate, mul_one, s.gcd_eq_zero_iff.2 h, ← nsmul_singleton,
    ← gcd_dedup, dedup_nsmul (card_pos.2 hs).ne', dedup_singleton, gcd_singleton]
      exact ⟨⟨rfl, h⟩, normalize_one⟩
    · choose f hf using @gcd_dvd _ _ _ s
      push_neg at h
      refine ⟨s.pmap @f fun _ ↦ id, ?_, extract_gcd' s _ h ?_⟩ <;>
      · rw [map_pmap]
        conv_lhs => rw [← s.map_id, ← s.pmap_eq_map _ _ fun _ ↦ id]
        congr with (x hx)
        rw [id, ← hf hx]

end gcd

end Multiset
