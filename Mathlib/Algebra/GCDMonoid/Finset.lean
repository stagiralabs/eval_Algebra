import VerifiedAgora.tagger
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.GCDMonoid.Multiset

/-!
# GCD and LCM operations on finsets

## Main definitions

- `Finset.gcd` - the greatest common denominator of a `Finset` of elements of a `GCDMonoid`
- `Finset.lcm` - the least common multiple of a `Finset` of elements of a `GCDMonoid`

## Implementation notes

Many of the proofs use the lemmas `gcd_def` and `lcm_def`, which relate `Finset.gcd`
and `Finset.lcm` to `Multiset.gcd` and `Multiset.lcm`.

TODO: simplify with a tactic and `Data.Finset.Lattice`

## Tags

finset, gcd
-/

variable {ι α β γ : Type*}

namespace Finset

open Multiset

variable [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]

/-! ### lcm -/


section lcm

/-- Least common multiple of a finite set -/
/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm (x y : R) : R := by sorry


variable {s s₁ s₂ : Finset β} {f : β → α}

@[target] theorem lcm_def : s.lcm f = (s.1.map f).lcm := by sorry


@[target] theorem lcm_empty : (∅ : Finset β).lcm f = 1 := by sorry


@[simp]
theorem lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ ∀ b ∈ s, f b ∣ a := by
  apply Iff.trans Multiset.lcm_dvd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb ↦ k _ _ hb rfl, fun k a' b hb h ↦ h ▸ k _ hb⟩

@[target] theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  sorry


@[target] theorem dvd_lcm {s : Multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm := by sorry


@[target] theorem lcm_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f) := by
  sorry


@[simp]
theorem lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b) :=
  Multiset.lcm_singleton

@[local simp] -- This will later be provable by other `simp` lemmas.
@[target] theorem normalize_lcm (s : Multiset α) : normalize s.lcm = s.lcm :=
  Multiset.induction_on s (by sorry


@[target] theorem lcm_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).lcm = GCDMonoid.lcm s₁.lcm s₂.lcm := by
  sorry


@[target] theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.lcm f = s₂.lcm g := by
  sorry


@[target] theorem lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g := by sorry


@[target] theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm := by sorry


@[target] theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  sorry

  classical induction s using Finset.induction <;> simp [*]

@[target] theorem lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id := by sorry


theorem lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ 0 ∈ f '' s := by
  simp only [Multiset.mem_map, lcm_def, Multiset.lcm_eq_zero_iff, Set.mem_image, mem_coe, ←
    Finset.mem_def]

end lcm

/-! ### gcd -/


section gcd

/-- Greatest common divisor of a finite set -/
def gcd (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.gcd 0 f

variable {s s₁ s₂ : Finset β} {f : β → α}

@[target] theorem gcd_def : s.gcd f = (s.1.map f).gcd := by sorry


@[target] theorem gcd_empty : (∅ : Finset β).gcd f = 0 := by sorry


theorem dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ ∀ b ∈ s, a ∣ f b := by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb ↦ k _ _ hb rfl, fun k a' b hb h ↦ h ▸ k _ hb⟩

@[target] theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  GCD.induction a b
    (fun b => by
      sorry


theorem dvd_gcd {a : α} : (∀ b ∈ s, a ∣ f b) → a ∣ s.gcd f :=
  dvd_gcd_iff.2

@[target] theorem gcd_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) := by
  sorry


@[target] theorem gcd_singleton {a : α} : ({a} : Multiset α).gcd = normalize a := by sorry


@[local simp] -- This will later be provable by other `simp` lemmas.
@[target] theorem normalize_gcd (s : Multiset α) : normalize s.gcd = s.gcd :=
  Multiset.induction_on s (by sorry


@[target] theorem gcd_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).gcd = GCDMonoid.gcd s₁.gcd s₂.gcd := by
  sorry


@[target] theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  sorry


@[target] theorem gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g := by sorry


@[target] theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd := by sorry


@[target] theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by
  sorry

  classical induction s using Finset.induction <;> simp [*]

@[target] theorem gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id := by sorry


protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by sorry


@[target] theorem gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β ↦ f x = 0] :
    s.gcd f = (s.filter fun x ↦ f x ≠ 0).gcd f := by
  sorry

  classical
    trans ((s.filter fun x ↦ f x = 0) ∪ s.filter fun x ↦ (f x ≠ 0)).gcd f
    · rw [filter_union_filter_neg_eq]
    rw [gcd_union]
    refine Eq.trans (?_ : _ = GCDMonoid.gcd (0 : α) ?_) (?_ : GCDMonoid.gcd (0 : α) _ = _)
    · exact (gcd (filter (fun x => (f x ≠ 0)) s) f)
    · refine congr (congr rfl <| s.induction_on ?_ ?_) (by simp)
      · simp
      · intro a s _ h
        rw [filter_insert]
        split_ifs with h1 <;> simp [h, h1]
    simp only [gcd_zero_left, normalize_gcd]

nonrec theorem gcd_mul_left {a : α} : (s.gcd fun x ↦ a * f x) = normalize a * s.gcd f := by
  classical
    refine s.induction_on ?_ ?_
    · simp
    · intro b t _ h
      rw [gcd_insert, gcd_insert, h, ← gcd_mul_left]
      apply ((normalize_associated a).mul_right _).gcd_eq_right

nonrec theorem gcd_mul_right {a : α} : (s.gcd fun x ↦ f x * a) = s.gcd f * normalize a := by
  classical
    refine s.induction_on ?_ ?_
    · simp
    · intro b t _ h
      rw [gcd_insert, gcd_insert, h, ← gcd_mul_right]
      apply ((normalize_associated a).mul_left _).gcd_eq_right

@[target] theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map (s.gcd * ·) ∧ t.gcd = 1 := by
  sorry


theorem extract_gcd (f : β → α) (hs : s.Nonempty) :
    ∃ g : β → α, (∀ b ∈ s, f b = s.gcd f * g b) ∧ s.gcd g = 1 := by
  classical
    by_cases h : ∀ x ∈ s, f x = (0 : α)
    · refine ⟨fun _ ↦ 1, fun b hb ↦ by rw [h b hb, gcd_eq_zero_iff.2 h, mul_one], ?_⟩
      rw [gcd_eq_gcd_image, image_const hs, gcd_singleton, id, normalize_one]
    · choose g' hg using @gcd_dvd _ _ _ _ s f
      push_neg at h
      refine ⟨fun b ↦ if hb : b ∈ s then g' hb else 0, fun b hb ↦ ?_,
          extract_gcd' f _ h fun b hb ↦ ?_⟩
      · simp only [hb, hg, dite_true]
      rw [dif_pos hb, hg hb]

variable [Div α] [MulDivCancelClass α] {f : ι → α} {s : Finset ι} {i : ι}

/-- Given a nonempty Finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
/-- Given a nonempty Finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
@[target] lemma gcd_div_eq_one (his : i ∈ s) (hfi : f i ≠ 0) : s.gcd (fun j ↦ f j / s.gcd f) = 1 := by
  sorry


@[target] lemma gcd_div_id_eq_one {s : Finset α} {a : α} (has : a ∈ s) (ha : a ≠ 0) :
    s.gcd (fun b ↦ b / s.gcd id) = 1 := by sorry


end gcd

end Finset

namespace Finset

section IsDomain

variable [CommRing α] [IsDomain α] [NormalizedGCDMonoid α]

@[target] theorem gcd_eq_of_dvd_sub {s : Finset β} {f g : β → α} {a : α}
    (h : ∀ x : β, x ∈ s → a ∣ f x - g x) :
    GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g) := by
  sorry

  classical
    revert h
    refine s.induction_on ?_ ?_
    · simp
    intro b s _ hi h
    rw [gcd_insert, gcd_insert, gcd_comm (f b), ← gcd_assoc,
      hi fun x hx ↦ h _ (mem_insert_of_mem hx), gcd_comm a, gcd_assoc,
      gcd_comm a (GCDMonoid.gcd _ _), gcd_comm (g b), gcd_assoc _ _ a, gcd_comm _ a]
    exact congr_arg _ (gcd_eq_of_dvd_sub_right (h _ (mem_insert_self _ _)))

end IsDomain

end Finset
