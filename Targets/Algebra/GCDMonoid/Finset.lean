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
def lcm (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.lcm 1 f

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem lcm_def : s.lcm f = (s.1.map f).lcm :=
  rfl

@[simp]
theorem lcm_empty : (∅ : Finset β).lcm f = 1 :=
  fold_empty

@[target, simp]
theorem lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ ∀ b ∈ s, f b ∣ a := by sorry

theorem lcm_dvd {a : α} : (∀ b ∈ s, f b ∣ a) → s.lcm f ∣ a :=
  lcm_dvd_iff.2

@[target]
theorem dvd_lcm {b : β} (hb : b ∈ s) : f b ∣ s.lcm f :=
  sorry

@[target, simp]
theorem lcm_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).lcm f = GCDMonoid.lcm (f b) (s.lcm f) := by sorry

@[target, simp]
theorem lcm_singleton {b : β} : ({b} : Finset β).lcm f = normalize (f b) :=
  sorry

@[target, local simp] -- This will later be provable by other `simp` lemmas.
theorem normalize_lcm : normalize (s.lcm f) = s.lcm f := by sorry

theorem lcm_union [DecidableEq β] : (s₁ ∪ s₂).lcm f = GCDMonoid.lcm (s₁.lcm f) (s₂.lcm f) :=
  Finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm])
    fun a s _ ih ↦ by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]

@[target]
theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.lcm f = s₂.lcm g := by sorry

@[target]
theorem lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g :=
  sorry

@[target]
theorem lcm_mono (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f :=
  sorry

theorem lcm_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).lcm f = s.lcm (f ∘ g) := by
  classical induction s using Finset.induction <;> simp [*]

@[target]
theorem lcm_eq_lcm_image [DecidableEq α] : s.lcm f = (s.image f).lcm id :=
  sorry

@[target]
theorem lcm_eq_zero_iff [Nontrivial α] : s.lcm f = 0 ↔ 0 ∈ f '' s := by sorry

end lcm

/-! ### gcd -/


section gcd

/-- Greatest common divisor of a finite set -/
def gcd (s : Finset β) (f : β → α) : α :=
  s.fold GCDMonoid.gcd 0 f

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_def : s.gcd f = (s.1.map f).gcd :=
  rfl

@[target, simp]
theorem gcd_empty : (∅ : Finset β).gcd f = 0 :=
  sorry

theorem dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ ∀ b ∈ s, a ∣ f b := by
  apply Iff.trans Multiset.dvd_gcd
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb ↦ k _ _ hb rfl, fun k a' b hb h ↦ h ▸ k _ hb⟩

theorem gcd_dvd {b : β} (hb : b ∈ s) : s.gcd f ∣ f b :=
  dvd_gcd_iff.1 dvd_rfl _ hb

@[target]
theorem dvd_gcd {a : α} : (∀ b ∈ s, a ∣ f b) → a ∣ s.gcd f :=
  sorry

@[simp]
theorem gcd_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) := by
  by_cases h : b ∈ s
  · rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)]
  apply fold_insert h

@[target, simp]
theorem gcd_singleton {b : β} : ({b} : Finset β).gcd f = normalize (f b) :=
  sorry

@[local simp] -- This will later be provable by other `simp` lemmas.
theorem normalize_gcd : normalize (s.gcd f) = s.gcd f := by simp [gcd_def]

@[target]
theorem gcd_union [DecidableEq β] : (s₁ ∪ s₂).gcd f = GCDMonoid.gcd (s₁.gcd f) (s₂.gcd f) :=
  sorry

theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.gcd f = s₂.gcd g := by
  subst hs
  exact Finset.fold_congr hfg

@[target]
theorem gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g :=
  sorry

theorem gcd_mono (h : s₁ ⊆ s₂) : s₂.gcd f ∣ s₁.gcd f :=
  dvd_gcd fun _ hb ↦ gcd_dvd (h hb)

@[target]
theorem gcd_image [DecidableEq β] {g : γ → β} (s : Finset γ) :
    (s.image g).gcd f = s.gcd (f ∘ g) := by sorry

@[target]
theorem gcd_eq_gcd_image [DecidableEq α] : s.gcd f = (s.image f).gcd id :=
  sorry

@[target]
theorem gcd_eq_zero_iff : s.gcd f = 0 ↔ ∀ x : β, x ∈ s → f x = 0 := by sorry

@[target]
theorem gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β ↦ f x = 0] :
    s.gcd f = (s.filter fun x ↦ f x ≠ 0).gcd f := by sorry

theorem extract_gcd' (f g : β → α) (hs : ∃ x, x ∈ s ∧ f x ≠ 0)
    (hg : ∀ b ∈ s, f b = s.gcd f * g b) : s.gcd g = 1 :=
  ((@mul_right_eq_self₀ _ _ (s.gcd f) _).1 <| by
        conv_lhs => rw [← normalize_gcd, ← gcd_mul_left, ← gcd_congr rfl hg]).resolve_right <| by
    contrapose! hs
    exact gcd_eq_zero_iff.1 hs

@[target]
theorem extract_gcd (f : β → α) (hs : s.Nonempty) :
    ∃ g : β → α, (∀ b ∈ s, f b = s.gcd f * g b) ∧ s.gcd g = 1 := by sorry

variable [Div α] [MulDivCancelClass α] {f : ι → α} {s : Finset ι} {i : ι}

/-- Given a nonempty Finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
lemma gcd_div_eq_one (his : i ∈ s) (hfi : f i ≠ 0) : s.gcd (fun j ↦ f j / s.gcd f) = 1 := by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨i, his⟩
  refine (Finset.gcd_congr rfl fun a ha ↦ ?_).trans hg
  rw [he a ha, mul_div_cancel_left₀]
  exact mt Finset.gcd_eq_zero_iff.1 fun h ↦ hfi <| h i his

lemma gcd_div_id_eq_one {s : Finset α} {a : α} (has : a ∈ s) (ha : a ≠ 0) :
    s.gcd (fun b ↦ b / s.gcd id) = 1 := gcd_div_eq_one has ha

end gcd

end Finset

namespace Finset

section IsDomain

variable [CommRing α] [IsDomain α] [NormalizedGCDMonoid α]

@[target]
theorem gcd_eq_of_dvd_sub {s : Finset β} {f g : β → α} {a : α}
    (h : ∀ x : β, x ∈ s → a ∣ f x - g x) :
    GCDMonoid.gcd a (s.gcd f) = GCDMonoid.gcd a (s.gcd g) := by sorry

end IsDomain

end Finset
