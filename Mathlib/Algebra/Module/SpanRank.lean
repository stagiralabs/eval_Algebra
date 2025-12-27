import VerifiedAgora.tagger
/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Xuchun Li, Jingting Wang, Andrew Yang
-/
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Minimum Cardinality of generating set of a submodule

In this file, we define the minimum cardinality of a generating set for a submodule, which is
implemented as `spanFinrank` and `spanRank`.
`spanFinrank` takes value in `ℕ` and equals `0` when no finite generating set exists.
`spanRank` takes value as a cardinal.

## Main Definitions

* `spanFinrank`: The minimum cardinality of a generating set of a submodule as a natural
  number. If no finite generating set exists, it is defined to be `0`.
* `spanRank`: The minimum cardinality of a generating set of a submodule as a cardinal.
* `FG.generators`: For a finitely generated submodule, get a set of generating elements with minimal
  cardinality.

## Main Results

* `FG.exists_span_set_card_eq_spanFinrank` : Any submodule has a generating set of cardinality equal
  to `spanRank`.

* `rank_eq_spanRank_of_free` : For a ring `R` (not necessarily commutative) satisfying
  `StrongRankCondition R`, if `M` is a free `R`-module, then the `spanRank` of `M` equals to the
   rank of M.

* `rank_le_spanRank` : For a ring `R` (not necessarily commutative) satisfying
  `StrongRankCondition R`, if `M` is an `R`-module, then the `spanRank` of `M` is less than or equal
  to the rank of M.

## Tags
submodule, generating subset, span rank

## Remark
Note that the corresponding API - `Module.rank` is only defined for a module rather than a
submodule, so there is some asymmetry here. Further refactoring might be needed if this difference
creates a friction later on.
-/

namespace Submodule

section Defs

universe u

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

open Cardinal

/-- The minimum cardinality of a generating set of a submodule as a cardinal. -/
noncomputable def spanRank (p : Submodule R M) : Cardinal := ⨅ (s : {s : Set M // span R s = p}), #s

/-- The minimum cardinality of a generating set of a submodule as a natural number. If no finite
  generating set exists, the span rank is defined to be `0`. -/
noncomputable def spanFinrank (p : Submodule R M) : ℕ := (spanRank p).toNat

instance (p : Submodule R M) : Nonempty {s : Set M // span R s = p} := ⟨⟨p, by simp⟩⟩

lemma spanRank_toENat_eq_iInf_encard (p : Submodule R M) : p.spanRank.toENat =
    (⨅ (s : Set M) (_ : span R s = p), s.encard) := by
  rw [spanRank]
  apply le_antisymm
  · refine le_iInf₂ (fun s hs ↦ ?_)
    rw [Set.encard, ENat.card]
    exact toENat.monotone' (ciInf_le' _ (⟨s, hs⟩ : {s : Set M // span R s = p}))
  · have := congrFun toENat_comp_ofENat.{u}.symm (⨅ (s : Set M) (_ : span R s = p), s.encard)
    rw [id_eq] at this; rw [this]
    refine toENat.monotone' (le_ciInf fun s ↦ ?_)
    have : ofENat.{u} (⨅ (s' : Set M), ⨅ (_ : span R s' = p), s'.encard) ≤ ofENat s.1.encard :=
      ofENatHom.monotone' (le_trans (ciInf_le' _ s.1) (ciInf_le' _ s.2))
    apply le_trans this
    rw [Set.encard, ENat.card]
    exact Cardinal.ofENat_toENat_le _

lemma spanRank_toENat_eq_iInf_finset_card (p : Submodule R M) :
    p.spanRank.toENat =
      ⨅ (s : {s : Set M // s.Finite ∧ span R s = p}), (s.2.1.toFinset.card : ℕ∞) := by
  rw [spanRank_toENat_eq_iInf_encard]
  rcases (eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤) with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s ↦ False.elim (((Set.encard_ne_top_iff (s := s.1)).mpr s.2.1) (h1 s.1 s.2.2))
  · apply le_antisymm
    · refine le_iInf (fun s ↦ (le_trans (iInf₂_le s.1 s.2.2) ?_))
      rw [s.2.1.encard_eq_coe_toFinset_card]
    · refine le_iInf (fun s ↦ (le_iInf (fun h ↦ ?_)))
      by_cases hs : s.Finite
      · apply @le_trans _ _ _ (hs.toFinset.card : ℕ∞) _
        · apply iInf_le (fun (s : {s : Set M // s.Finite ∧ span R s = p})
            ↦ (s.2.1.toFinset.card : ℕ∞)) ⟨s, ⟨hs, h⟩⟩
        · rw [hs.encard_eq_coe_toFinset_card]
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _

lemma spanFinrank_eq_iInf (p : Submodule R M) :
    p.spanFinrank = ⨅ (s : {s : Set M // s.Finite ∧ span R s = p}), s.2.1.toFinset.card := by
  simp [spanFinrank, Cardinal.toNat, spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

/-- A submodule's `spanRank` is finite if and only if it is finitely generated. -/
/-- A submodule's `spanRank` is finite if and only if it is finitely generated. -/
@[target] lemma spanRank_finite_iff_fg {p : Submodule R M} : p.spanRank < aleph0 ↔ p.FG := by
  sorry


/-- A submodule is finitely generated if and only if its `spanRank` is equal to its `spanFinrank`.
-/
/-- A submodule is finitely generated if and only if its `spanRank` is equal to its `spanFinrank`.
-/
@[target] lemma fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG := by
  sorry


@[target] lemma spanRank_span_le_card (s : Set M) : (Submodule.span R s).spanRank ≤ #s := by
  sorry


@[target] lemma spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) :
    (span R s).spanFinrank ≤ s.ncard := by
  sorry


/-- Constructs a generating set with cardinality equal to the `spanRank` of the submodule -/
/-- Constructs a generating set with cardinality equal to the `spanRank` of the submodule -/
@[target] theorem exists_span_set_card_eq_spanRank (p : Submodule R M) :
    ∃ s : Set M, #s = p.spanRank ∧ span R s = p := by
  sorry


/-- Constructs a generating set with cardinality equal to the `spanFinrank` of the submodule when
  the submodule is finitely generated. -/
theorem FG.exists_span_set_encard_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    ∃ s : Set M, s.encard = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard, ENat.card, spanFinrank, hs₁, this]
  simp

/-- For a finitely generated submodule, its spanRank is less than or equal to a cardinal `a`
  if and only if there is a generating subset with cardinality less than or equal to `a`. -/
lemma FG.spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank ≤ a ↔ ∃ s : Set M, #s ≤ a ∧ span R s = p := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact (fun ⟨s, ⟨hs₁, hs₂⟩⟩ ↦ hs₂.symm ▸ (le_trans (spanRank_span_le_card s) hs₁))

@[target] lemma spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  sorry


@[simp]
lemma spanRank_bot : (⊥ : Ideal R).spanRank = 0 := Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

/-- Generating elements for the submodule of minimum cardinality. -/
noncomputable def generators (p : Submodule R M) : Set M :=
  Classical.choose (exists_span_set_card_eq_spanRank p)

lemma generators_card (p : Submodule R M) : #(generators p) = spanRank p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).1

lemma FG.generators_ncard {p : Submodule R M} (h : p.FG) :
    (generators p).ncard = spanFinrank p := by
  rw [← Nat.cast_inj (R := Cardinal), ← fg_iff_spanRank_eq_spanFinrank.mpr h, Set.ncard, Set.encard,
     ENat.card, generators_card, toNat_toENat, ← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm

/-- The span of the generators equals the submodule. -/
/-- The span of the generators equals the submodule. -/
@[target] lemma span_generators (p : Submodule R M) : span R (generators p) = p := by sorry


/-- The elements of the generators are in the submodule. -/
lemma FG.generators_mem (p : Submodule R M) : generators p ⊆ p := by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)

@[target] lemma spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank ≤ p.spanRank + q.spanRank := by
  sorry


end Defs

section rank

open Cardinal

universe u v w

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

lemma Basis.mk_eq_spanRank [RankCondition R] {ι : Type*} (v : Basis ι R M) :
    #(Set.range v) = (⊤ : Submodule R M).spanRank := by
  rw [spanRank]
  let x : {s : Set M // span R s = ⊤} := ⟨Set.range v, Basis.span_eq v⟩
  exact le_antisymm (le_ciInf fun s ↦ v.le_span s.2) (ciInf_le' _ x)

@[target] theorem rank_eq_spanRank_of_free [Module.Free R M] [StrongRankCondition R] :
    Module.rank R M = (⊤ : Submodule R M).spanRank := by
  sorry


theorem rank_le_spanRank [StrongRankCondition R] :
    Module.rank R M ≤ (⊤ : Submodule R M).spanRank := by
  rw [Module.rank, Submodule.spanRank]
  refine ciSup_le' (fun ι ↦ (le_ciInf fun s ↦ ?_))
  have := linearIndependent_le_span'' ι.2 s.1 s.2
  simpa

end rank

end Submodule
