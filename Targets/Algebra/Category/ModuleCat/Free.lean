import VerifiedAgora.tagger
/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exact sequences with free modules

This file proves results about linear independence and span in exact sequences of modules.

## Main theorems

* `linearIndependent_shortExact`: Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
  `R`-modules and linearly independent families `v : ι → X₁` and `w : ι' → X₃`, we get a linearly
  independent family `ι ⊕ ι' → X₂`
* `span_rightExact`: Given an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and spanning
  families `v : ι → X₁` and `w : ι' → X₃`, we get a spanning family `ι ⊕ ι' → X₂`
* Using `linearIndependent_shortExact` and `span_rightExact`, we prove `free_shortExact`: In a
  short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` where `X₁` and `X₃` are free, `X₂` is free as well.

## Tags
linear algebra, module, free

-/

open CategoryTheory Module

namespace ModuleCat

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

open CategoryTheory Submodule Set

section LinearIndependent

variable (hv : LinearIndependent R v) {u : ι ⊕ ι' → S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)

section
include hS hw huv

@[target]
theorem disjoint_span_sum : Disjoint (span R (range (u ∘ Sum.inl)))
    (span R (range (u ∘ Sum.inr))) := by sorry
@[target]
theorem linearIndependent_leftExact : LinearIndependent R u := by sorry
theorem linearIndependent_shortExact {w : ι' → S.X₃} (hw : LinearIndependent R w) :
    LinearIndependent R (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w)) := by
  apply linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)

end LinearIndependent

section Span

include hS in
/-- In the commutative diagram
```
    f     g
 X₁ --→ X₂ --→ X₃
 ↑      ↑      ↑
v|     u|     w|
 ι  → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are `Sum.inl` and
`Sum.inr`. If `v` spans `X₁` and `w` spans `X₃`, then `u` spans `X₂`. -/
theorem span_exact {β : Type*} {u : ι ⊕ β → S.X₂} (huv : u ∘ Sum.inl = S.f ∘ v)
    (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range (S.g ∘ u ∘ Sum.inr))) :
    ⊤ ≤ span R (range u) := by
  intro m _
  have hgm : S.g m ∈ span R (range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j))
  have hsub : m - m' ∈ LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm, map_finsupp_sum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsupp_sum] at hnm
  rw [← sub_add_cancel m m', ← hnm,]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b ↦ b • S.f (v a)) =
      (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

include hS in
/-- Given an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and spanning
    families `v : ι → X₁` and `w : ι' → X₃`, we get a spanning family `ι ⊕ ι' → X₂` -/
@[target]
theorem span_rightExact {w : ι' → S.X₃} (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range w)) (hE : Epi S.g) :
    ⊤ ≤ span R (range (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w))) := by sorry

end Span

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, given bases for `X₁` and `X₃`
indexed by `ι` and `ι'` respectively, we get a basis for `X₂` indexed by `ι ⊕ ι'`. -/
noncomputable
def Basis.ofShortExact
    (bN : Basis ι R S.X₁) (bP : Basis ι' R S.X₃) : Basis (ι ⊕ ι') R S.X₂ :=
  Basis.mk (linearIndependent_shortExact hS' bN.linearIndependent bP.linearIndependent)
    (span_rightExact hS'.exact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) hS'.epi_g)

include hS'

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, if `X₁` and `X₃` are free,
then `X₂` is free. -/
@[target]
theorem free_shortExact [Module.Free R S.X₁] [Module.Free R S.X₃] :
    Module.Free R S.X₂ :=
  sorry

@[target]
theorem free_shortExact_rank_add [Module.Free R S.X₁] [Module.Free R S.X₃]
    [StrongRankCondition R] :
    Module.rank R S.X₂ = Module.rank R S.X₁ + Module.rank R S.X₃ := by sorry

theorem free_shortExact_finrank_add {n p : ℕ} [Module.Free R S.X₁] [Module.Free R S.X₃]
    [Module.Finite R S.X₁] [Module.Finite R S.X₃]
    (hN : Module.finrank R S.X₁ = n)
    (hP : Module.finrank R S.X₃ = p)
    [StrongRankCondition R] :
    finrank R S.X₂ = n + p := by
  apply finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add hS', ← hN, ← hP]
  simp only [Nat.cast_add, finrank_eq_rank]

end ModuleCat
