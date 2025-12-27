import VerifiedAgora.tagger
/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Trace

/-!
# Chains of roots and weights

Given roots `α` and `β` of a Lie algebra, together with elements `x` in the `α`-root space and
`y` in the `β`-root space, it follows from the Leibniz identity that `⁅x, y⁆` is either zero or
belongs to the `α + β`-root space. Iterating this operation leads to the study of families of
roots of the form `k • α + β`. Such a family is known as the `α`-chain through `β` (or sometimes,
the `α`-string through `β`) and the study of the sum of the corresponding root spaces is an
important technique.

More generally if `α` is a root and `χ` is a weight of a representation, it is useful to study the
`α`-chain through `χ`.

We provide basic definitions and results to support `α`-chain techniques in this file.

## Main definitions / results

 * `LieModule.exists₂_genWeightSpace_smul_add_eq_bot`: given weights `χ₁`, `χ₂` if `χ₁ ≠ 0`, we can
   find `p < 0` and `q > 0` such that the weight spaces `p • χ₁ + χ₂` and `q • χ₁ + χ₂` are both
   trivial.
 * `LieModule.genWeightSpaceChain`: given weights `χ₁`, `χ₂` together with integers `p` and `q`,
   this is the sum of the weight spaces `k • χ₁ + χ₂` for `p < k < q`.
 * `LieModule.trace_toEnd_genWeightSpaceChain_eq_zero`: given a root `α` relative to a Cartan
   subalgebra `H`, there is a natural ideal `corootSpace α` in `H`. This lemma
   states that this ideal acts by trace-zero endomorphisms on the sum of root spaces of any
   `α`-chain, provided the weight spaces at the endpoints are both trivial.
 * `LieModule.exists_forall_mem_corootSpace_smul_add_eq_zero`: given a (potential) root
   `α` relative to a Cartan subalgebra `H`, if we restrict to the ideal
   `corootSpace α` of `H`, we may find an integral linear combination between
   `α` and any weight `χ` of a representation.

-/

open Module Function Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

section IsNilpotent

variable [LieRing.IsNilpotent L] (χ₁ χ₂ : L → R) (p q : ℤ)

section

variable [NoZeroSMulDivisors ℤ R] [NoZeroSMulDivisors R M] [IsNoetherian R M] (hχ₁ : χ₁ ≠ 0)
include hχ₁

@[target]
lemma eventually_genWeightSpace_smul_add_eq_bot :
    ∀ᶠ (k : ℕ) in Filter.atTop, genWeightSpace M (k • χ₁ + χ₂) = ⊥ := by sorry

@[target]
lemma exists_genWeightSpace_smul_add_eq_bot :
    ∃ k > 0, genWeightSpace M (k • χ₁ + χ₂) = ⊥ :=
  sorry

lemma exists₂_genWeightSpace_smul_add_eq_bot :
    ∃ᵉ (p < (0 : ℤ)) (q > (0 : ℤ)),
      genWeightSpace M (p • χ₁ + χ₂) = ⊥ ∧
      genWeightSpace M (q • χ₁ + χ₂) = ⊥ := by
  obtain ⟨q, hq₀, hq⟩ := exists_genWeightSpace_smul_add_eq_bot M χ₁ χ₂ hχ₁
  obtain ⟨p, hp₀, hp⟩ := exists_genWeightSpace_smul_add_eq_bot M (-χ₁) χ₂ (neg_ne_zero.mpr hχ₁)
  refine ⟨-(p : ℤ), by simpa, q, by simpa, ?_, ?_⟩
  · rw [neg_smul, ← smul_neg, natCast_zsmul]
    exact hp
  · rw [natCast_zsmul]
    exact hq

end

/-- Given two (potential) weights `χ₁` and `χ₂` together with integers `p` and `q`, it is often
useful to study the sum of weight spaces associated to the family of weights `k • χ₁ + χ₂` for
`p < k < q`. -/
def genWeightSpaceChain : LieSubmodule R L M :=
  ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂)

lemma genWeightSpaceChain_def :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Ioo p q, genWeightSpace M (k • χ₁ + χ₂) :=
  rfl

@[target]
lemma genWeightSpaceChain_def' :
    genWeightSpaceChain M χ₁ χ₂ p q = ⨆ k ∈ Finset.Ioo p q, genWeightSpace M (k • χ₁ + χ₂) := by sorry

@[target, simp]
lemma genWeightSpaceChain_neg :
    genWeightSpaceChain M (-χ₁) χ₂ (-q) (-p) = genWeightSpaceChain M χ₁ χ₂ p q := by sorry

@[target]
lemma genWeightSpace_le_genWeightSpaceChain {k : ℤ} (hk : k ∈ Ioo p q) :
    genWeightSpace M (k • χ₁ + χ₂) ≤ genWeightSpaceChain M χ₁ χ₂ p q :=
  sorry

end IsNilpotent

section LieSubalgebra

open LieAlgebra

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

@[target]
lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H α)
    {y : M} (hy : y ∈ genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ genWeightSpaceChain M α χ p q := by sorry

lemma lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_left [LieRing.IsNilpotent H]
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H (-α))
    {y : M} (hy : y ∈ genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ genWeightSpaceChain M α χ p q := by
  replace hp : genWeightSpace M ((-p) • (-α) + χ) = ⊥ := by rwa [smul_neg, neg_smul, neg_neg]
  rw [← genWeightSpaceChain_neg] at hy ⊢
  exact lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right M (-α) χ (-q) (-p) hp hx hy

section IsCartanSubalgebra

variable [H.IsCartanSubalgebra] [IsNoetherian R L]

@[target]
lemma trace_toEnd_genWeightSpaceChain_eq_zero
    (hp : genWeightSpace M (p • α + χ) = ⊥)
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : H} (hx : x ∈ corootSpace α) :
    LinearMap.trace R _ (toEnd R H (genWeightSpaceChain M α χ p q) x) = 0 := by sorry
@[target]
lemma exists_forall_mem_corootSpace_smul_add_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [CharZero R] [NoZeroSMulDivisors R M] [IsNoetherian R M]
    (hα : α ≠ 0) (hχ : genWeightSpace M χ ≠ ⊥) :
    ∃ a b : ℤ, 0 < b ∧ ∀ x ∈ corootSpace α, (a • α + b • χ) x = 0 := by sorry

end IsCartanSubalgebra

end LieSubalgebra

section

variable {M}
variable [LieRing.IsNilpotent L]
variable [NoZeroSMulDivisors ℤ R] [NoZeroSMulDivisors R M] [IsNoetherian R M]
variable (α : L → R) (β : Weight R L M)

/-- This is the largest `n : ℕ` such that `i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
def chainTopCoeff : ℕ :=
  letI := Classical.propDecidable
  if hα : α = 0 then 0 else
  Nat.pred <| Nat.find (show ∃ n, genWeightSpace M (n • α + β : L → R) = ⊥ from
    (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists)

/-- This is the largest `n : ℕ` such that `-i • α + β` is a weight for all `0 ≤ i ≤ n`. -/
noncomputable
def chainBotCoeff : ℕ := chainTopCoeff (-α) β

@[simp] lemma chainTopCoeff_neg : chainTopCoeff (-α) β = chainBotCoeff α β := rfl
@[simp] lemma chainBotCoeff_neg : chainBotCoeff (-α) β = chainTopCoeff α β := by
  rw [← chainTopCoeff_neg, neg_neg]

@[simp] lemma chainTopCoeff_zero : chainTopCoeff 0 β = 0 := dif_pos rfl
@[simp] lemma chainBotCoeff_zero : chainBotCoeff 0 β = 0 := dif_pos neg_zero

section
variable (hα : α ≠ 0)
include hα

@[target]
lemma chainTopCoeff_add_one :
    letI := sorry

lemma genWeightSpace_chainTopCoeff_add_one_nsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1) • α + β : L → R) = ⊥ := by
  classical
  rw [chainTopCoeff_add_one _ _ hα]
  exact Nat.find_spec (eventually_genWeightSpace_smul_add_eq_bot M α β hα).exists

@[target]
lemma genWeightSpace_chainTopCoeff_add_one_zsmul_add :
    genWeightSpace M ((chainTopCoeff α β + 1 : ℤ) • α + β : L → R) = ⊥ := by sorry

@[target]
lemma genWeightSpace_chainBotCoeff_sub_one_zsmul_sub :
    genWeightSpace M ((-chainBotCoeff α β - 1 : ℤ) • α + β : L → R) = ⊥ := by sorry

@[target]
lemma genWeightSpace_nsmul_add_ne_bot_of_le {n} (hn : n ≤ chainTopCoeff α β) :
    genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by sorry

lemma genWeightSpace_zsmul_add_ne_bot {n : ℤ}
    (hn : -chainBotCoeff α β ≤ n) (hn' : n ≤ chainTopCoeff α β) :
      genWeightSpace M (n • α + β : L → R) ≠ ⊥ := by
  rcases n with (n | n)
  · simp only [Int.ofNat_eq_coe, Nat.cast_le, Nat.cast_smul_eq_nsmul] at hn' ⊢
    exact genWeightSpace_nsmul_add_ne_bot_of_le α β hn'
  · simp only [Int.negSucc_eq, ← Nat.cast_succ, neg_le_neg_iff, Nat.cast_le] at hn ⊢
    rw [neg_smul, ← smul_neg, Nat.cast_smul_eq_nsmul]
    exact genWeightSpace_nsmul_add_ne_bot_of_le (-α) β hn

@[target]
lemma genWeightSpace_neg_zsmul_add_ne_bot {n : ℕ} (hn : n ≤ chainBotCoeff α β) :
    genWeightSpace M ((-n : ℤ) • α + β : L → R) ≠ ⊥ := by sorry
def chainTop (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨chainTopCoeff α β • α + β, genWeightSpace_nsmul_add_ne_bot_of_le α β le_rfl⟩

/-- The first weight in an `α`-chain through `β`. -/
noncomputable
def chainBot (α : L → R) (β : Weight R L M) : Weight R L M :=
  ⟨(- chainBotCoeff α β : ℤ) • α + β, genWeightSpace_neg_zsmul_add_ne_bot α β le_rfl⟩

@[target]
lemma coe_chainTop' : (chainTop α β : L → R) = chainTopCoeff α β • α + β := sorry

@[simp] lemma coe_chainTop : (chainTop α β : L → R) = (chainTopCoeff α β : ℤ) • α + β := by
  rw [Nat.cast_smul_eq_nsmul ℤ]; rfl
@[simp] lemma coe_chainBot : (chainBot α β : L → R) = (-chainBotCoeff α β : ℤ) • α + β := rfl

@[simp] lemma chainTop_neg : chainTop (-α) β = chainBot α β := by ext; simp
@[simp] lemma chainBot_neg : chainBot (-α) β = chainTop α β := by ext; simp

@[simp] lemma chainTop_zero : chainTop 0 β = β := by ext; simp
@[simp] lemma chainBot_zero : chainBot 0 β = β := by ext; simp

section
variable (hα : α ≠ 0)
include hα

lemma genWeightSpace_add_chainTop :
    genWeightSpace M (α + chainTop α β : L → R) = ⊥ := by
  rw [coe_chainTop', ← add_assoc, ← succ_nsmul',
    genWeightSpace_chainTopCoeff_add_one_nsmul_add _ _ hα]

lemma genWeightSpace_neg_add_chainBot :
    genWeightSpace M (-α + chainBot α β : L → R) = ⊥ := by
  rw [← chainTop_neg, genWeightSpace_add_chainTop _ _ (by simpa using hα)]

lemma chainTop_isNonZero' (hα' : genWeightSpace M α ≠ ⊥) :
    (chainTop α β).IsNonZero := by
  by_contra e
  apply hα'
  rw [← add_zero (α : L → R), ← e, genWeightSpace_add_chainTop _ _ hα]

end

lemma chainTop_isNonZero (α β : Weight R L M) (hα : α.IsNonZero) :
    (chainTop α β).IsNonZero :=
  chainTop_isNonZero' α β hα α.2

end

end LieModule
