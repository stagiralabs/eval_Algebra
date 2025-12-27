import VerifiedAgora.tagger
/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Weights.Chain
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Roots of Lie algebras with non-degenerate Killing forms

The file contains definitions and results about roots of Lie algebras with non-degenerate Killing
forms.

## Main definitions
 * `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`: if the Killing form of
   a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
 * `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`: if the Killing form of a Lie
   algebra is non-singular, then its Cartan subalgebras are Abelian.
 * `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`: over a perfect field, if a Lie
   algebra has non-degenerate Killing form, Cartan subalgebras contain only semisimple elements.
 * `LieAlgebra.IsKilling.span_weight_eq_top`: given a splitting Cartan subalgebra `H` of a
   finite-dimensional Lie algebra with non-singular Killing form, the corresponding roots span the
   dual space of `H`.
 * `LieAlgebra.IsKilling.coroot`: the coroot corresponding to a root.
 * `LieAlgebra.IsKilling.isCompl_ker_weight_span_coroot`: given a root `α` with respect to a Cartan
   subalgebra `H`, we have a natural decomposition of `H` as the kernel of `α` and the span of the
   coroot corresponding to `α`.
 * `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`: root spaces are one-dimensional.

-/

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

lemma restrict_killingForm (H : LieSubalgebra R L) :
    (killingForm R L).restrict H = LieModule.traceForm R H L :=
  rfl

namespace IsKilling

variable [IsKilling R L]

/-- If the Killing form of a Lie algebra is non-singular, it remains non-singular when restricted
to a Cartan subalgebra. -/
lemma ker_restrict_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker ((killingForm R L).restrict H) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmodule_inj, LieSubmodule.sup_toSubmodule,
      LieSubmodule.top_toSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁

@[simp] lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (LieModule.traceForm R H L) = ⊥ :=
  ker_restrict_eq_bot_of_isCartanSubalgebra R L H

@[target]
lemma traceForm_cartan_nondegenerate
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieModule.traceForm R H L).Nondegenerate := by sorry

variable [Module.Free R L] [Module.Finite R L]

instance instIsLieAbelianOfIsCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    IsLieAbelian H :=
  LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L <|
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

end IsKilling

section Field

open Module LieModule Set
open Submodule (span subset_span)

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

section
variable [IsTriangularizable K H L]

/-- For any `α` and `β`, the corresponding root spaces are orthogonal with respect to the Killing
form, provided `α + β ≠ 0`. -/
@[target]
lemma killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H → K} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hαβ : α + β ≠ 0) :
    killingForm K L x y = 0 := by sorry
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hx' : ∀ y ∈ rootSpace H (-α), killingForm K L x y = 0) :
    x ∈ LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y ∈ ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | hN β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  | h0 => simp
  | hadd => simp_all
end

namespace IsKilling

variable [IsKilling K L]

/-- If a Lie algebra `L` has non-degenerate Killing form, the only element of a Cartan subalgebra
whose adjoint action on `L` is nilpotent, is the zero element.

Over a perfect field a much stronger result is true, see
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`. -/
@[target]
lemma eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H)
    (hx' : _root_.IsNilpotent (ad K L x)) : x = 0 := by sorry

@[target, simp]
lemma corootSpace_zero_eq_bot :
    corootSpace (0 : H → K) = ⊥ := by sorry

variable {K L} in
/-- The restriction of the Killing form to a Cartan subalgebra, as a linear equivalence to the
dual. -/
@[simps! apply_apply]
noncomputable def cartanEquivDual :
    H ≃ₗ[K] Module.Dual K H :=
  (traceForm K H L).toDual <| traceForm_cartan_nondegenerate K L H

variable {K L H}

/-- The coroot corresponding to a root. -/
noncomputable def coroot (α : Weight K H L) : H :=
  2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α

@[target]
lemma traceForm_coroot (α : Weight K H L) (x : H) :
    traceForm K H L (coroot α) x = 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • α x := by sorry

variable [IsTriangularizable K H L]

@[target]
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α))
    (aux : ∀ (h : H), ⁅h, e⁆ = α h • e) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by sorry
@[target]
lemma cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) :
    (cartanEquivDual H).symm α ∈ corootSpace α := by sorry
@[target, simp]
lemma span_weight_eq_top :
    span K (range (Weight.toLinear K H L)) = ⊤ := by sorry

variable (K L H) in
@[target, simp]
lemma span_weight_isNonZero_eq_top :
    span K ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) = ⊤ := by sorry

@[target, simp]
lemma iInf_ker_weight_eq_bot :
    ⨅ α : Weight K H L, α.ker = ⊥ := by sorry

section PerfectField

variable [PerfectField K]

open Module.End in
lemma isSemisimple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H) :
    (ad K L x).IsSemisimple := by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_of_add_eq hSN.symm] at hN
  /- Note that the semisimple part `S` is just a scalar action on each root space. -/
  have aux {α : H → K} {y : L} (hy : y ∈ rootSpace H α) : S y = α x' • y := by
    replace hy : y ∈ (ad K L x).maxGenEigenspace (α x') :=
      (genWeightSpace_le_genWeightSpaceOf L x' α) hy
    rw [maxGenEigenspace_eq] at hy
    set k := maxGenEigenspaceIndex (ad K L x) (α x')
    rw [apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hy hS₀ hS.isFinitelySemisimple hN]
  /- So `S` obeys the derivation axiom if we restrict to root spaces. -/
  have h_der (y z : L) (α β : H → K) (hy : y ∈ rootSpace H α) (hz : z ∈ rootSpace H β) :
      S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hyz : ⁅y, z⁆ ∈ rootSpace H (α + β) :=
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β hy hz
    rw [aux hy, aux hz, aux hyz, smul_lie, lie_smul, ← add_smul, ← Pi.add_apply]
  /- Thus `S` is a derivation since root spaces span. -/
  replace h_der (y z : L) : S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hy : y ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    have hz : z ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction' with
    | hN α y hy =>
      induction hz using LieSubmodule.iSup_induction' with
      | hN β z hz => exact h_der y z α β hy hz
      | h0 => simp
      | hadd _ _ _ _ h h' => simp only [lie_add, map_add, h, h']; abel
    | h0 => simp
    | hadd _ _ _ _ h h' => simp only [add_lie, map_add, h, h']; abel
  /- An equivalent form of the derivation axiom used in `LieDerivation`. -/
  replace h_der : ∀ y z : L, S ⁅y, z⁆ = ⁅y, S z⁆ - ⁅z, S y⁆ := by
    simp_rw [← lie_skew (S _) _, add_comm, ← sub_eq_add_neg] at h_der; assumption
  /- Bundle `S` as a `LieDerivation`. -/
  let S' : LieDerivation K L L := ⟨S, h_der⟩
  /- Since `L` has non-degenerate Killing form, `S` must be inner, corresponding to some `y : L`. -/
  obtain ⟨y, hy⟩ := LieDerivation.IsKilling.exists_eq_ad S'
  /- `y` commutes with all elements of `H` because `S` has eigenvalue 0 on `H`, `S = ad K L y`. -/
  have hy' (z : L) (hz : z ∈ H) : ⁅y, z⁆ = 0 := by
    rw [← LieSubalgebra.mem_toLieSubmodule, ← rootSpace_zero_eq] at hz
    simp [S', ← ad_apply (R := K), ← LieDerivation.coe_ad_apply_eq_ad_apply, hy, aux hz]
  /- Thus `y` belongs to `H` since `H` is self-normalizing. -/
  replace hy' : y ∈ H := by
    suffices y ∈ H.normalizer by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at this
    exact (H.mem_normalizer_iff y).mpr fun z hz ↦ hy' z hz ▸ LieSubalgebra.zero_mem H
  /- It suffices to show `x = y` since `S = ad K L y` is semisimple. -/
  suffices x = y by rwa [this, ← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rw [← sub_eq_zero]
  /- This will follow if we can show that `ad K L (x - y)` is nilpotent. -/
  apply eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra K L H (H.sub_mem hx hy')
  /- Which is true because `ad K L (x - y) = N`. -/
  replace hy : S = ad K L y := by rw [← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rwa [LieHom.map_sub, hSN, hy, add_sub_cancel_right, eq_sub_of_add_eq hSN.symm]

@[target]
lemma lie_eq_smul_of_mem_rootSpace {α : H → K} {x : L} (hx : x ∈ rootSpace H α) (h : H) :
    ⁅h, x⁆ = α h • x := by sorry

@[target]
lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by sorry

lemma coe_corootSpace_eq_span_singleton' (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ (cartanEquivDual H).symm α := by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} ⊆
        K ∙ ((cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      exact ⟨killingForm K L e f, rfl⟩
    simp only [LieSubmodule.mem_toSubmodule, mem_corootSpace] at hx'
    replace this := Submodule.span_mono this hx'
    rw [Submodule.span_span] at this
    rw [Submodule.mem_span_singleton] at this ⊢
    obtain ⟨t, rfl⟩ := this
    use t
    simp only [Subtype.ext_iff]
    rw [Submodule.coe_smul_of_tower]
  · simp only [Submodule.span_singleton_le_iff_mem, LieSubmodule.mem_toSubmodule]
    exact cartanEquivDual_symm_apply_mem_corootSpace α

end PerfectField

section CharZero

variable [CharZero K]

/-- The contrapositive of this result is very useful, taking `x` to be the element of `H`
corresponding to a root `α` under the identification between `H` and `H^*` provided by the Killing
form. -/
lemma eq_zero_of_apply_eq_zero_of_mem_corootSpace
    (x : H) (α : H → K) (hαx : α x = 0) (hx : x ∈ corootSpace α) :
    x = 0 := by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x ∈ ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β ↦ ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx

lemma disjoint_ker_weight_corootSpace (α : Weight K H L) :
    Disjoint α.ker (corootSpace α) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ ↦ ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

@[target]
lemma root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    α ((cartanEquivDual H).symm α) ≠ 0 := by sorry

lemma root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) :
    α (coroot α) = 2 := by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel₀ (root_apply_cartanEquivDual_symm_ne_zero hα)

@[simp] lemma coroot_eq_zero_iff {α : Weight K H L} :
    coroot α = 0 ↔ α.IsZero := by
  refine ⟨fun hα ↦ ?_, fun hα ↦ ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

@[target, simp]
lemma coroot_zero [Nontrivial L] : coroot (0 : Weight K H L) = 0 := by sorry

@[target]
lemma coe_corootSpace_eq_span_singleton (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ coroot α := by sorry

@[target, simp]
lemma corootSpace_eq_bot_iff {α : Weight K H L} :
    corootSpace α = ⊥ ↔ α.IsZero := by sorry

lemma isCompl_ker_weight_span_coroot (α : Weight K H L) :
    IsCompl α.ker (K ∙ coroot α) := by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by aesop)
      (disjoint_ker_weight_corootSpace α)
    replace hα : corootSpace α ≠ ⊥ := by simpa using hα
    rwa [ne_eq, ← LieSubmodule.toSubmodule_inj] at hα

@[target]
lemma traceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : H}
    (hx : x ∈ α.ker) (hy : y ∈ K ∙ coroot α) :
    traceForm K H L x y = 0 := by sorry

@[simp] lemma orthogonal_span_coroot_eq_ker (α : Weight K H L) :
    (traceForm K H L).orthogonal (K ∙ coroot α) = α.ker := by
  if hα : α.IsZero then
    have hα' : coroot α = 0 := by simpa
    replace hα : α.ker = ⊤ := by ext; simp [hα]
    simp [hα, hα']
  else
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx y hy ↦ ?_)
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      specialize hx (coroot α) (Submodule.mem_span_singleton_self _)
      simp only [LinearMap.BilinForm.isOrtho_def, traceForm_coroot, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, false_or] at hx
      simpa using hx.resolve_left (root_apply_cartanEquivDual_symm_ne_zero hα)
    · have := traceForm_eq_zero_of_mem_ker_of_mem_span_coroot hx hy
      rwa [traceForm_comm] at this

@[simp] lemma coroot_eq_iff (α β : Weight K H L) :
    coroot α = coroot β ↔ α = β := by
  refine ⟨fun hyp ↦ ?_, fun h ↦ by rw [h]⟩
  if hα : α.IsZero then
    have hβ : β.IsZero := by
      rw [← coroot_eq_zero_iff] at hα ⊢
      rwa [← hyp]
    ext
    simp [hα.eq, hβ.eq]
  else
    have hβ : β.IsNonZero := by
      contrapose! hα
      simp only [not_not, ← coroot_eq_zero_iff] at hα ⊢
      rwa [hyp]
    have : α.ker = β.ker := by
      rw [← orthogonal_span_coroot_eq_ker α, hyp, orthogonal_span_coroot_eq_ker]
    suffices (α : H →ₗ[K] K) = β by ext x; simpa using LinearMap.congr_fun this x
    apply Module.Dual.eq_of_ker_eq_of_apply_eq (coroot α) this
    · rw [Weight.toLinear_apply, root_apply_coroot hα, hyp, Weight.toLinear_apply,
        root_apply_coroot hβ]
    · simp [root_apply_coroot hα]

@[target]
lemma exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ h e f : L, IsSl2Triple h e f ∧ e ∈ rootSpace H α ∧ f ∈ rootSpace H (- α) := by sorry

lemma _root_.IsSl2Triple.h_eq_coroot {α : Weight K H L} (hα : α.IsNonZero)
    {h e f : L} (ht : IsSl2Triple h e f) (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (- α)) :
    h = coroot α := by
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift h to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  congr 1
  have key : α h = 2 := by
    have := lie_eq_smul_of_mem_rootSpace heα h
    rw [LieSubalgebra.coe_bracket_of_module, ht.lie_h_e_smul K] at this
    exact smul_left_injective K ht.e_ne_zero this.symm
  suffices ∃ s : K, s • h = coroot α by
    obtain ⟨s, hs⟩ := this
    replace this : s = 1 := by simpa [root_apply_coroot hα, key] using congr_arg α hs
    rwa [this, one_smul] at hs
  set α' := (cartanEquivDual H).symm α with hα'
  have h_eq : h = killingForm K L e f • α' := by
    simp only [hα', Subtype.ext_iff, ← ht.lie_e_f, hef]
    rw [Submodule.coe_smul_of_tower]
  use (2 • (α α')⁻¹) * (killingForm K L e f)⁻¹
  have hef₀ : killingForm K L e f ≠ 0 := by
    have := ht.h_ne_zero
    contrapose! this
    simpa [this] using h_eq
  rw [h_eq, smul_smul, mul_assoc, inv_mul_cancel₀ hef₀, mul_one, smul_assoc, coroot]

@[target]
lemma finrank_rootSpace_eq_one (α : Weight K H L) (hα : α.IsNonZero) :
    finrank K (rootSpace H α) = 1 := by sorry

lemma restrict_killingForm_eq_sum :
    (killingForm K L).restrict H = ∑ α ∈ H.root, (α : H →ₗ[K] K).smulRight (α : H →ₗ[K] K) := by
  rw [restrict_killingForm, traceForm_eq_sum_finrank_nsmul' K H L]
  refine Finset.sum_congr rfl fun χ hχ ↦ ?_
  replace hχ : χ.IsNonZero := by simpa [LieSubalgebra.root] using hχ
  simp [finrank_rootSpace_eq_one _ hχ]

end CharZero

end IsKilling

end Field

end LieAlgebra

namespace LieModule

namespace Weight

open LieAlgebra IsKilling

variable {K L}

variable [FiniteDimensional K L]
variable [IsKilling K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
variable {α : Weight K H L}

instance : InvolutiveNeg (Weight K H L) where
  neg α := ⟨-α, by
    by_cases hα : α.IsZero
    · convert α.genWeightSpace_ne_bot; rw [hα, neg_zero]
    · intro e
      obtain ⟨x, hx, x_ne0⟩ := α.exists_ne_zero
      have := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hx
        (fun y hy ↦ by rw [rootSpace, e] at hy; rw [hy, map_zero])
      rw [ker_killingForm_eq_bot] at this
      exact x_ne0 this⟩
  neg_neg α := by ext; simp

@[simp] lemma coe_neg : ((-α : Weight K H L) : H → K) = -α := rfl

lemma IsZero.neg (h : α.IsZero) : (-α).IsZero := by ext; rw [coe_neg, h, neg_zero]

@[simp] lemma isZero_neg : (-α).IsZero ↔ α.IsZero := ⟨fun h ↦ neg_neg α ▸ h.neg, fun h ↦ h.neg⟩

lemma IsNonZero.neg (h : α.IsNonZero) : (-α).IsNonZero := fun e ↦ h (by simpa using e.neg)

@[simp] lemma isNonZero_neg {α : Weight K H L} : (-α).IsNonZero ↔ α.IsNonZero := isZero_neg.not

@[simp] lemma toLinear_neg {α : Weight K H L} : (-α).toLinear = -α.toLinear := rfl

variable [CharZero K]

@[target, simp]
lemma _root_.LieAlgebra.IsKilling.coroot_neg (α : Weight K H L) : coroot (-α) = -coroot α := by sorry

end Weight

end LieModule
