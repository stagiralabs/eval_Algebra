import VerifiedAgora.tagger
/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# The category of `R`-modules has enough projectives.
-/

universe v u u'

open CategoryTheory

open CategoryTheory.Limits

open LinearMap

open ModuleCat

open scoped Module

/-- The categorical notion of projective object agrees with the explicit module-theoretic notion. -/
@[target]
theorem IsProjective.iff_projective {R : Type u} [Ring R] {P : Type max u v} [AddCommGroup P]
    [Module R P] : Module.Projective R P ↔ Projective (ModuleCat.of R P) := by sorry

namespace ModuleCat

variable {R : Type u} [Ring R] {M : ModuleCat.{max u v} R}

-- We transport the corresponding result from `Module.Projective`.
/-- Modules that have a basis are projective. -/
@[target]
theorem projective_of_free {ι : Type u'} (b : Basis ι R M) : Projective M :=
  sorry
instance moduleCat_enoughProjectives : EnoughProjectives (ModuleCat.{max u v} R) where
  presentation M :=
    ⟨{  p := ModuleCat.of R (M →₀ R)
        projective :=
          projective_of_free.{v,u} (ι := M) (M := ModuleCat.of R (M →₀ R)) <|
            Finsupp.basisSingleOne
        f := ofHom <| Finsupp.basisSingleOne.constr ℕ _root_.id
        epi := (epi_iff_range_eq_top _).mpr
            (range_eq_top.2 fun m => ⟨Finsupp.single m (1 : R), by
              simp [Finsupp.linearCombination_single, Basis.constr] ⟩)}⟩

end ModuleCat
