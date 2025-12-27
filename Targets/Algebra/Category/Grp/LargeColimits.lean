import VerifiedAgora.tagger
/-
Copyright (c) 2025 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Existence of "big" colimits in the category of additive commutative groups

If `F : J ⥤ AddCommGrp.{w}` is a functor, we show that `F` admits a colimit if and only
if `Colimits.Quot F` (the quotient of the direct sum of the commutative groups `F.obj j`
by the relations given by the morphisms in the diagram) is `w`-small.

-/

universe w u v

open CategoryTheory Limits

namespace AddCommGrp

variable {J : Type u} [Category.{v} J] {F : J ⥤ AddCommGrp.{w}} (c : Cocone F)

open Colimits

/--
If `c` is a cocone of `F` such that `Quot.desc F c` is bijective, then `c` is a colimit
cocone of `F`.
-/
@[target]
lemma isColimit_iff_bijective_desc [DecidableEq J] :
     Nonempty (IsColimit c) ↔ Function.Bijective (Quot.desc F c) := by sorry
lemma hasColimit_iff_small_quot [DecidableEq J] : HasColimit F ↔ Small.{w} (Quot F) :=
  ⟨fun _ ↦ Small.mk ⟨_, ⟨(Equiv.ofBijective _ ((isColimit_iff_bijective_desc (colimit.cocone F)).mp
    ⟨colimit.isColimit _⟩))⟩⟩, hasColimit_of_small_quot F⟩

end AddCommGrp
