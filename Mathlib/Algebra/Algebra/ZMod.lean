import VerifiedAgora.tagger
/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.ZMod.Basic

/-!
# The `ZMod n`-algebra structure on rings whose characteristic divides `n`
-/

assert_not_exists TwoSidedIdeal

namespace ZMod

variable (R : Type*) [Ring R]

instance (p : ℕ) : Subsingleton (Algebra (ZMod p) R) :=
  ⟨fun _ _ => Algebra.algebra_ext _ _ <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

section

variable {n : ℕ} (m : ℕ) [CharP R m]

/-- The `ZMod n`-algebra structure on rings whose characteristic `m` divides `n`.
See note [reducible non-instances]. -/
instance algebra : Algebra R (Π i, A i) where
  algebraMap := Pi.ringHom fun i ↦ algebraMap R (A i)
  commutes' := fun a f ↦ by sorry


end

/-- The `ZMod p`-algebra structure on a ring of characteristic `p`. This is not an
instance since it creates a diamond with `Algebra.id`.
See note [reducible non-instances]. -/
abbrev algebra (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl

end ZMod
