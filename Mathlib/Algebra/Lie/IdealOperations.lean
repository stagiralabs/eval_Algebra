import VerifiedAgora.tagger
/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Submodule

/-!
# Ideal operations for Lie algebras

Given a Lie module `M` over a Lie algebra `L`, there is a natural action of the Lie ideals of `L`
on the Lie submodules of `M`. In the special case that `M = L` with the adjoint action, this
provides a pairing of Lie ideals which is especially important. For example, it can be used to
define solvability / nilpotency of a Lie algebra via the derived / lower-central series.

## Main definitions

  * `LieSubmodule.hasBracket`
  * `LieSubmodule.lieIdeal_oper_eq_linear_span`
  * `LieIdeal.map_bracket_le`
  * `LieIdeal.comap_bracket_le`

## Notation

Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M` and a Lie
ideal `I ⊆ L`, we introduce the notation `⁅I, N⁆` for the Lie submodule of `M` corresponding to
the action defined in this file.

## Tags

lie algebra, ideal operation
-/


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]
variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
variable (f : M →ₗ⁅R,L⁆ M₂)

section LieIdealOperations

@[target] theorem map_comap_le : map f (comap f N₂) ≤ N₂ := by sorry


@[target] theorem map_comap_eq (hf : N₂ ≤ f.range) : map f (comap f N₂) = N₂ := by
  sorry


@[target] theorem le_comap_map : N ≤ comap f (map f N) := by sorry


theorem comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N := by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)

@[target] theorem map_comap_incl : map N.incl (comap N.incl N') = N ⊓ N' := by
  sorry


variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

/-- Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts on the set
of submodules of `M`. -/
instance hasBracket : Bracket (LieIdeal R L) (LieSubmodule R L M) :=
  ⟨fun I N => lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }⟩

@[target] theorem lieIdeal_oper_eq_span :
    ⁅I, N⁆ = lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } := by sorry


/-- See also `LieSubmodule.lieIdeal_oper_eq_linear_span'` and
`LieSubmodule.lieIdeal_oper_eq_tensor_map_range`. -/
/-- See also `LieSubmodule.lieIdeal_oper_eq_linear_span'` and
`LieSubmodule.lieIdeal_oper_eq_tensor_map_range`. -/
@[target] theorem lieIdeal_oper_eq_linear_span [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } := by
  sorry


theorem lieIdeal_oper_eq_linear_span' [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x ∈ I) (n ∈ N) } := by
  rw [lieIdeal_oper_eq_linear_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    exact ⟨x, hx, n, hn, rfl⟩
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩

@[target] theorem lie_le_iff : ⁅I, N⁆ ≤ N' ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅x, m⁆ ∈ N' := by
  sorry


variable {N I} in
variable {N I} in
@[target] theorem lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ ∈ ⁅I, N⁆ := by
  sorry


variable {N I} in
variable {N I} in
@[target] theorem lie_mem_lie {x : L} {m : M} (hx : x ∈ I) (hm : m ∈ N) : ⁅x, m⁆ ∈ ⁅I, N⁆ := by sorry


@[target] theorem lie_comm : ⁅I, J⁆ = ⁅J, I⁆ := by
  sorry


@[target] theorem lie_le_right : ⁅I, N⁆ ≤ N := by
  sorry


theorem lie_le_left : ⁅I, J⁆ ≤ I := by rw [lie_comm]; exact lie_le_right I J

@[target] theorem lie_le_inf : ⁅I, J⁆ ≤ I ⊓ J := by sorry


@[target] theorem lie_bot : ⁅I, (⊥ : LieSubmodule R L M)⁆ = ⊥ := by sorry


@[target] theorem bot_lie : ⁅(⊥ : LieIdeal R L), N⁆ = ⊥ := by
  sorry


@[target] theorem lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅(x : L), m⁆ = 0 := by
  sorry


variable {I J N N'} in
variable {I J N N'} in
@[target] theorem mono_lie (h₁ : I ≤ J) (h₂ : N ≤ N') : ⁅I, N⁆ ≤ ⁅J, N'⁆ := by
  sorry


variable {I J} in
variable {I J} in
@[target] theorem mono_lie_left (h : I ≤ J) : ⁅I, N⁆ ≤ ⁅J, N⁆ := by sorry


variable {N N'} in
variable {N N'} in
@[target] theorem mono_lie_right (h : N ≤ N') : ⁅I, N⁆ ≤ ⁅I, N'⁆ := by sorry


@[target] theorem lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ := by
  sorry


@[target] theorem sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ := by
  sorry


@[target] theorem lie_inf : ⁅I, N ⊓ N'⁆ ≤ ⁅I, N⁆ ⊓ ⁅I, N'⁆ := by
  sorry


@[target] theorem inf_lie : ⁅I ⊓ J, N⁆ ≤ ⁅I, N⁆ ⊓ ⁅J, N⁆ := by
  sorry


@[target] theorem map_bracket_eq [LieModule R L M] : map f ⁅I, N⁆ = ⁅I, map f N⁆ := by
  sorry


@[target] theorem comap_bracket_eq [LieModule R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ ≤ f.range) :
    comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆ := by
  sorry


end LieIdealOperations

end LieSubmodule

namespace LieIdeal

open LieAlgebra

variable {R : Type u} {L : Type v} {L' : Type w₂}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
@[target] theorem map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁, I₂⁆ ≤ ⁅map f I₁, map f I₂⁆ := by
  sorry


theorem map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) :
    map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆ := by
  suffices ⁅map f I₁, map f I₂⁆ ≤ map f ⁅I₁, I₂⁆ by exact le_antisymm (map_bracket_le f) this
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, coe_map_of_surjective h,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  apply Submodule.span_mono
  rintro x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩
  obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁
  obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂
  exact ⟨⁅(y₁ : L), (y₂ : L)⁆, ⟨y₁, y₂, rfl⟩, by apply f.map_lie⟩

@[target] theorem comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁, comap f J₂⁆ ≤ comap f ⁅J₁, J₂⁆ := by
  sorry


variable {f}

theorem map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂ := by
  conv_rhs => rw [← I₁.incl_idealRange]
  rw [← map_comap_eq]
  exact I₁.incl_isIdealMorphism

theorem comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj, comap_toSubmodule,
    LieSubmodule.sup_toSubmodule, f.ker_toSubmodule, ← Submodule.comap_map_eq,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  congr; simp only [LieHom.coe_toLinearMap, Set.mem_setOf_eq]; ext y
  constructor
  · rintro ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩, hy⟩; rw [← hy]
    rw [LieSubmodule.mem_inf, f.mem_idealRange_iff h] at hx₁ hx₂
    obtain ⟨⟨z₁, hz₁⟩, hz₁'⟩ := hx₁; rw [← hz₁] at hz₁'
    obtain ⟨⟨z₂, hz₂⟩, hz₂'⟩ := hx₂; rw [← hz₂] at hz₂'
    refine ⟨⁅z₁, z₂⁆, ⟨⟨z₁, hz₁'⟩, ⟨z₂, hz₂'⟩, rfl⟩, ?_⟩
    simp only [hz₁, hz₂, Submodule.coe_mk, LieHom.map_lie]
  · rintro ⟨x, ⟨⟨z₁, hz₁⟩, ⟨z₂, hz₂⟩, hx⟩, hy⟩; rw [← hy, ← hx]
    have hz₁' : f z₁ ∈ f.idealRange ⊓ J₁ := by
      rw [LieSubmodule.mem_inf]; exact ⟨f.mem_idealRange z₁, hz₁⟩
    have hz₂' : f z₂ ∈ f.idealRange ⊓ J₂ := by
      rw [LieSubmodule.mem_inf]; exact ⟨f.mem_idealRange z₂, hz₂⟩
    use ⟨f z₁, hz₁'⟩, ⟨f z₂, hz₂'⟩; simp only [Submodule.coe_mk, LieHom.map_lie]

@[target] theorem map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ := by
  sorry


@[target] theorem comap_bracket_incl {I₁ I₂ : LieIdeal R L} :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆ := by
  sorry


/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
@[target] theorem comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ := by
    sorry


end LieIdeal
