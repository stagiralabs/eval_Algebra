import VerifiedAgora.tagger
/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Translations

/-!
# Stabilisation of gcf Computations Under Termination

## Summary

We show that the continuants and convergents of a gcf stabilise once the gcf terminates.
-/


namespace GenContFract

variable {K : Type*} {g : GenContFract K} {n m : ℕ}

/-- If a gcf terminated at position `n`, it also terminated at `m ≥ n`. -/
theorem terminated_stable (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.TerminatedAt m :=
  g.s.terminated_stable n_le_m terminatedAt_n

variable [DivisionRing K]

@[target] theorem contsAux_stable_step_of_terminated (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux (n + 2) = g.contsAux (n + 1) := by
  sorry


theorem contsAux_stable_of_terminated (n_lt_m : n < m) (terminatedAt_n : g.TerminatedAt n) :
    g.contsAux m = g.contsAux (n + 1) := by
  refine Nat.le_induction rfl (fun k hnk hk => ?_) _ n_lt_m
  rcases Nat.exists_eq_add_of_lt hnk with ⟨k, rfl⟩
  refine (contsAux_stable_step_of_terminated ?_).trans hk
  exact terminated_stable (Nat.le_add_right _ _) terminatedAt_n

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convs (g : GenContFract K) : Stream' K := by sorry


theorem convs'Aux_stable_of_terminated {s : Stream'.Seq <| Pair K} (n_le_m : n ≤ m)
    (terminatedAt_n : s.TerminatedAt n) : convs'Aux s m = convs'Aux s n := by
  induction n_le_m with
  | refl => rfl
  | step n_le_m IH =>
    refine (convs'Aux_stable_step_of_terminated (?_)).trans IH
    exact s.terminated_stable n_le_m terminatedAt_n

@[target] theorem conts_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.conts m = g.conts n := by
  sorry


@[target] theorem nums_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.nums m = g.nums n := by
  sorry


@[target] theorem dens_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.dens m = g.dens n := by
  sorry


@[target] theorem convs_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs m = g.convs n := by
  sorry


theorem convs'_stable_of_terminated (n_le_m : n ≤ m) (terminatedAt_n : g.TerminatedAt n) :
    g.convs' m = g.convs' n := by
  simp only [convs', convs'Aux_stable_of_terminated n_le_m terminatedAt_n]

end GenContFract
