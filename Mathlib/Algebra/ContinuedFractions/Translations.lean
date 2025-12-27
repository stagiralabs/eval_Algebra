import VerifiedAgora.tagger
/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.ContinuedFractions.Basic
import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`Algebra.ContinuedFractions.Basic`.
-/


namespace GenContFract

section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type*} {g : GenContFract α} {n : ℕ}

@[target] theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by sorry


@[target] theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by sorry


@[target] theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  sorry


@[target] theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  sorry


@[target] theorem partDen_none_iff_s_none : g.partDens.get? n = none ↔ g.s.get? n = none := by
  sorry


@[target] theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  sorry


@[target] theorem partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partNums.get? n = some gp.a := by sorry


@[target] theorem partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partDens.get? n = some gp.b := by sorry


@[target] theorem exists_s_a_of_partNum {a : α} (nth_partNum_eq : g.partNums.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.a = a := by
  sorry


@[target] theorem exists_s_b_of_partDen {b : α}
    (nth_partDen_eq : g.partDens.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  sorry


end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type*} {g : GenContFract K} {n : ℕ} [DivisionRing K]

@[target] theorem nth_cont_eq_succ_nth_contAux : g.conts n = g.contsAux (n + 1) := by sorry


@[target] theorem num_eq_conts_a : g.nums n = (g.conts n).a := by sorry


@[target] theorem den_eq_conts_b : g.dens n = (g.conts n).b := by sorry


@[target] theorem conv_eq_num_div_den : g.convs n = g.nums n / g.dens n := by sorry


@[target] theorem conv_eq_conts_a_div_conts_b :
    g.convs n = (g.conts n).a / (g.conts n).b := by sorry


@[target] theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.nums n = A) :
    ∃ conts, g.conts n = conts ∧ conts.a = A := by sorry


@[target] theorem exists_conts_b_of_den {B : K} (nth_denom_eq : g.dens n = B) :
    ∃ conts, g.conts n = conts ∧ conts.b = B := by sorry


@[target] theorem zeroth_contAux_eq_one_zero : g.contsAux 0 = ⟨1, 0⟩ := by sorry


@[target] theorem first_contAux_eq_h_one : g.contsAux 1 = ⟨g.h, 1⟩ := by sorry


@[target] theorem zeroth_cont_eq_h_one : g.conts 0 = ⟨g.h, 1⟩ := by sorry


@[target] theorem zeroth_num_eq_h : g.nums 0 = g.h := by sorry


@[target] theorem zeroth_den_eq_one : g.dens 0 = 1 := by sorry


@[target] theorem zeroth_conv_eq_h : g.convs 0 = g.h := by
  sorry


@[target] theorem second_contAux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  sorry


@[target] theorem first_cont_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  sorry


@[target] theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by sorry


@[target] theorem first_den_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.dens 1 = gp.b := by sorry


@[simp]
theorem zeroth_conv'Aux_eq_zero {s : Stream'.Seq <| Pair K} :
    convs'Aux s 0 = (0 : K) :=
  rfl

@[simp]
theorem zeroth_conv'_eq_h : g.convs' 0 = g.h := by simp [convs']

/-- Returns the convergents `Aₙ / Bₙ` of `g`, where `Aₙ, Bₙ` are the nth continuants of `g`. -/
def convs (g : GenContFract K) : Stream' K := by sorry


theorem convs'Aux_succ_some {s : Stream'.Seq (Pair K)} {p : Pair K} (h : s.head = some p)
    (n : ℕ) : convs'Aux s (n + 1) = p.a / (p.b + convs'Aux s.tail n) := by
  simp [convs'Aux, h]

end WithDivisionRing

end GenContFract
