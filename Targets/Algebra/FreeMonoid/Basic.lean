import VerifiedAgora.tagger
/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Equiv.Defs

/-!
# Free monoid over a given alphabet

## Main definitions

* `FreeMonoid α`: free monoid over alphabet `α`; defined as a synonym for `List α`
  with multiplication given by `(++)`.
* `FreeMonoid.of`: embedding `α → FreeMonoid α` sending each element `x` to `[x]`;
* `FreeMonoid.lift`: natural equivalence between `α → M` and `FreeMonoid α →* M`
* `FreeMonoid.map`: embedding of `α → β` into `FreeMonoid α →* FreeMonoid β` given by `List.map`.
-/


variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

/-- Free monoid over a given alphabet. -/
@[to_additive "Free nonabelian additive monoid over a given alphabet"]
def FreeMonoid (α) := List α

namespace FreeMonoid

/-- The identity equivalence between `FreeMonoid α` and `List α`. -/
@[to_additive "The identity equivalence between `FreeAddMonoid α` and `List α`."]
def toList : FreeMonoid α ≃ List α := Equiv.refl _

/-- The identity equivalence between `List α` and `FreeMonoid α`. -/
@[to_additive "The identity equivalence between `List α` and `FreeAddMonoid α`."]
def ofList : List α ≃ FreeMonoid α := Equiv.refl _

@[to_additive (attr := simp)]
theorem toList_symm : (@toList α).symm = ofList := rfl

@[to_additive (attr := simp)]
theorem ofList_symm : (@ofList α).symm = toList := rfl

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem ofList_toList (xs : FreeMonoid α) : ofList (toList xs) = xs := rfl

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[to_additive]
instance : CancelMonoid (FreeMonoid α) where
  one := ofList []
  mul x y := ofList (toList x ++ toList y)
  mul_one := List.append_nil
  one_mul := List.nil_append
  mul_assoc := List.append_assoc
  mul_left_cancel _ _ _ := List.append_cancel_left
  mul_right_cancel _ _ _ := List.append_cancel_right

@[to_additive]
instance : Inhabited (FreeMonoid α) := ⟨1⟩

@[to_additive]
instance [IsEmpty α] : Unique (FreeMonoid α) := inferInstanceAs <| Unique (List α)

@[to_additive (attr := simp)]
theorem toList_one : toList (1 : FreeMonoid α) = [] := rfl

@[to_additive (attr := simp)]
theorem ofList_nil : ofList ([] : List α) = 1 := rfl

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[target, to_additive (attr := by sorry

@[target, to_additive (attr := sorry

@[deprecated (since := "2024-10-15")] alias ofList_join := ofList_flatten
@[deprecated (since := "2024-10-15")]
alias _root_.FreeAddMonoid.ofList_join := _root_.FreeAddMonoid.ofList_flatten

/-- Embeds an element of `α` into `FreeMonoid α` as a singleton list. -/
@[to_additive "Embeds an element of `α` into `FreeAddMonoid α` as a singleton list."]
def of (x : α) : FreeMonoid α := ofList [x]

@[target, to_additive (attr := sorry

@[to_additive]
theorem ofList_singleton (x : α) : ofList [x] = of x := rfl

@[to_additive (attr := simp)]
theorem ofList_cons (x : α) (xs : List α) : ofList (x :: xs) = of x * ofList xs := rfl

@[target, to_additive]
theorem toList_of_mul (x : α) (xs : FreeMonoid α) : toList (of x * xs) = x :: toList xs := sorry

@[target, to_additive]
theorem of_injective : Function.Injective (@of α) := sorry

section Length
variable {a : FreeMonoid α}

/-- The length of a free monoid element: 1.length = 0 and (a * b).length = a.length + b.length -/
@[to_additive "The length of an additive free monoid element: 1.length = 0 and (a + b).length =
  a.length + b.length"]
def length (a : FreeMonoid α) : ℕ := a.toList.length

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem length_of (m : α) : length (of m) = 1 := rfl

@[target, to_additive existing]
theorem length_eq_one : length a = 1 ↔ ∃ m, a = FreeMonoid.of m :=
  sorry

@[to_additive]
theorem length_eq_two {v : FreeMonoid α} :
    v.length = 2 ↔ ∃ c d, v = FreeMonoid.of c * FreeMonoid.of d := List.length_eq_two

@[to_additive]
theorem length_eq_three {v : FreeMonoid α} : v.length = 3 ↔ ∃ (a b c : α), v = of a * of b * of c :=
  List.length_eq_three

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem of_ne_one (a : α) : of a ≠ 1 := by
  intro h
  have := congrArg FreeMonoid.length h
  simp only [length_of, length_one, Nat.succ_ne_self] at this

@[target, to_additive (attr := sorry

end Length

section Mem
variable {m : α}

/-- Membership in a free monoid element -/
@[to_additive "Membership in a free monoid element"]
def mem (a : FreeMonoid α) (m : α) := m ∈ toList a

@[to_additive]
instance : Membership α (FreeMonoid α) := ⟨mem⟩

@[target, to_additive]
theorem not_mem_one : ¬ m ∈ (1 : FreeMonoid α) := sorry

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem mem_of_self : m ∈ of m := sorry

@[target, to_additive (attr := sorry

end Mem

/-- Recursor for `FreeMonoid` using `1` and `FreeMonoid.of x * xs` instead of `[]` and `x :: xs`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
  "Recursor for `FreeAddMonoid` using `0` and
  FreeAddMonoid.of x + xs` instead of `[]` and `x :: xs`."]
-- Porting note: change from `List.recOn` to `List.rec` since only the latter is computable
def recOn {C : FreeMonoid α → Sort*} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (of x * xs)) : C xs := List.rec h0 ih xs

@[target, to_additive (attr := sorry

@[target, to_additive (attr := sorry

section induction_principles

/-- An induction principle on free monoids, with cases for `1`, `FreeMonoid.of` and `*`. -/
@[to_additive (attr := elab_as_elim, induction_eliminator)
"An induction principle on free monoids, with cases for `0`, `FreeAddMonoid.of` and `+`."]
protected theorem inductionOn {C : FreeMonoid α → Prop} (z : FreeMonoid α) (one : C 1)
    (of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
  C z := List.rec one (fun _ _ ih => mul [_] _ (of _) ih) z

/-- An induction principle for free monoids which mirrors induction on lists, with cases analogous
to the empty list and cons -/
@[to_additive (attr := elab_as_elim) "An induction principle for free monoids which mirrors
induction on lists, with cases analogous to the empty list and cons"]
protected theorem inductionOn' {p : FreeMonoid α → Prop} (a : FreeMonoid α)
    (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (of b * a)) : p a :=
  List.rec one (fun _ _ tail_ih => mul_of _ _ tail_ih) a

end induction_principles

/-- A version of `List.cases_on` for `FreeMonoid` using `1` and `FreeMonoid.of x * xs` instead of
`[]` and `x :: xs`. -/
@[to_additive (attr := elab_as_elim, cases_eliminator)
  "A version of `List.casesOn` for `FreeAddMonoid` using `0` and
  `FreeAddMonoid.of x + xs` instead of `[]` and `x :: xs`."]
def casesOn {C : FreeMonoid α → Sort*} (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : C xs := List.casesOn xs h0 ih

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem casesOn_of_mul {C : FreeMonoid α → Sort*} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (of x * xs)) : @casesOn α C (of x * xs) h0 ih = ih x xs := rfl

@[target, to_additive (attr := sorry
@[to_additive "A variant of `List.sum` that has `[x].sum = x` true definitionally.
The purpose is to make `FreeAddMonoid.lift_eval_of` true by `rfl`."]
def prodAux {M} [Monoid M] : List M → M
  | [] => 1
  | (x :: xs) => List.foldl (· * ·) x xs

@[target, to_additive]
lemma prodAux_eq : ∀ l : List M, FreeMonoid.prodAux l = l.prod
  | [] => rfl
  | (_ :: xs) => by simp [prodAux, List.prod_eq_foldl]

/-- Equivalence between maps `α → M` and monoid homomorphisms `FreeMonoid α →* M`. -/
@[to_additive "Equivalence between maps `α → A` and additive monoid homomorphisms
`FreeAddMonoid α →+ A`."]
def lift : (α → M) ≃ (FreeMonoid α →* M) where
  toFun f :=
  sorry

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem lift_symm_apply (f : FreeMonoid α →* M) : lift.symm f = f ∘ of := rfl

@[target, to_additive]
theorem lift_apply (f : α → M) (l : FreeMonoid α) : lift f l = ((toList l).map f).prod :=
  sorry

@[target, to_additive]
theorem lift_comp_of (f : α → M) : lift f ∘ of = f := sorry

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem lift_restrict (f : FreeMonoid α →* M) : lift (f ∘ of) = f := lift.apply_symm_apply f

@[target, to_additive]
theorem comp_lift (g : M →* N) (f : α → M) : g.comp (lift f) = lift (g ∘ f) := by sorry

@[to_additive]
theorem hom_map_lift (g : M →* N) (f : α → M) (x : FreeMonoid α) : g (lift f x) = lift (g ∘ f) x :=
  DFunLike.ext_iff.1 (comp_lift g f) x

/-- Define a multiplicative action of `FreeMonoid α` on `β`. -/
@[to_additive "Define an additive action of `FreeAddMonoid α` on `β`."]
def mkMulAction (f : α → β → β) : MulAction (FreeMonoid α) β where
  smul l b := l.toList.foldr f b
  one_smul _ := rfl
  mul_smul _ _ _ := List.foldr_append _ _ _ _

@[to_additive]
theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := mkMulAction f
    l • b = l.toList.foldr f b := rfl

@[target, to_additive]
theorem ofList_smul (f : α → β → β) (l : List α) (b : β) :
    haveI := sorry

@[target, to_additive (attr := sorry

section Map
variable {f : α → β} {a b : FreeMonoid α}
/-- The unique monoid homomorphism `FreeMonoid α →* FreeMonoid β` that sends
each `of x` to `of (f x)`. -/
@[to_additive "The unique additive monoid homomorphism `FreeAddMonoid α →+ FreeAddMonoid β`
that sends each `of x` to `of (f x)`."]
def map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun l := ofList <| l.toList.map f
  map_one' := rfl
  map_mul' _ _ := List.map_append _ _ _

@[target, to_additive (attr := sorry

@[target, to_additive]
theorem mem_map {m : β} : m ∈ map f a ↔ ∃ n ∈ a, f n = m := sorry

@[target, to_additive]
theorem map_map {α₁ : Type*} {g : α₁ → α} {x : FreeMonoid α₁} :
    map f (map g x) = map (f ∘ g) x := by sorry

@[target, to_additive]
theorem toList_map (f : α → β) (xs : FreeMonoid α) : toList (map f xs) = xs.toList.map f := sorry

@[to_additive]
theorem ofList_map (f : α → β) (xs : List α) : ofList (xs.map f) = map f (ofList xs) := rfl

@[to_additive]
theorem lift_of_comp_eq_map (f : α → β) : (lift fun x ↦ of (f x)) = map f := hom_eq fun _ ↦ rfl

@[target, to_additive]
theorem map_comp (g : β → γ) (f : α → β) : map (g ∘ f) = (map g).comp (map f) := sorry

@[to_additive (attr := simp)]
theorem map_id : map (@id α) = MonoidHom.id (FreeMonoid α) := hom_eq fun _ ↦ rfl

@[target, to_additive (attr := by sorry

@[target, to_additive (attr := by sorry
@[to_additive]
instance uniqueUnits : Unique (FreeMonoid α)ˣ where
  uniq u := Units.ext <| toList.injective <|
    have : toList u.val ++ toList u.inv = [] := DFunLike.congr_arg toList u.val_inv
    (List.append_eq_nil_iff.mp this).1

@[target, to_additive (attr := by sorry

end Map

/-! ### reverse -/

section Reverse
/-- reverses the symbols in a free monoid element -/
@[to_additive "reverses the symbols in an additive free monoid element"]
def reverse : FreeMonoid α → FreeMonoid α := List.reverse

@[target, to_additive (attr := sorry

@[to_additive]
theorem reverse_mul {a b : FreeMonoid α} : reverse (a * b) = reverse b * reverse a :=
  List.reverse_append _ _

@[target, to_additive (attr := by sorry

@[to_additive (attr := simp)]
theorem length_reverse {a : FreeMonoid α} : a.reverse.length = a.length :=
  List.length_reverse _

end Reverse

section IsomorphicTypes

variable {α β : Type*}

/-- free monoids over isomorphic types are isomorphic -/
@[to_additive "if two types are isomorphic, the additive free monoids over those types are
isomorphic"]
def freeMonoidCongr (e : α ≃ β) :  FreeMonoid α ≃* FreeMonoid β where
  toFun := FreeMonoid.map ⇑e
  invFun := FreeMonoid.map ⇑e.symm
  left_inv _ := map_symm_apply_map_eq e
  right_inv _ := map_apply_map_symm_eq e
  map_mul' := by simp [map_mul]

@[target, to_additive (attr := sorry

@[to_additive (attr := simp)]
theorem freeMonoidCongr_symm_of (e : α ≃ β) (b : β) :
    freeMonoidCongr e.symm (of b) = of (e.symm b) := rfl

end IsomorphicTypes

end FreeMonoid
