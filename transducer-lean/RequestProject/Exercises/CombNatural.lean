/-
Naturality, and the first exercises about it, of Section *Combinators* of *Transducers*
(M. Bojańczyk).

The exercises after Exercise `exer:windows-of-size-two` are about *natural transformations* between
the type functors of Definition `def:types`, a notion the book introduces in the text between
Exercise `exer:natural-identity` and Exercise `exer:head-operation-natural`.  Nothing of it was in
the project, so this file defines it, and the later files of the group
(`Exercises/CombNaturalAtoms.lean`, `Exercises/CombNaturalFree.lean`) use the same definition.

## What a functor is here, and why

The book says: *a functor is an expression built from a type variable `A` using the type
constructors of Definition `def:types`*, and adds, in Exercise
`exer:natural-transformations-from-regular-terms`, that the notion extends to several type
variables.  Since several variables are needed for four of the six exercises, the definition is
given once, for any number of variables, and the one-variable exercises use the variable `0`:

* `Transducers.Exercises.TyFun` is the syntax of a functor -- a type variable `var i` indexed by a
  natural number, the unit type, and the product, co-product and list constructors of
  `Transducers.Ty`;
* a *valuation* of the variables is a function `A : ℕ → Ty`, and `TyFun.app F A : Ty` is the type
  that `F` denotes under it, so that a functor really is an operation on the types of the book and
  not on arbitrary Lean types;
* `TyFun.map F g` is the action of `F` on a family of functions `g i : (A i).Elt → (B i).Elt`,
  by recursion on `F`;
* a family of functions is then indexed by a valuation, `f : ∀ A : ℕ → Ty, (F.app A).Elt →
  (G.app A).Elt`, and `Transducers.Exercises.IsNatural F G f` says that the book's square commutes:
  `G.map g (f A x) = f B (F.map g x)` for every `A`, `B`, every family `g` and every `x`.

Three choices are worth spelling out.

* *Variables are indexed by `ℕ` and a family is indexed by a valuation of all of them*, rather than
  by `Fin n` for a fixed arity with families indexed by `n` types.  This keeps one definition for
  all arities -- `IsNatural` is never applied at a "number of variables" -- and costs nothing: a
  functor mentions finitely many variables, and the naturality square for a valuation that differs
  elsewhere is available all the same.  For a one-variable functor the family `f` is thus indexed
  by a valuation rather than by a single type; this is a *weaker* hypothesis than the book's
  (`f` may in principle depend on the values of the other variables), so the negative statements
  below (Exercise `exer:head-operation-natural`) and the classification statements (Exercises
  `exer:natural-transformations-from-A`, `exer:natural-transformations-list-free`) are, if
  anything, slightly stronger than the book's, and the positive ones (Exercise
  `exer:natural-list-function`) exhibit families that do not use that extra freedom.

* *The functions `g` range over all functions between the sets of elements of two types*, with no
  regularity or definability requirement, exactly as in the book: the square is asked to commute
  "for every function `g : A → B`".

* *Naturality is a `Prop` about a family, not a structure*: there is no bundled type of natural
  transformations, so that statements can be made about families that are given by a formula, such
  as `fun A l => l.reverse`.

## What is in this file

* Exercise `exer:natural-identity`: a natural family `A → A` is the identity at every type
  (`natural_id_eq_id`).  This is the exercise that fixes the definition.
* Exercise `exer:head-operation-natural`: there is no natural transformation `A* → A`
  (`no_natural_head`); in particular the `head` of Claim `claim:head` is not one
  (`not_natural_head_of_claim`).
* Exercise `exer:natural-list-function`: there are uncountably many natural transformations
  `A* → A*` (`uncountably_many_natural_list`), by the author's construction restricted to the
  families `lenSelect b` that keep the input list or erase it according to a Boolean read off its
  length.
* Exercise `exer:natural-transformations-from-A`: every natural transformation `A → A*` repeats
  its argument a fixed number of times (`natural_toList_eq_replicate`) and is therefore regular at
  every type (`natural_toList_regular`), indeed defined by a regular term
  (`natural_toList_regularTerm`).
-/
import RequestProject.PartC.CombDerived
import RequestProject.PartC.CombStatements

namespace Transducers
namespace Exercises

open Transducers

/-! ## Functors and natural transformations -/

/-- **A type functor.**  An expression built from type variables `var i`, one for each natural
number, by the constructors of Definition `def:types`: the unit type, the product, the co-product
and the list constructor.  The book's `F(A) = A*` is `TyFun.list (TyFun.var 0)`, and its
`G(A) = 1 + A × A*` is `TyFun.sum TyFun.one (TyFun.prod (TyFun.var 0) (TyFun.list (TyFun.var 0)))`.
Several variables are allowed, as Exercise `exer:natural-transformations-from-regular-terms` asks
for. -/
inductive TyFun : Type
  | var (i : ℕ) : TyFun
  | one : TyFun
  | prod : TyFun → TyFun → TyFun
  | sum : TyFun → TyFun → TyFun
  | list : TyFun → TyFun
  deriving DecidableEq

/-- The type that a functor denotes when its variables are given the values `A`. -/
def TyFun.app : TyFun → (ℕ → Ty) → Ty
  | .var i, A => A i
  | .one, _ => .one
  | .prod F G, A => .prod (F.app A) (G.app A)
  | .sum F G, A => .sum (F.app A) (G.app A)
  | .list F, A => .list (F.app A)

@[simp] lemma TyFun.app_var (i : ℕ) (A : ℕ → Ty) : (TyFun.var i).app A = A i := rfl
@[simp] lemma TyFun.app_one (A : ℕ → Ty) : TyFun.one.app A = .one := rfl
@[simp] lemma TyFun.app_prod (F G : TyFun) (A : ℕ → Ty) :
    (TyFun.prod F G).app A = .prod (F.app A) (G.app A) := rfl
@[simp] lemma TyFun.app_sum (F G : TyFun) (A : ℕ → Ty) :
    (TyFun.sum F G).app A = .sum (F.app A) (G.app A) := rfl
@[simp] lemma TyFun.app_list (F : TyFun) (A : ℕ → Ty) :
    (TyFun.list F).app A = .list (F.app A) := rfl

/-- **The action of a functor on functions.**  A family of functions `g i : A i → B i`, one for
each type variable, is lifted along the constructors of the functor. -/
def TyFun.map : (F : TyFun) → {A B : ℕ → Ty} → (g : ∀ i, (A i).Elt → (B i).Elt) →
    (F.app A).Elt → (F.app B).Elt
  | .var i, _, _, g => g i
  | .one, _, _, _ => fun _ => ()
  | .prod F G, _, _, g => fun p => (F.map g p.1, G.map g p.2)
  | .sum F G, _, _, g => fun x => Sum.map (F.map g) (G.map g) x
  | .list F, _, _, g => fun l => l.map (F.map g)

@[simp] lemma TyFun.map_var {A B : ℕ → Ty} (i : ℕ) (g : ∀ i, (A i).Elt → (B i).Elt)
    (x : (A i).Elt) : (TyFun.var i).map g x = g i x := rfl

@[simp] lemma TyFun.map_one {A B : ℕ → Ty} (g : ∀ i, (A i).Elt → (B i).Elt)
    (x : (TyFun.one.app A).Elt) : TyFun.one.map g x = () := rfl

@[simp] lemma TyFun.map_prod {A B : ℕ → Ty} (F G : TyFun) (g : ∀ i, (A i).Elt → (B i).Elt)
    (p : ((TyFun.prod F G).app A).Elt) :
    (TyFun.prod F G).map g p = (F.map g p.1, G.map g p.2) := rfl

@[simp] lemma TyFun.map_sum {A B : ℕ → Ty} (F G : TyFun) (g : ∀ i, (A i).Elt → (B i).Elt)
    (x : ((TyFun.sum F G).app A).Elt) :
    (TyFun.sum F G).map g x = Sum.map (F.map g) (G.map g) x := rfl

@[simp] lemma TyFun.map_list {A B : ℕ → Ty} (F : TyFun) (g : ∀ i, (A i).Elt → (B i).Elt)
    (l : ((TyFun.list F).app A).Elt) :
    (TyFun.list F).map g l = l.map (F.map g) := rfl

/-- **A natural transformation.**  A family of functions `F(A) → G(A)`, one for each valuation of
the type variables, is *natural* if the book's square commutes for every family of functions
`g i : A i → B i`. -/
def IsNatural (F G : TyFun) (f : ∀ A : ℕ → Ty, (F.app A).Elt → (G.app A).Elt) : Prop :=
  ∀ (A B : ℕ → Ty) (g : ∀ i, (A i).Elt → (B i).Elt) (x : (F.app A).Elt),
    G.map g (f A x) = f B (F.map g x)

/-- Natural transformations are closed under composition, as the solution of Exercise
`exer:natural-transformations-list-free` observes. -/
theorem IsNatural.comp {F G H : TyFun} {f : ∀ A, (F.app A).Elt → (G.app A).Elt}
    {h : ∀ A, (G.app A).Elt → (H.app A).Elt} (hf : IsNatural F G f) (hh : IsNatural G H h) :
    IsNatural F H (fun A x => h A (f A x)) := by
  intro A B g x
  rw [hh A B g (f A x), hf A B g x]

/-! ## Exercise `exer:natural-identity`: a natural family `A → A` is the identity -/

/-- **Exercise `exer:natural-identity`.**  A family of functions `f_A : A → A`, natural in the
sense that `f;g = g;f` for every `g`, is the identity at every type.

This is the author's argument, which does not even compare two different types: given `a`, the
naturality square for the constant function `g` with value `a` reads `a = g (f a) = f (g a) =
f a`. -/
theorem natural_id_eq_id
    (f : ∀ A : ℕ → Ty, ((TyFun.var 0).app A).Elt → ((TyFun.var 0).app A).Elt)
    (hf : IsNatural (.var 0) (.var 0) f) (A : ℕ → Ty) (a : (A 0).Elt) :
    f A a = a := by
  have key := hf A A (fun i x => match i with | 0 => a | _ + 1 => x) a
  exact key.symm

/-! ## Exercise `exer:head-operation-natural`: no natural transformation `A* → A` -/

/-- **Exercise `exer:head-operation-natural`.**  There is no natural transformation of type
`A* → A`.

The author's argument: apply the candidate to the empty list at some type `A`, and map into the
two-element type `1 + 1` by the two constant functions.  Naturality makes both constants equal to
the value of the candidate on the empty list of `1 + 1`, hence equal to each other. -/
theorem no_natural_head :
    ¬ ∃ f : ∀ A : ℕ → Ty, ((TyFun.list (.var 0)).app A).Elt → ((TyFun.var 0).app A).Elt,
        IsNatural (.list (.var 0)) (.var 0) f := by
  rintro ⟨f, hf⟩
  have h₁ := hf (fun _ => .one) (fun _ => .sum .one .one) (fun _ _ => Sum.inl ()) []
  have h₂ := hf (fun _ => .one) (fun _ => .sum .one .one) (fun _ _ => Sum.inr ()) []
  simp only [TyFun.map_var, TyFun.map_list, List.map_nil] at h₁ h₂
  exact Sum.inl_ne_inr (h₁.trans h₂.symm)

/-- **Exercise `exer:head-operation-natural`, second half.**  In particular the `head` operation of
Claim `claim:head` -- the first entry of the list, and an invented element for the empty list -- is
not a natural transformation. -/
theorem not_natural_head_of_claim :
    ¬ IsNatural (.list (.var 0)) (.var 0)
        (fun (A : ℕ → Ty) (l : ((TyFun.list (.var 0)).app A).Elt) => l.headI) :=
  fun h => no_natural_head ⟨_, h⟩

/-! ## Exercise `exer:natural-list-function`: uncountably many natural transformations `A* → A*` -/

/-- The family of natural transformations `A* → A*` used for Exercise `exer:natural-list-function`:
the input list is kept or erased according to the Boolean that `b` attaches to its length.  These
are the author's transformations for the maps `α` that send `n` either to `[1,…,n]` or to the empty
list; only the length of the input is inspected, which is what makes them natural, and there are
continuum many of them because `b` is arbitrary. -/
def lenSelect (b : ℕ → Bool) (A : ℕ → Ty) (l : ((TyFun.list (.var 0)).app A).Elt) :
    ((TyFun.list (.var 0)).app A).Elt :=
  if b l.length then l else []

theorem lenSelect_natural (b : ℕ → Bool) :
    IsNatural (.list (.var 0)) (.list (.var 0)) (lenSelect b) := by
  intro A B g l
  by_cases h : b l.length <;> simp [lenSelect, h]

/-- **Exercise `exer:natural-list-function`.**  There are uncountably many natural transformations
of type `A* → A*`.

The transformations `lenSelect b` are pairwise different for different `b`, and there are
uncountably many Booleans-valued functions on `ℕ`; the shift `n ↦ b (n-1)` is there because the
length `0` cannot separate two of them. -/
theorem uncountably_many_natural_list :
    ¬ Countable {f : ∀ A : ℕ → Ty, ((TyFun.list (.var 0)).app A).Elt →
        ((TyFun.list (.var 0)).app A).Elt // IsNatural (.list (.var 0)) (.list (.var 0)) f} := by
  intro hc
  have hinj : Function.Injective
      (fun b : ℕ → Bool => (⟨lenSelect (fun n => b (n - 1)), lenSelect_natural _⟩ :
        {f : ∀ A : ℕ → Ty, ((TyFun.list (.var 0)).app A).Elt →
          ((TyFun.list (.var 0)).app A).Elt // IsNatural (.list (.var 0)) (.list (.var 0)) f})) := by
    intro b b' hb
    funext n
    have h := congrArg Subtype.val hb
    have h' := congrFun (congrFun h (fun _ => Ty.one)) (List.replicate (n + 1) ())
    simp only [lenSelect, List.length_replicate, Nat.add_sub_cancel] at h'
    cases hbn : b n <;> cases hbn' : b' n <;> rw [hbn, hbn'] at h' <;>
      simp_all [List.replicate_succ]
  have hcount : Countable (ℕ → Bool) := hinj.countable
  have h1 : Cardinal.mk (ℕ → Bool) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id,
    Cardinal.two_power_aleph0] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

/-! ## Exercise `exer:natural-transformations-from-A`: natural transformations `A → A*` -/

/-- **Exercise `exer:natural-transformations-from-A`, the classification.**  A natural
transformation of type `A → A*` repeats its argument a fixed number of times, the number being the
length of its value at the unit type.

The argument is the author's: the value at an arbitrary `a` is the image, under the map that sends
the unique element of the unit type to `a`, of the value at the unit type. -/
theorem natural_toList_eq_replicate
    (f : ∀ A : ℕ → Ty, ((TyFun.var 0).app A).Elt → ((TyFun.list (.var 0)).app A).Elt)
    (hf : IsNatural (.var 0) (.list (.var 0)) f) (A : ℕ → Ty) (a : (A 0).Elt) :
    f A a = List.replicate (f (fun _ => .one) ()).length a := by
  have key := hf (fun _ => .one) A
    (fun i _ => match i with | 0 => a | _ + 1 => default) ()
  simp only [TyFun.map_var, TyFun.map_list] at key
  rw [← key]
  exact List.map_const'

/-- Repeating the argument a fixed number of times is defined by a regular term. -/
theorem tfun_replicate (A : Ty) : ∀ n : ℕ,
    IsRegularTermFun (A := A) (B := .list A) (fun a => List.replicate n a)
  | 0 => ((bang_definable A).comp (tfun_nil A)).congr (fun _ => rfl)
  | n + 1 => by
      refine ((((tfun_id A).pair (tfun_replicate A n)).comp
        (tfun_inr .one (.prod A (.list A)))).comp (tfun_cons A)).congr (fun a => rfl)

/-- **Exercise `exer:natural-transformations-from-A`.**  Every natural transformation of type
`A → A*` is defined by a regular term, at every type. -/
theorem natural_toList_regularTerm
    (f : ∀ A : ℕ → Ty, ((TyFun.var 0).app A).Elt → ((TyFun.list (.var 0)).app A).Elt)
    (hf : IsNatural (.var 0) (.list (.var 0)) f) (A : ℕ → Ty) :
    IsRegularTermFun (A := A 0) (B := .list (A 0)) (f A) :=
  (tfun_replicate (A 0) (f (fun _ => .one) ()).length).congr
    (fun a => (natural_toList_eq_replicate f hf A a).symm)

/-- **Exercise `exer:natural-transformations-from-A`, as the book states it.**  Every natural
transformation of type `A → A*` is regular, at every type: regular under string representation, in
the sense of Definition `def:regular-functions-on-types-under-string-representation`. -/
theorem natural_toList_regular
    (f : ∀ A : ℕ → Ty, ((TyFun.var 0).app A).Elt → ((TyFun.list (.var 0)).app A).Elt)
    (hf : IsNatural (.var 0) (.list (.var 0)) f) (A : ℕ → Ty) :
    IsRegularUnderRepr (A := A 0) (B := .list (A 0)) (f A) :=
  regularTerm_isRegular (natural_toList_regularTerm f hf A)

end Exercises
end Transducers
