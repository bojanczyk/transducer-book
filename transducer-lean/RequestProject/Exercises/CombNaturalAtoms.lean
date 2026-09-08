/-
Exercise `exer:natural-transformations-from-regular-terms` of Section *Combinators* of
*Transducers* (M. Bojańczyk): the atomic functions of Definition `def:regular-terms` are natural
transformations.

Naturality is the notion of `Exercises/CombNatural.lean`, which is already stated for functors in
any number of type variables, as this exercise asks; so nothing has to be extended here, and each
atomic function of Definition `def:regular-terms` is stated as a family indexed by a valuation of
the variables it uses:

| atomic function | domain functor | codomain functor |
| --- | --- | --- |
| identity | `var 0` | `var 0` |
| projections | `var 0 × var 1` | `var 0`, `var 1` |
| co-projections | `var 0`, `var 1` | `var 0 + var 1` |
| diagonal | `var 0` | `var 0 × var 0` |
| co-diagonal | `var 0 + var 0` | `var 0` |
| distributivity | `var 0 × (var 1 + var 2)` | `var 0 × var 1 + var 0 × var 2` |
| list constructor | `1 + var 0 × var 0*` | `var 0*` |
| list deconstructor | `var 0*` | `1 + var 0 × var 0*` |
| reverse | `var 0*` | `var 0*` |
| concatenation | `var 0**` | `var 0*` |
| block | `(var 0 + var 1)*` | `var 0* × (var 1 × var 0*)*` |

The semantics used for each of them is the one the project already fixed in
`Transducers.RegTerm.eval`, so this file states naturality of the *same* functions that the term
language evaluates to, and not of a fresh copy of them.

Group prefix multiplication is left out, as the book leaves it out: it is parameterised by a group
and not by a type, so it is not a family indexed by the types at all and the question does not
arise for it.

`Transducers.Exercises.regTerm_atomics_natural` collects the eleven statements in one theorem;
the individual lemmas are stated separately above it.
-/
import RequestProject.Exercises.CombNatural

namespace Transducers
namespace Exercises

open Transducers

/-! ## The atomic functions, one at a time -/

/-- The identity is a natural transformation. -/
theorem natural_id : IsNatural (.var 0) (.var 0) (fun _ x => x) := by
  intro A B g x; rfl

/-- The first projection is a natural transformation. -/
theorem natural_fst :
    IsNatural (.prod (.var 0) (.var 1)) (.var 0)
      (fun (A : ℕ → Ty) (p : ((TyFun.prod (.var 0) (.var 1)).app A).Elt) => p.1) := by
  intro A B g p; rfl

/-- The second projection is a natural transformation. -/
theorem natural_snd :
    IsNatural (.prod (.var 0) (.var 1)) (.var 1)
      (fun (A : ℕ → Ty) (p : ((TyFun.prod (.var 0) (.var 1)).app A).Elt) => p.2) := by
  intro A B g p; rfl

/-- The left co-projection is a natural transformation. -/
theorem natural_inl :
    IsNatural (.var 0) (.sum (.var 0) (.var 1))
      (fun (A : ℕ → Ty) (a : (A 0).Elt) => Sum.inl a) := by
  intro A B g a; rfl

/-- The right co-projection is a natural transformation. -/
theorem natural_inr :
    IsNatural (.var 1) (.sum (.var 0) (.var 1))
      (fun (A : ℕ → Ty) (b : (A 1).Elt) => Sum.inr b) := by
  intro A B g b; rfl

/-- The diagonal is a natural transformation. -/
theorem natural_diag :
    IsNatural (.var 0) (.prod (.var 0) (.var 0)) (fun (A : ℕ → Ty) (a : (A 0).Elt) => (a, a)) := by
  intro A B g a; rfl

/-- The co-diagonal is a natural transformation. -/
theorem natural_codiag :
    IsNatural (.sum (.var 0) (.var 0)) (.var 0)
      (fun (A : ℕ → Ty) (x : ((TyFun.sum (.var 0) (.var 0)).app A).Elt) =>
        Sum.elim (fun a => a) (fun a => a) x) := by
  intro A B g x
  cases x <;> rfl

/-- Distributivity is a natural transformation. -/
theorem natural_distr :
    IsNatural (.prod (.var 0) (.sum (.var 1) (.var 2)))
      (.sum (.prod (.var 0) (.var 1)) (.prod (.var 0) (.var 2)))
      (fun (A : ℕ → Ty) (x : ((TyFun.prod (.var 0) (.sum (.var 1) (.var 2))).app A).Elt) =>
        Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2) := by
  intro A B g x
  obtain ⟨a, bc⟩ := x
  cases bc <;> rfl

/-- The list constructor is a natural transformation. -/
theorem natural_cons :
    IsNatural (.sum .one (.prod (.var 0) (.list (.var 0)))) (.list (.var 0))
      (fun (A : ℕ → Ty)
        (x : ((TyFun.sum .one (.prod (.var 0) (.list (.var 0)))).app A).Elt) =>
          Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x) := by
  intro A B g x
  cases x <;> rfl

/-- The list deconstructor is a natural transformation. -/
theorem natural_uncons :
    IsNatural (.list (.var 0)) (.sum .one (.prod (.var 0) (.list (.var 0))))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.var 0)).app A).Elt) =>
        match l with
        | [] => Sum.inl ()
        | a :: l' => Sum.inr (a, l')) := by
  intro A B g l
  cases l <;> rfl

/-- Reverse is a natural transformation. -/
theorem natural_reverse :
    IsNatural (.list (.var 0)) (.list (.var 0))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.var 0)).app A).Elt) => l.reverse) := by
  intro A B g l
  simp

/-- Concatenation is a natural transformation. -/
theorem natural_concat :
    IsNatural (.list (.list (.var 0))) (.list (.var 0))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.list (.var 0))).app A).Elt) => l.flatten) := by
  intro A B g l
  simp only [TyFun.map_list, List.map_flatten]
  rfl

/-- The block function of Example `ex:block` commutes with a relabelling of the two summands. -/
lemma splitList_map {A₀ A₁ B₀ B₁ : Type} (g₀ : A₀ → B₀) (g₁ : A₁ → B₁) (l : List (A₀ ⊕ A₁)) :
    splitList (l.map (Sum.map g₀ g₁))
      = ((splitList l).1.map g₀,
        (splitList l).2.map (fun p => (g₁ p.1, p.2.map g₀))) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases a with
      | inl a => simp [ih]
      | inr b => simp [ih]

/-- The block function of Example `ex:block` is a natural transformation. -/
theorem natural_split :
    IsNatural (.list (.sum (.var 0) (.var 1)))
      (.prod (.list (.var 0)) (.list (.prod (.var 1) (.list (.var 0)))))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.sum (.var 0) (.var 1))).app A).Elt) => splitList l) := by
  intro A B g l
  exact (splitList_map (g 0) (g 1) l).symm

/-! ## The exercise -/

/-- **Exercise `exer:natural-transformations-from-regular-terms`.**  Every atomic function of
Definition `def:regular-terms`, group prefix multiplication aside, is a natural transformation
between the functors that give its type -- functors in several type variables, which is the
extension of naturality the exercise asks for and which
`Transducers.Exercises.IsNatural` already provides.

Group prefix multiplication is not covered, as in the book: it is parameterised by a group rather
than by a type, so it is not a family indexed by the types. -/
theorem regTerm_atomics_natural :
    IsNatural (.var 0) (.var 0) (fun _ x => x) ∧
    IsNatural (.prod (.var 0) (.var 1)) (.var 0)
      (fun (A : ℕ → Ty) (p : ((TyFun.prod (.var 0) (.var 1)).app A).Elt) => p.1) ∧
    IsNatural (.prod (.var 0) (.var 1)) (.var 1)
      (fun (A : ℕ → Ty) (p : ((TyFun.prod (.var 0) (.var 1)).app A).Elt) => p.2) ∧
    IsNatural (.var 0) (.sum (.var 0) (.var 1))
      (fun (A : ℕ → Ty) (a : (A 0).Elt) => Sum.inl a) ∧
    IsNatural (.var 1) (.sum (.var 0) (.var 1))
      (fun (A : ℕ → Ty) (b : (A 1).Elt) => Sum.inr b) ∧
    IsNatural (.var 0) (.prod (.var 0) (.var 0)) (fun (A : ℕ → Ty) (a : (A 0).Elt) => (a, a)) ∧
    IsNatural (.sum (.var 0) (.var 0)) (.var 0)
      (fun (A : ℕ → Ty) (x : ((TyFun.sum (.var 0) (.var 0)).app A).Elt) =>
        Sum.elim (fun a => a) (fun a => a) x) ∧
    IsNatural (.prod (.var 0) (.sum (.var 1) (.var 2)))
      (.sum (.prod (.var 0) (.var 1)) (.prod (.var 0) (.var 2)))
      (fun (A : ℕ → Ty) (x : ((TyFun.prod (.var 0) (.sum (.var 1) (.var 2))).app A).Elt) =>
        Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2) ∧
    IsNatural (.sum .one (.prod (.var 0) (.list (.var 0)))) (.list (.var 0))
      (fun (A : ℕ → Ty)
        (x : ((TyFun.sum .one (.prod (.var 0) (.list (.var 0)))).app A).Elt) =>
          Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x) ∧
    IsNatural (.list (.var 0)) (.sum .one (.prod (.var 0) (.list (.var 0))))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.var 0)).app A).Elt) =>
        match l with
        | [] => Sum.inl ()
        | a :: l' => Sum.inr (a, l')) ∧
    IsNatural (.list (.var 0)) (.list (.var 0))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.var 0)).app A).Elt) => l.reverse) ∧
    IsNatural (.list (.list (.var 0))) (.list (.var 0))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.list (.var 0))).app A).Elt) => l.flatten) ∧
    IsNatural (.list (.sum (.var 0) (.var 1)))
      (.prod (.list (.var 0)) (.list (.prod (.var 1) (.list (.var 0)))))
      (fun (A : ℕ → Ty) (l : ((TyFun.list (.sum (.var 0) (.var 1))).app A).Elt) =>
        splitList l) :=
  ⟨natural_id, natural_fst, natural_snd, natural_inl, natural_inr, natural_diag, natural_codiag,
    natural_distr, natural_cons, natural_uncons, natural_reverse, natural_concat, natural_split⟩

end Exercises
end Transducers
