/-
Exercise `exer:natural-transformations-list-free` of Section *Combinators* of *Transducers*
(M. Bojańczyk): a natural transformation whose *domain* functor does not use the list constructor
is definable by a regular term.

Naturality is the notion of `Exercises/CombNatural.lean`, already stated for functors in any number
of type variables, which is what this exercise needs.  The codomain functor is arbitrary; only the
domain is required to be list-free (`Transducers.Exercises.TyFun.ListFree`).

## The argument

The book reduces the domain, by distributivity, to a disjoint union of products of type variables,
and then observes that the transformation "constructs the output in some fixed shape, with pointers
to the input types".  The proof formalised here is the same argument organised so that no
normalisation of the domain is needed, which saves the whole distributive-normal-form
development:

* `TyFun.posTy F i` is the type of *positions* of the variable `i` in `F` -- one position for each
  leaf of `F`, the leaves of a product and of a co-product being kept apart by a co-product of
  position types.  It is a type of the book, built from `1` by `+`, and it is finite because `F`
  is list-free.  The valuation `E i = TyFun.posTy F i` is the *generic* valuation.

* `TyFun.gen F` maps an element of `F(A)` to the element of `F(E)` with the same shape whose every
  leaf holds its own position, and `TyFun.sel F i q` reads the element sitting at the position `q`
  of an element of `F(A)` (an invented element, if the shape of the element does not have that
  position).  Both are defined by recursion on `F` and both are definable by regular terms
  (`tfun_gen`, `tfun_sel`).

* The two are inverse to each other in the sense that matters, `TyFun.map_gen`:
  `F.map (fun i q => F.sel i q x) (F.gen x) = x`.  So naturality gives, for every `x`,

      f A x = G.map (fun i q => F.sel i q x) (f E (F.gen x)),

  which is the book's "fixed shape with pointers to the input": the shape is the value of `f` at
  the generic valuation, and the pointers are the positions.

* For a *fixed* `u : G(E)`, the function `x ↦ G.map (fun i q => F.sel i q x) u` is definable by a
  regular term (`tfun_mapOf`), by induction on `G`: a variable is a pointer, a product is a
  pairing, a co-product a co-projection, and a list is a fixed finite list of terms, since `u`
  itself is a fixed finite list.  This is where the codomain may use the list constructor freely.

* Finally `F(E)` is finite, `F` being list-free, so the dependence of `u = f E (F.gen x)` on `x` is
  a finite case distinction, which terms can perform (`Transducers.tfun_finCases'`).

The result is `Transducers.Exercises.natural_listFree_regularTerm`, and
`Transducers.Exercises.natural_listFree_regular` restates it as regularity under string
representation through the easy direction of Theorem `thm:regular-terms`.
-/
import RequestProject.Exercises.CombNatural

namespace Transducers
namespace Exercises

open Transducers

/-! ## List-free functors -/

/-- A functor is *list-free* if the list constructor does not occur in it. -/
def TyFun.ListFree : TyFun → Prop
  | .var _ => True
  | .one => True
  | .prod F G => F.ListFree ∧ G.ListFree
  | .sum F G => F.ListFree ∧ G.ListFree
  | .list _ => False

/-! ## Positions, the generic element and the selectors -/

/-- The type of positions of the variable `i` in the functor `F`: one position for each leaf
labelled `i`, the leaves of the two sides of a product or of a co-product being kept apart.  The
type is a type of the book, and it also has spurious elements -- a leaf that is not labelled `i`
contributes one -- which does no harm and keeps the type nonempty. -/
def TyFun.posTy : TyFun → ℕ → Ty
  | .var _, _ => .one
  | .one, _ => .one
  | .prod F G, i => .sum (F.posTy i) (G.posTy i)
  | .sum F G, i => .sum (F.posTy i) (G.posTy i)
  | .list F, i => F.posTy i

theorem TyFun.finite_posTy (F : TyFun) (i : ℕ) : Finite ((F.posTy i).Elt) := by
  induction F with
  | var j => exact inferInstanceAs (Finite Unit)
  | one => exact inferInstanceAs (Finite Unit)
  | prod F G ihF ihG =>
      haveI := ihF; haveI := ihG
      exact inferInstanceAs (Finite ((F.posTy i).Elt ⊕ (G.posTy i).Elt))
  | sum F G ihF ihG =>
      haveI := ihF; haveI := ihG
      exact inferInstanceAs (Finite ((F.posTy i).Elt ⊕ (G.posTy i).Elt))
  | list F ihF => exact ihF

/-- A list-free functor takes finite types to finite types. -/
theorem TyFun.finite_app (E : ℕ → Ty) (hE : ∀ i, Finite (E i).Elt) :
    ∀ F : TyFun, F.ListFree → Finite ((F.app E).Elt) := by
  intro F
  induction F with
  | var i => exact fun _ => hE i
  | one => exact fun _ => inferInstanceAs (Finite Unit)
  | prod F G ihF ihG =>
      intro h
      haveI := ihF h.1; haveI := ihG h.2
      exact inferInstanceAs (Finite ((F.app E).Elt × (G.app E).Elt))
  | sum F G ihF ihG =>
      intro h
      haveI := ihF h.1; haveI := ihG h.2
      exact inferInstanceAs (Finite ((F.app E).Elt ⊕ (G.app E).Elt))
  | list F _ => exact fun h => h.elim

/-- The *generic* element: an element of `F(A)` is mapped to the element of `F(E)` of the same
shape whose every leaf holds its own position.  The embedding `emb` says where the positions of the
sub-functor under consideration sit in the positions of the whole one. -/
def TyFun.gen : (F : TyFun) → {A E : ℕ → Ty} → (emb : ∀ i, (F.posTy i).Elt → (E i).Elt) →
    (F.app A).Elt → (F.app E).Elt
  | .var j, _, _, emb => fun _ => emb j ()
  | .one, _, _, _ => fun _ => ()
  | .prod F G, _, _, emb => fun p =>
      (F.gen (fun i q => emb i (Sum.inl q)) p.1, G.gen (fun i q => emb i (Sum.inr q)) p.2)
  | .sum F G, _, _, emb => fun x =>
      Sum.map (F.gen (fun i q => emb i (Sum.inl q))) (G.gen (fun i q => emb i (Sum.inr q))) x
  | .list F, _, _, emb => fun l => l.map (F.gen emb)

/-- The element sitting at the position `q` of an element of `F(A)`, and an invented element if the
shape of that element does not reach the position. -/
def TyFun.sel : (F : TyFun) → {A : ℕ → Ty} → (i : ℕ) → (F.posTy i).Elt →
    (F.app A).Elt → (A i).Elt
  | .var j, _, i, _ => fun x => if h : j = i then h ▸ x else default
  | .one, _, _, _ => fun _ => default
  | .prod F G, _, i, q => fun x =>
      Sum.elim (fun q' => F.sel i q' x.1) (fun q' => G.sel i q' x.2) q
  | .sum F G, _, i, q => fun x =>
      Sum.elim
        (fun q' => Sum.elim (fun a => F.sel i q' a) (fun _ => default) x)
        (fun q' => Sum.elim (fun _ => default) (fun b => G.sel i q' b) x) q
  | .list _, _, _, _ => fun _ => default

/-- **The generic element determines the element.**  Reading, at each position, the entry of `x`
that sits there, and substituting the result into the generic element of `x`, gives `x` back. -/
theorem TyFun.map_gen : ∀ (F : TyFun), F.ListFree → ∀ {A E : ℕ → Ty}
    (emb : ∀ i, (F.posTy i).Elt → (E i).Elt) (sel : ∀ i, (E i).Elt → (A i).Elt)
    (x : (F.app A).Elt), (∀ i q, sel i (emb i q) = F.sel i q x) →
      F.map sel (F.gen emb x) = x
  | .var j, _, _, _, emb, sel, x, h => by
      have := h j ()
      simpa [TyFun.sel] using this
  | .one, _, _, _, _, _, _, _ => rfl
  | .prod F G, hF, _, _, emb, sel, x, h => by
      have h1 : ∀ i q, sel i ((fun i q => emb i (Sum.inl q)) i q) = F.sel i q x.1 :=
        fun i q => h i (Sum.inl q)
      have h2 : ∀ i q, sel i ((fun i q => emb i (Sum.inr q)) i q) = G.sel i q x.2 :=
        fun i q => h i (Sum.inr q)
      have e1 := TyFun.map_gen F hF.1 (fun i q => emb i (Sum.inl q)) sel x.1 h1
      have e2 := TyFun.map_gen G hF.2 (fun i q => emb i (Sum.inr q)) sel x.2 h2
      show (F.map sel (F.gen _ x.1), G.map sel (G.gen _ x.2)) = x
      rw [e1, e2]
      rfl
  | .sum F G, hF, _, _, emb, sel, x, h => by
      cases x with
      | inl a =>
          have h1 : ∀ i q, sel i ((fun i q => emb i (Sum.inl q)) i q) = F.sel i q a :=
            fun i q => h i (Sum.inl q)
          have e1 := TyFun.map_gen F hF.1 (fun i q => emb i (Sum.inl q)) sel a h1
          show Sum.inl (F.map sel (F.gen _ a)) = Sum.inl a
          rw [e1]
      | inr b =>
          have h2 : ∀ i q, sel i ((fun i q => emb i (Sum.inr q)) i q) = G.sel i q b :=
            fun i q => h i (Sum.inr q)
          have e2 := TyFun.map_gen G hF.2 (fun i q => emb i (Sum.inr q)) sel b h2
          show Sum.inr (G.map sel (G.gen _ b)) = Sum.inr b
          rw [e2]

/-! ## The three definability lemmas -/

/-- Reading the entry at a fixed position is definable by a regular term. -/
theorem tfun_sel : ∀ (F : TyFun), F.ListFree → ∀ (A : ℕ → Ty) (i : ℕ) (q : (F.posTy i).Elt),
    IsRegularTermFun (A := F.app A) (B := A i) (fun x => F.sel i q x)
  | .var j, _, A, i, _ => by
      by_cases h : j = i
      · subst h
        exact (tfun_id (A j)).congr (fun x => by simp [TyFun.sel])
      · exact (tfun_const (A j) (A i) default).congr (fun x => by simp [TyFun.sel, h])
  | .one, _, A, i, _ => tfun_const .one (A i) default
  | .prod F G, hF, A, i, q => by
      cases q with
      | inl q' => exact (tfun_fst (F.app A) (G.app A)).comp (tfun_sel F hF.1 A i q')
      | inr q' => exact (tfun_snd (F.app A) (G.app A)).comp (tfun_sel G hF.2 A i q')
  | .sum F G, hF, A, i, q => by
      cases q with
      | inl q' =>
          exact ((tfun_sel F hF.1 A i q').copair
            (tfun_const (G.app A) (A i) default)).congr (fun x => by cases x <;> rfl)
      | inr q' =>
          exact ((tfun_const (F.app A) (A i) default).copair
            (tfun_sel G hF.2 A i q')).congr (fun x => by cases x <;> rfl)

/-- Passing to the generic element is definable by a regular term. -/
theorem tfun_gen : ∀ (F : TyFun), F.ListFree → ∀ (A E : ℕ → Ty)
    (emb : ∀ i, (F.posTy i).Elt → (E i).Elt),
    IsRegularTermFun (A := F.app A) (B := F.app E) (F.gen emb)
  | .var j, _, A, E, emb => tfun_const (A j) (E j) (emb j ())
  | .one, _, _, _, _ => tfun_const .one .one ()
  | .prod F G, hF, A, E, emb =>
      (((tfun_fst (F.app A) (G.app A)).comp
        (tfun_gen F hF.1 A E (fun i q => emb i (Sum.inl q)))).pair
       ((tfun_snd (F.app A) (G.app A)).comp
        (tfun_gen G hF.2 A E (fun i q => emb i (Sum.inr q))))).congr (fun _ => rfl)
  | .sum F G, hF, A, E, emb =>
      ((tfun_gen F hF.1 A E (fun i q => emb i (Sum.inl q))).sumMap
        (tfun_gen G hF.2 A E (fun i q => emb i (Sum.inr q)))).congr (fun x => by cases x <;> rfl)

/-- **The fixed shape with pointers is definable.**  For a fixed element `u` of `G(E)`, the
function that replaces every leaf of `u` by the entry of the input that its position points to is
definable by a regular term, whatever the codomain functor `G` -- a variable is a pointer, a
product a pairing, a co-product a co-projection, and a list a fixed finite list of terms. -/
theorem tfun_mapOf : ∀ (G : TyFun) {D : Ty} {A E : ℕ → Ty}
    (sel : ∀ i, (E i).Elt → D.Elt → (A i).Elt),
    (∀ i q, IsRegularTermFun (A := D) (B := A i) (fun x => sel i q x)) →
    ∀ u : (G.app E).Elt,
      IsRegularTermFun (A := D) (B := G.app A) (fun x => G.map (fun i q => sel i q x) u)
  | .var i, _, _, _, sel, hsel, u => hsel i u
  | .one, D, _, _, _, _, _ => tfun_const D .one ()
  | .prod G₁ G₂, _, _, _, sel, hsel, u =>
      ((tfun_mapOf G₁ sel hsel u.1).pair (tfun_mapOf G₂ sel hsel u.2)).congr (fun _ => rfl)
  | .sum G₁ G₂, _, A, _, sel, hsel, u => by
      cases u with
      | inl v =>
          exact ((tfun_mapOf G₁ sel hsel v).comp (tfun_inl (G₁.app A) (G₂.app A))).congr
            (fun _ => rfl)
      | inr v =>
          exact ((tfun_mapOf G₂ sel hsel v).comp (tfun_inr (G₁.app A) (G₂.app A))).congr
            (fun _ => rfl)
  | .list G₁, D, A, _, sel, hsel, u => by
      induction u with
      | nil => exact (tfun_const D (.list (G₁.app A)) []).congr (fun _ => rfl)
      | cons v l ih =>
          refine ((((tfun_mapOf G₁ sel hsel v).pair ih).comp
            (tfun_inr .one (.prod (G₁.app A) (.list (G₁.app A))))).comp
              (tfun_cons (G₁.app A))).congr (fun _ => rfl)

/-! ## The exercise -/

/-- **Exercise `exer:natural-transformations-list-free`.**  A natural transformation whose domain
functor does not use the list constructor is definable by a regular term, at every valuation of
its type variables.  The codomain functor is arbitrary, and the number of type variables is
arbitrary. -/
theorem natural_listFree_regularTerm {F G : TyFun} (hF : F.ListFree)
    (f : ∀ A : ℕ → Ty, (F.app A).Elt → (G.app A).Elt) (hf : IsNatural F G f) (A : ℕ → Ty) :
    IsRegularTermFun (A := F.app A) (B := G.app A) (f A) := by
  classical
  set E : ℕ → Ty := fun i => F.posTy i with hE
  have key : ∀ x : (F.app A).Elt,
      f A x = G.map (fun i q => F.sel i q x) (f E (F.gen (fun _ q => q) x)) := by
    intro x
    have h := hf E A (fun i q => F.sel i q x) (F.gen (fun _ q => q) x)
    rw [h, TyFun.map_gen F hF (fun _ q => q) (fun i q => F.sel i q x) x (fun _ _ => rfl)]
  have hfin : Finite ((F.app E).Elt) :=
    TyFun.finite_app E (fun i => TyFun.finite_posTy F i) F hF
  have hpair : IsRegularTermFun (A := F.app A) (B := .prod (F.app E) (F.app A))
      (fun x => (F.gen (fun _ q => q) x, x)) :=
    (tfun_gen F hF A E (fun _ q => q)).pair (tfun_id (F.app A))
  have hcases : IsRegularTermFun (A := Ty.prod (F.app E) (F.app A)) (B := G.app A)
      (fun p => G.map (fun i q => F.sel i q p.2) (f E p.1)) :=
    tfun_finCases' hfin (fun u => tfun_mapOf G (fun i q x => F.sel i q x)
      (fun i q => tfun_sel F hF A i q) (f E u))
  exact (hpair.comp hcases).congr (fun x => (key x).symm)

/-- **Exercise `exer:natural-transformations-list-free`, as the book states it.**  Such a natural
transformation is in particular regular under string representation, by the easy direction of
Theorem `thm:regular-terms`. -/
theorem natural_listFree_regular {F G : TyFun} (hF : F.ListFree)
    (f : ∀ A : ℕ → Ty, (F.app A).Elt → (G.app A).Elt) (hf : IsNatural F G f) (A : ℕ → Ty) :
    IsRegularUnderRepr (A := F.app A) (B := G.app A) (f A) :=
  regularTerm_isRegular (natural_listFree_regularTerm hF f hf A)

end Exercises
end Transducers
