/-
Part D, Section *A functional programming language*: natural transformations, Claim
`claim:atomic-functions-are-natural-transformations` and Claim `claim:functors-applied-to-good`.

The induction basis of the Fundamental Lemma -- the case of the atomic functions -- rests on two
observations of the book.  Every atomic function is not a single function but a family

    F(A₁,…,Aₙ) → G(A₁,…,Aₙ),

indexed by type parameters, whose domain and co-domain are expressions built from the parameters
using the *arrow-free* type constructors; the family is *natural*, in that it commutes with the
lifting of arbitrary functions `Aᵢ → Bᵢ` to those expressions; and a good function into such an
expression always factors through the expression applied to arrow-free parameter types.

This file formalises all three.

* `Transducers.HTyFun` is an expression built from type variables `var i`, one for every natural
  number, and from fixed arrow-free types, by the constructors `1`, `×`, `+` and `*`;
  `Transducers.HTyFun.app` applies it to a valuation `A : ℕ → HTy` of the variables, and
  `Transducers.HTyFun.map` is its action on functions -- the lifting `F(ρ₁,…,ρₙ)` of the book.  A
  fixed arrow-free type is allowed as a leaf (`Transducers.HTyFun.const`) because two atomic
  functions, group prefix multiplication and the product of a list, are families over a fixed group
  type rather than over a type parameter; such a leaf carries no parameter, so the lifting acts on
  it as the identity.

  This mirrors `Transducers.Exercises.TyFun` of `RequestProject/Exercises/CombNatural.lean`, which
  is the same notion for the exercises of Section *Combinators*, with the same convention that the
  variables are indexed by `ℕ` and a family is indexed by a valuation of all of them.  It is a
  separate definition because the parameters here are *higher-order* types, which is exactly what
  the Fundamental Lemma needs and what the type functors of Part C cannot express.

* `Transducers.IsNaturalTransformation` is the Definition of a natural transformation of the book,
  which carries no `\label` there and is therefore not aliased in `RequestProject/Labels.lean`: for
  all functions `ρᵢ : Aᵢ → Bᵢ`, which are required to be neither good nor polyregular, the square
  of the definition commutes.

* `Transducers.atoms_are_natural` is Claim `claim:atomic-functions-are-natural-transformations`,
  and `Transducers.good_of_functor_applied` is Claim `claim:functors-applied-to-good`.

The two atomic functions `map` and `either` are absent from the first claim, and necessarily so:
their types are not of the form `F(A₁,…,Aₙ) → G(A₁,…,Aₙ)` with `F` and `G` arrow-free, since their
arguments are themselves functions, so the book's definition of a natural transformation does not
apply to them.  They are the atomic functions that the book treats in the *combinator* case of the
Fundamental Lemma instead.  All the others appear, each with the arity the book gives it -- at most
three type parameters, which are the variables `0`, `1` and `2` -- and each is stated for every
valuation, of which it uses as many variables as it needs.
-/
import RequestProject.PartD.HORel

namespace Transducers

open Comb

/-! ## Arrow-free type functors -/

/-- An expression built from type variables, and from fixed arrow-free types, by the arrow-free
type constructors `1`, `×`, `+` and `*`.  These are the expressions `F(A₁,…,Aₙ)` in which the book
states the domain and the co-domain of an atomic function; the parameters may be higher-order
types. -/
inductive HTyFun : Type
  /-- The type variable with index `i`. -/
  | var : ℕ → HTyFun
  /-- A fixed arrow-free type, which carries no parameter. -/
  | const : Ty → HTyFun
  /-- The unit type. -/
  | one : HTyFun
  /-- A product. -/
  | prod : HTyFun → HTyFun → HTyFun
  /-- A co-product. -/
  | sum : HTyFun → HTyFun → HTyFun
  /-- A list type. -/
  | list : HTyFun → HTyFun

/-- The higher-order type that an expression denotes under a valuation of its variables. -/
def HTyFun.app : HTyFun → (ℕ → HTy) → HTy
  | .var i, A => A i
  | .const C, _ => HTy.ofTy C
  | .one, _ => .one
  | .prod F G, A => .prod (F.app A) (G.app A)
  | .sum F G, A => .sum (F.app A) (G.app A)
  | .list F, A => .list (F.app A)

/-- **The lifting `F(ρ₁,…,ρₙ)` of the book**: the action of an expression on a family of functions
between the types substituted for its variables. -/
def HTyFun.map : (F : HTyFun) → {A B : ℕ → HTy} → (∀ i, (A i).Sem → (B i).Sem) →
    (F.app A).Sem → (F.app B).Sem
  | .var i, _, _, r, x => r i x
  | .const _, _, _, _, x => x
  | .one, _, _, _, x => x
  | .prod F G, _, _, r, x => (F.map r x.1, G.map r x.2)
  | .sum F G, _, _, r, x => Sum.map (F.map r) (G.map r) x
  | .list F, _, _, r, l => l.map (F.map r)

/-- The expression applied to a valuation by *arrow-free* types, as a type of Definition
`def:types`.  Applying it to arrow-free types and reading the result as a higher-order type is the
same as applying it to those types read as higher-order types, which is how
`Transducers.HTyFun.mapTy` below is typed. -/
def HTyFun.appTy : HTyFun → (ℕ → Ty) → Ty
  | .var i, P => P i
  | .const C, _ => C
  | .one, _ => .one
  | .prod F G, P => .prod (F.appTy P) (G.appTy P)
  | .sum F G, P => .sum (F.appTy P) (G.appTy P)
  | .list F, P => .list (F.appTy P)

/-- The lifting of a family of functions `Pᵢ → Aᵢ` whose sources are arrow-free types. -/
def HTyFun.mapTy : (F : HTyFun) → {P : ℕ → Ty} → {A : ℕ → HTy} →
    (∀ i, (P i).Elt → (A i).Sem) → (HTy.ofTy (F.appTy P)).Sem → (F.app A).Sem
  | .var i, P, _, r, x => r i (HTy.toElt (P i) x)
  | .const _, _, _, _, x => x
  | .one, _, _, _, x => x
  | .prod F G, _, _, r, x => (F.mapTy r x.1, G.mapTy r x.2)
  | .sum F G, _, _, r, x => Sum.map (F.mapTy r) (G.mapTy r) x
  | .list F, _, _, r, l => l.map (F.mapTy r)

/-- The lifting of a family of functions between arrow-free types, as a function between the
elements of two types of Definition `def:types`. -/
def HTyFun.mapElt : (F : HTyFun) → {P Q : ℕ → Ty} → (∀ i, (P i).Elt → (Q i).Elt) →
    (F.appTy P).Elt → (F.appTy Q).Elt
  | .var i, _, _, h, x => h i x
  | .const _, _, _, _, x => x
  | .one, _, _, _, x => x
  | .prod F G, _, _, h, x => (F.mapElt h x.1, G.mapElt h x.2)
  | .sum F G, _, _, h, x => Sum.map (F.mapElt h) (G.mapElt h) x
  | .list F, _, _, h, l => l.map (F.mapElt h)

/-- The lifting of regular functions between arrow-free types is regular. -/
theorem HTyFun.isRegularUnderRepr_mapElt :
    ∀ (F : HTyFun) {P Q : ℕ → Ty} (h : ∀ i, (P i).Elt → (Q i).Elt),
      (∀ i, IsRegularUnderRepr (h i)) → IsRegularUnderRepr (F.mapElt h) := by
  intro F
  induction F with
  | var i => intro P Q h hh; exact hh i
  | const C => intro P Q h _; exact isRegularUnderRepr_id C
  | one => intro P Q h _; exact isRegularUnderRepr_id .one
  | prod F G ihF ihG =>
      intro P Q h hh
      exact (IsRegularUnderRepr.prodMap (ihF h hh) (ihG h hh)).congr (fun _ => rfl)
  | sum F G ihF ihG =>
      intro P Q h hh
      exact (IsRegularUnderRepr.sumMap (ihF h hh) (ihG h hh)).congr (fun _ => rfl)
  | list F ihF =>
      intro P Q h hh
      exact (IsRegularUnderRepr.mapList (ihF h hh)).congr (fun _ => rfl)

/-- The two liftings compose: lifting `Pᵢ → Qᵢ` and then `Qᵢ → Aᵢ` is lifting the composition. -/
theorem HTyFun.mapTy_mapElt :
    ∀ (F : HTyFun) {P Q : ℕ → Ty} {A : ℕ → HTy} (h : ∀ i, (P i).Elt → (Q i).Elt)
      (r : ∀ i, (Q i).Elt → (A i).Sem) (x : (F.appTy P).Elt),
      F.mapTy r (HTy.ofElt (F.appTy Q) (F.mapElt h x))
        = F.mapTy (fun i p => r i (h i p)) (HTy.ofElt (F.appTy P) x) := by
  intro F
  induction F with
  | var i =>
      intro P Q A h r x
      show r i (HTy.toElt (Q i) (HTy.ofElt (Q i) (h i x)))
        = r i (h i (HTy.toElt (P i) (HTy.ofElt (P i) x)))
      rw [HTy.toElt_ofElt, HTy.toElt_ofElt]
  | const C => intro P Q A h r x; rfl
  | one => intro P Q A h r x; rfl
  | prod F G ihF ihG =>
      intro P Q A h r x
      show (F.mapTy r (HTy.ofElt (F.appTy Q) (F.mapElt h x.1)),
          G.mapTy r (HTy.ofElt (G.appTy Q) (G.mapElt h x.2))) = _
      rw [ihF h r x.1, ihG h r x.2]
      rfl
  | sum F G ihF ihG =>
      intro P Q A h r x
      cases x with
      | inl a =>
          show Sum.inl (F.mapTy r (HTy.ofElt (F.appTy Q) (F.mapElt h a))) = _
          rw [ihF h r a]
          rfl
      | inr b =>
          show Sum.inr (G.mapTy r (HTy.ofElt (G.appTy Q) (G.mapElt h b))) = _
          rw [ihG h r b]
          rfl
  | list F ihF =>
      intro P Q A h r l
      show ((l.map (F.mapElt h)).map (HTy.ofElt (F.appTy Q))).map (F.mapTy r)
        = (l.map (HTy.ofElt (F.appTy P))).map (F.mapTy (fun i p => r i (h i p)))
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left (fun x _ => ihF h r x)

/-! ## Natural transformations -/

/-- **Natural transformation.**  A family of functions `F(A₁,…,Aₙ) → G(A₁,…,Aₙ)`, one for every
valuation of the type variables by higher-order types, whose domain and co-domain are expressions
built from the variables by the arrow-free type constructors, is a *natural transformation* if the
square of the book commutes for every family of functions `ρᵢ : Aᵢ → Bᵢ`, which are required to be
neither good nor polyregular.  This definition carries no `\label` in the book. -/
def IsNaturalTransformation (F G : HTyFun)
    (f : ∀ A : ℕ → HTy, (F.app A).Sem → (G.app A).Sem) : Prop :=
  ∀ (A B : ℕ → HTy) (r : ∀ i, (A i).Sem → (B i).Sem) (x : (F.app A).Sem),
    G.map r (f A x) = f B (F.map r x)

/-! ## Claim `claim:atomic-functions-are-natural-transformations` -/

/-- **Claim `claim:atomic-functions-are-natural-transformations`.**  Every atomic function of the
polyregular system whose type is of the form `F(A₁,…,Aₙ) → G(A₁,…,Aₙ)`, for expressions `F` and `G`
built by the arrow-free type constructors, is a natural transformation.  The atomic functions are
listed here in the order of `Transducers.HAtom`, each with the arity the book gives it -- at most
three type variables; the two that are missing, `map` and `either`, take functions as arguments and
so are not families of that form at all. -/
theorem atoms_are_natural :
    IsNaturalTransformation (.var 0) (.var 0)
        (fun A => (HAtom.idA (A 0)).sem) ∧
      IsNaturalTransformation (.prod (.var 0) (.var 1)) (.var 0)
        (fun A => (HAtom.fst (A 0) (A 1)).sem) ∧
      IsNaturalTransformation (.prod (.var 0) (.var 1)) (.var 1)
        (fun A => (HAtom.snd (A 0) (A 1)).sem) ∧
      IsNaturalTransformation (.var 0) (.sum (.var 0) (.var 1))
        (fun A => (HAtom.inl (A 0) (A 1)).sem) ∧
      IsNaturalTransformation (.var 1) (.sum (.var 0) (.var 1))
        (fun A => (HAtom.inr (A 0) (A 1)).sem) ∧
      IsNaturalTransformation (.var 0) (.prod (.var 0) (.var 0))
        (fun A => (HAtom.diag (A 0)).sem) ∧
      IsNaturalTransformation (.sum (.var 0) (.var 0)) (.var 0)
        (fun A => (HAtom.codiag (A 0)).sem) ∧
      IsNaturalTransformation (.prod (.var 0) (.sum (.var 1) (.var 2)))
        (.sum (.prod (.var 0) (.var 1)) (.prod (.var 0) (.var 2)))
        (fun A => (HAtom.distr (A 0) (A 1) (A 2)).sem) ∧
      IsNaturalTransformation
        (.sum .one (.prod (.var 0) (.list (.var 0)))) (.list (.var 0))
        (fun A => (HAtom.consA (A 0)).sem) ∧
      IsNaturalTransformation
        (.list (.var 0)) (.sum .one (.prod (.var 0) (.list (.var 0))))
        (fun A => (HAtom.uncons (A 0)).sem) ∧
      IsNaturalTransformation (.list (.var 0)) (.list (.var 0))
        (fun A => (HAtom.reverse (A 0)).sem) ∧
      IsNaturalTransformation (.list (.list (.var 0))) (.list (.var 0))
        (fun A => (HAtom.concat (A 0)).sem) ∧
      IsNaturalTransformation (.list (.sum (.var 0) (.var 1)))
        (.prod (.list (.var 0)) (.list (.prod (.var 1) (.list (.var 0)))))
        (fun A => (HAtom.blockSplit (A 0) (A 1)).sem) ∧
      IsNaturalTransformation (.list (.var 0))
        (.list (.prod (.list (.var 0)) (.list (.var 0))))
        (fun A => (HAtom.splits (A 0)).sem) ∧
      (∀ (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt),
        IsNaturalTransformation (.list (.const G)) (.list (.const G))
          (fun _ => (HAtom.pref G grp hfin).sem)) ∧
      (∀ (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt),
        IsNaturalTransformation (.list (.const G)) (.const G)
          (fun _ => (HAtom.mult G grp hfin).sem)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B r x; rfl
  · intro A B r x; rfl
  · intro A B r x; rfl
  · intro A B r x; rfl
  · intro A B r x; rfl
  · intro A B r x; rfl
  · intro A B r x; cases x <;> rfl
  · intro A B r x
    obtain ⟨u, v⟩ := x
    cases v <;> rfl
  · intro A B r x
    cases x with
    | inl _ => rfl
    | inr p => rfl
  · intro A B r x
    cases x with
    | nil => rfl
    | cons a l => rfl
  · intro A B r x
    exact List.map_reverse
  · intro A B r x
    exact List.map_flatten
  · intro A B r x
    exact (splitList_map (r 0) (r 1) x).symm
  · intro A B r x
    exact (splitsList_map (r 0) x).symm
  · intro G grp hfin A B r x
    show (groupPrefixProd G grp x).map (fun y => y) = groupPrefixProd G grp (x.map (fun y => y))
    simp
  · intro G grp hfin A B r x
    show groupProd G grp x = groupProd G grp (x.map (fun y => y))
    simp

/-! ## Claim `claim:functors-applied-to-good` -/

/-- Good functions are closed under co-pairing: the function that runs one of two good functions,
according to the side of a co-product parameter, is good.  This is the step by which the book
replaces two good functions by a single one, when it treats the list constructor. -/
theorem Rel.copair (H : HTy) {P Q : Ty} {u : P.Elt → H.Sem} {v : Q.Elt → H.Sem}
    (hu : Rel H P u) (hv : Rel H Q v) : Rel H (.sum P Q) (fun x => Sum.elim u v x) := by
  have ht : IsPolyregularUnderRepr (A := .sum P Q) (B := .sum .one .one)
      (fun x => Sum.map (fun _ => ()) (fun _ => ()) x) :=
    (isRegularUnderRepr_sumTag P Q).isPolyregularUnderRepr
  have hu' : Rel H (.sum P Q) (fun x => u (Sum.elim (fun p => p) (fun _ => default) x)) :=
    Rel.reindex H hu (isRegularUnderRepr_elimDefault P Q).isPolyregularUnderRepr
  have hv' : Rel H (.sum P Q) (fun x => v (Sum.elim (fun _ => default) (fun q => q) x)) :=
    Rel.reindex H hv (isRegularUnderRepr_elimDefaultRight P Q).isPolyregularUnderRepr
  refine (Rel.glue H ht hu' hv').congr (fun x => ?_)
  cases x <;> rfl

/-- The tuple of parameters that the case of a bare type parameter needs: the good family itself
at the place of that parameter, and a good constant family everywhere else. -/
private theorem exists_param_tuple {A : ℕ → HTy} (c : ∀ i, (A i).Sem)
    (hc : ∀ (i : ℕ) (P : Ty), Rel (A i) P (fun _ => c i)) (i : ℕ) {P : Ty}
    {g : P.Elt → (A i).Sem} (hg : Rel (A i) P g) :
    ∃ r : ∀ j, P.Elt → (A j).Sem, (∀ j, Rel (A j) P (r j)) ∧ r i = g := by
  classical
  refine ⟨fun j => if h : j = i then
      (fun p => cast (congrArg (fun k => (A k).Sem) h).symm (g p)) else (fun _ => c j), ?_, ?_⟩
  · intro j
    by_cases h : j = i
    · subst h
      simpa using hg
    · simpa [dif_neg h] using hc j P
  · funext p
    simp

/-- **Claim `claim:functors-applied-to-good`.**  Let `F(A₁,…,Aₙ)` be an expression built by the
arrow-free type constructors and let `A₁,…,Aₙ` be higher-order types.  A function
`ρ : P → F(A₁,…,Aₙ)` is good if and only if it is a composition

    P → F(P₁,…,Pₙ) → F(A₁,…,Aₙ)

of a polyregular function with the lifting `F(ρ₁,…,ρₙ)` of good functions `ρᵢ : Pᵢ → Aᵢ`, for some
arrow-free parameter types `P₁,…,Pₙ`. -/
theorem good_of_functor_applied {A : ℕ → HTy} :
    ∀ (F : HTyFun) {P : Ty} (g : P.Elt → (F.app A).Sem),
      Rel (F.app A) P g ↔
        ∃ (Q : ℕ → Ty) (r : ∀ i, (Q i).Elt → (A i).Sem) (f : P.Elt → (F.appTy Q).Elt),
          IsPolyregularUnderRepr f ∧ (∀ i, Rel (A i) (Q i) (r i)) ∧
            ∀ p, g p = F.mapTy r (HTy.ofElt (F.appTy Q) (f p)) := by
  obtain ⟨c, hc⟩ : ∃ c : ∀ i, (A i).Sem, ∀ (i : ℕ) (P : Ty), Rel (A i) P (fun _ => c i) := by
    choose c hc using fun i => Rel.exists_const (A i)
    exact ⟨c, hc⟩
  intro F
  induction F with
  | var i =>
      intro P g
      constructor
      · intro h
        obtain ⟨r, hr, hri⟩ := exists_param_tuple c hc i h
        refine ⟨fun _ => P, r, fun p => p,
          (isRegularUnderRepr_id P).isPolyregularUnderRepr, fun j => hr j, fun p => ?_⟩
        show g p = r i (HTy.toElt P (HTy.ofElt P p))
        rw [HTy.toElt_ofElt, hri]
      · rintro ⟨Q, r, f, hf, hr, he⟩
        refine (Rel.reindex (A i) (hr i) hf).congr (fun p => ?_)
        rw [he p]
        show r i (f p) = r i (HTy.toElt (Q i) (HTy.ofElt (Q i) (f p)))
        rw [HTy.toElt_ofElt]
  | const C =>
      intro P g
      constructor
      · intro h
        refine ⟨fun _ => .one, fun j _ => c j, fun p => HTy.toElt C (g p),
          (Rel.iff_polyregular C g).mp h, fun j => hc j _, fun p => ?_⟩
        show g p = HTy.ofElt C (HTy.toElt C (g p))
        rw [HTy.ofElt_toElt]
      · rintro ⟨Q, r, f, hf, hr, he⟩
        refine (Rel.iff_polyregular C g).mpr (hf.congr (fun p => ?_))
        rw [he p]
        show f p = HTy.toElt C (HTy.ofElt C (f p))
        rw [HTy.toElt_ofElt]
  | one =>
      intro P g
      constructor
      · intro _
        exact ⟨fun _ => .one, fun j _ => c j, fun _ => (),
          isPolyregularUnderRepr_const (A := P) (B := .one) (), fun j => hc j _, fun _ => rfl⟩
      · intro _; trivial
  | prod F G ihF ihG =>
      intro P g
      constructor
      · intro h
        obtain ⟨Q₁, r₁, f₁, hf₁, hr₁, he₁⟩ := (ihF (P := P) (fun p => (g p).1)).mp h.1
        obtain ⟨Q₂, r₂, f₂, hf₂, hr₂, he₂⟩ := (ihG (P := P) (fun p => (g p).2)).mp h.2
        refine ⟨fun i => .sum (Q₁ i) (Q₂ i), fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x,
          fun p => (F.mapElt (fun i => (Sum.inl : (Q₁ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₁ p),
            G.mapElt (fun i => (Sum.inr : (Q₂ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₂ p)),
          ?_, ?_, ?_⟩
        · exact IsPolyregularUnderRepr.pair
            (hf₁.comp (F.isRegularUnderRepr_mapElt _
              (fun i => isRegularUnderRepr_inl (Q₁ i) (Q₂ i))).isPolyregularUnderRepr)
            (hf₂.comp (G.isRegularUnderRepr_mapElt _
              (fun i => isRegularUnderRepr_inr (Q₁ i) (Q₂ i))).isPolyregularUnderRepr)
        · exact fun i => Rel.copair (A i) (hr₁ i) (hr₂ i)
        · intro p
          show g p = (F.mapTy (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x)
              (HTy.ofElt (F.appTy (fun i => Ty.sum (Q₁ i) (Q₂ i)))
                (F.mapElt (fun i => (Sum.inl : (Q₁ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₁ p))),
            G.mapTy (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x)
              (HTy.ofElt (G.appTy (fun i => Ty.sum (Q₁ i) (Q₂ i)))
                (G.mapElt (fun i => (Sum.inr : (Q₂ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₂ p))))
          rw [F.mapTy_mapElt (fun i => (Sum.inl : (Q₁ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt))
              (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x) (f₁ p),
            G.mapTy_mapElt (fun i => (Sum.inr : (Q₂ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt))
              (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x) (f₂ p)]
          exact Prod.ext (he₁ p) (he₂ p)
      · rintro ⟨Q, r, f, hf, hr, he⟩
        refine ⟨(ihF (P := P) (fun p => (g p).1)).mpr ⟨Q, r, fun p => (f p).1,
            hf.comp (isRegularUnderRepr_fst (F.appTy Q) (G.appTy Q)).isPolyregularUnderRepr, hr,
            fun p => congrArg Prod.fst (he p)⟩,
          (ihG (P := P) (fun p => (g p).2)).mpr ⟨Q, r, fun p => (f p).2,
            hf.comp (isRegularUnderRepr_snd (F.appTy Q) (G.appTy Q)).isPolyregularUnderRepr, hr,
            fun p => congrArg Prod.snd (he p)⟩⟩
  | sum F G ihF ihG =>
      intro P g
      constructor
      · rintro ⟨a, b, ha, hb, htag, hcons⟩
        obtain ⟨Q₁, r₁, f₁, hf₁, hr₁, he₁⟩ := (ihF (P := P) a).mp ha
        obtain ⟨Q₂, r₂, f₂, hf₂, hr₂, he₂⟩ := (ihG (P := P) b).mp hb
        refine ⟨fun i => .sum (Q₁ i) (Q₂ i), fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x,
          fun p => Sum.elim
            (fun _ => Sum.inl (F.mapElt
              (fun i => (Sum.inl : (Q₁ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₁ p)))
            (fun _ => Sum.inr (G.mapElt
              (fun i => (Sum.inr : (Q₂ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₂ p)))
            (Sum.map (fun _ => ()) (fun _ => ()) (g p)), ?_, ?_, ?_⟩
        · refine IsPolyregularUnderRepr.cond htag ?_ ?_
          · exact (hf₁.comp (F.isRegularUnderRepr_mapElt _
              (fun i => isRegularUnderRepr_inl (Q₁ i) (Q₂ i))).isPolyregularUnderRepr).comp
              (isRegularUnderRepr_inl (F.appTy _) (G.appTy _)).isPolyregularUnderRepr
          · exact (hf₂.comp (G.isRegularUnderRepr_mapElt _
              (fun i => isRegularUnderRepr_inr (Q₁ i) (Q₂ i))).isPolyregularUnderRepr).comp
              (isRegularUnderRepr_inr (F.appTy _) (G.appTy _)).isPolyregularUnderRepr
        · exact fun i => Rel.copair (A i) (hr₁ i) (hr₂ i)
        · intro p
          rcases hcons p with hp | hp <;> simp only [hp]
          · show Sum.inl (a p) = Sum.inl (F.mapTy (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x)
              (HTy.ofElt (F.appTy (fun i => Ty.sum (Q₁ i) (Q₂ i)))
                (F.mapElt (fun i => (Sum.inl : (Q₁ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₁ p))))
            rw [F.mapTy_mapElt (fun i => (Sum.inl : (Q₁ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt))
              (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x) (f₁ p)]
            exact congrArg Sum.inl (he₁ p)
          · show Sum.inr (b p) = Sum.inr (G.mapTy (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x)
              (HTy.ofElt (G.appTy (fun i => Ty.sum (Q₁ i) (Q₂ i)))
                (G.mapElt (fun i => (Sum.inr : (Q₂ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt)) (f₂ p))))
            rw [G.mapTy_mapElt (fun i => (Sum.inr : (Q₂ i).Elt → (Ty.sum (Q₁ i) (Q₂ i)).Elt))
              (fun i (x : (Ty.sum (Q₁ i) (Q₂ i)).Elt) => Sum.elim (r₁ i) (r₂ i) x) (f₂ p)]
            exact congrArg Sum.inr (he₂ p)
      · rintro ⟨Q, r, f, hf, hr, he⟩
        refine ⟨fun p => F.mapTy r (HTy.ofElt (F.appTy Q)
            (Sum.elim (fun x => x) (fun _ => default) (f p))),
          fun p => G.mapTy r (HTy.ofElt (G.appTy Q)
            (Sum.elim (fun _ => default) (fun y => y) (f p))), ?_, ?_, ?_, ?_⟩
        · exact (ihF (P := P) _).mpr ⟨Q, r,
            fun p => Sum.elim (fun x => x) (fun _ => default) (f p),
            hf.comp (isRegularUnderRepr_elimDefault (F.appTy Q)
              (G.appTy Q)).isPolyregularUnderRepr, hr, fun _ => rfl⟩
        · exact (ihG (P := P) _).mpr ⟨Q, r,
            fun p => Sum.elim (fun _ => default) (fun y => y) (f p),
            hf.comp (isRegularUnderRepr_elimDefaultRight (F.appTy Q)
              (G.appTy Q)).isPolyregularUnderRepr, hr, fun _ => rfl⟩
        · refine ((hf.comp (isRegularUnderRepr_sumTag (F.appTy Q)
            (G.appTy Q)).isPolyregularUnderRepr)).congr (fun p => ?_)
          rw [he p]
          cases f p <;> rfl
        · intro p
          cases hfp : f p with
          | inl x =>
              refine Or.inl ?_
              simp only [he p, hfp]
              rfl
          | inr y =>
              refine Or.inr ?_
              simp only [he p, hfp]
              rfl
  | list F ihF =>
      intro P g
      constructor
      · rintro ⟨Q₀, l, e, hl, he, hg⟩
        obtain ⟨Q₁, r₁, f₁, hf₁, hr₁, he₁⟩ := (ihF (P := .prod P Q₀) e).mp he
        refine ⟨Q₁, r₁, fun p => (l p).map (fun q => f₁ (p, q)),
          IsPolyregularUnderRepr.mapParam hl hf₁, hr₁, fun p => ?_⟩
        rw [hg p]
        show (l p).map (fun q => e (p, q))
          = (((l p).map (fun q => f₁ (p, q))).map (HTy.ofElt (F.appTy Q₁))).map (F.mapTy r₁)
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left (fun q _ => he₁ (p, q))
      · rintro ⟨Q, r, f, hf, hr, he⟩
        refine ⟨F.appTy Q, f, fun x => F.mapTy r (HTy.ofElt (F.appTy Q) x.2), hf, ?_, fun p => ?_⟩
        · exact (ihF (P := .prod P (F.appTy Q)) _).mpr ⟨Q, r, fun x => x.2,
            (isRegularUnderRepr_snd P (F.appTy Q)).isPolyregularUnderRepr, hr, fun _ => rfl⟩
        · rw [he p]
          show ((f p).map (HTy.ofElt (F.appTy Q))).map (F.mapTy r)
            = (f p).map (fun x => F.mapTy r (HTy.ofElt (F.appTy Q) x))
          rw [List.map_map]
          rfl

end Transducers
