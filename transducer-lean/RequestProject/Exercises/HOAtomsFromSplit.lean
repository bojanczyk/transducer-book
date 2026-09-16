/-
The three exercises of Section *A functional programming language* (`higher-order.tex`).

Lemma `lem:fewer-atomic` drops eight of the atomic functions of Definition `def:higher-order-terms`
and keeps ten: the two projections, the two co-projections, `uncons`, `concat`, `split`, `mult`,
`map` and `either`.  For five of the eight the book displays the defining term; the remaining three
are the exercises formalised here, each of which says that one dropped atomic function is definable
without it:

* Exercise `exer:reverse-from-split` -- `reverse`, by running over the cuts that `split` produces
  and keeping the first entry of every suffix;
* Exercise `exer:block-from-split` -- the block split of Example `ex:block`, without `reverse`;
* Exercise `nolabel:exer-pref-from-mult` -- group prefix multiplication, from the product `mult` of a list.

**What is proved where.**  The book phrases the three exercises for *polyregular* terms
(Definition `def:polyregular-terms`, `Transducers.PolyTerm`), and that is what
`Transducers.Exercises.reverse_from_split`, `Transducers.Exercises.block_from_split` and
`Transducers.Exercises.pref_from_mult` below state: the witnesses are polyregular terms, built from
the combinators of Definition `def:regular-terms` and the atomic function `split` of Definition
`def:polyregular-terms`, and a clause of each statement says which atomic constructors the witness
avoids.  No lambda is involved: in the polyregular syntax `map` is the combinator
`Transducers.PolyTerm.map`, so the author's solutions transcribe directly.

The same three statements in the *higher-order* syntax of Definition `def:higher-order-terms` are
kept below under the names `Transducers.Exercises.reverse_from_split_higherOrder`,
`Transducers.Exercises.block_from_split_higherOrder` and
`Transducers.Exercises.pref_from_mult_higherOrder`.  Those are the ones that the proof of Lemma
`lem:fewer-atomic` in `RequestProject/PartD/HOFewer.lean` appeals to, through the terms
`Transducers.HTerm.reverseTerm`, `Transducers.HTerm.blockSplitTerm` and
`Transducers.HTerm.prefTerm`; they are *not* the exercises, because they are the weaker reading of
them -- every polyregular term is a higher-order term, so asking for a higher-order term asks for
less.  (An earlier version of this file claimed the implication in the other direction; that was
wrong, and the polyregular statements above are what the exercises ask for.)

**The atomic function `mult`.**  The polyregular terms of Definition `def:polyregular-terms` have
group prefix multiplication `pref : G* → G*` among their atomic functions but not the product
`mult : G* → G` of a list, which is the atomic function that Lemma `lem:fewer-atomic` puts in its
place and that Exercise `nolabel:exer-pref-from-mult` asks to use.  So the third exercise is stated for
`Transducers.PolyMultTerm`, the polyregular terms extended by that one atomic function, and the
clause `Transducers.PolyMultTerm.NoPref` of the statement says that the witness uses no `pref`.

The combinatorial identities behind the three terms are the ones of
`RequestProject/PartD/HOFewerAux.lean` -- `Transducers.flatten_headAsList_splits`,
`Transducers.twiFun_eq`, `Transducers.bsFun_eq` and `Transducers.prefFun_eq` -- which are shared
with the higher-order terms; only the terms are rebuilt here.
-/
import RequestProject.PartD.HOFewer

namespace Transducers

/-! ## The semantics of a polyregular term, constructor by constructor

The semantics `Transducers.PolyTerm.eval` is defined by recursion on the term, and the equations
below are the individual steps of that recursion, in the form in which `simp` can use them. -/

namespace PolyTerm

variable {A B C A₁ A₂ B₁ B₂ : Ty}

lemma eval_id (x : A.Elt) : (PolyTerm.id A).eval x = x := rfl

lemma eval_fst (p : (Ty.prod A B).Elt) : (PolyTerm.fst A B).eval p = p.1 := rfl

lemma eval_snd (p : (Ty.prod A B).Elt) : (PolyTerm.snd A B).eval p = p.2 := rfl

lemma eval_inl (x : A.Elt) : (PolyTerm.inl A B).eval x = Sum.inl x := rfl

lemma eval_inr (x : B.Elt) : (PolyTerm.inr A B).eval x = Sum.inr x := rfl

lemma eval_diag (x : A.Elt) : (PolyTerm.diag A).eval x = (x, x) := rfl

lemma eval_codiag_inl (x : A.Elt) : (PolyTerm.codiag A).eval (Sum.inl x) = x := rfl

lemma eval_codiag_inr (x : A.Elt) : (PolyTerm.codiag A).eval (Sum.inr x) = x := rfl

lemma eval_distr_inl (x : A.Elt) (b : B.Elt) :
    (PolyTerm.distr A B C).eval (x, Sum.inl b) = Sum.inl (x, b) := rfl

lemma eval_distr_inr (x : A.Elt) (c : C.Elt) :
    (PolyTerm.distr A B C).eval (x, Sum.inr c) = Sum.inr (x, c) := rfl

lemma eval_cons_inl (u : Unit) : (PolyTerm.cons A).eval (Sum.inl u) = [] := rfl

lemma eval_cons_inr (p : A.Elt × List A.Elt) :
    (PolyTerm.cons A).eval (Sum.inr p) = p.1 :: p.2 := rfl

lemma eval_uncons_nil : (PolyTerm.uncons A).eval [] = Sum.inl () := rfl

lemma eval_uncons_cons (a : A.Elt) (l : List A.Elt) :
    (PolyTerm.uncons A).eval (a :: l) = Sum.inr (a, l) := rfl

lemma eval_concat (L : List (List A.Elt)) : (PolyTerm.concat A).eval L = L.flatten := rfl

lemma eval_splits (l : List A.Elt) : (PolyTerm.splits A).eval l = splitsList l := rfl

lemma eval_comp (s : PolyTerm A B) (t : PolyTerm B C) (x : A.Elt) :
    (s.comp t).eval x = t.eval (s.eval x) := rfl

lemma eval_prodMap (s : PolyTerm A₁ B₁) (t : PolyTerm A₂ B₂) (p : (Ty.prod A₁ A₂).Elt) :
    (s.prodMap t).eval p = (s.eval p.1, t.eval p.2) := rfl

lemma eval_sumMap_inl (s : PolyTerm A₁ B₁) (t : PolyTerm A₂ B₂) (x : A₁.Elt) :
    (s.sumMap t).eval (Sum.inl x) = Sum.inl (s.eval x) := rfl

lemma eval_sumMap_inr (s : PolyTerm A₁ B₁) (t : PolyTerm A₂ B₂) (x : A₂.Elt) :
    (s.sumMap t).eval (Sum.inr x) = Sum.inr (t.eval x) := rfl

lemma eval_map (t : PolyTerm A B) (l : List A.Elt) : t.map.eval l = l.map t.eval := rfl

end PolyTerm

/-! ## Which atomic functions a polyregular term uses

Each exercise asks for a term that avoids one or two named atomic functions, so each of the
predicates below excludes exactly the constructors of `Transducers.PolyTerm` that the exercise it
serves excludes, and is propagated structurally through composition and the three functoriality
combinators.  They are the analogue, for the polyregular terms, of `Transducers.HAtom.Small` and
`Transducers.HTerm.Small`. -/

/-- A polyregular term **does not use the atomic function `reverse`**. -/
def PolyTerm.NoReverse : {A B : Ty} → PolyTerm A B → Prop
  | _, _, .reverse _ => False
  | _, _, .comp s t => s.NoReverse ∧ t.NoReverse
  | _, _, .prodMap s t => s.NoReverse ∧ t.NoReverse
  | _, _, .sumMap s t => s.NoReverse ∧ t.NoReverse
  | _, _, .map t => t.NoReverse
  | _, _, _ => True

/-- A polyregular term **does not use the atomic function `split`**, the block split, which cuts a
list over `A + B` at its entries from `B`.  (This is not the atomic function `split` of Definition
`def:polyregular-terms`, which lists all the ways of cutting a list in two and which is called
`Transducers.PolyTerm.splits` here.) -/
def PolyTerm.NoBlockSplit : {A B : Ty} → PolyTerm A B → Prop
  | _, _, .split _ _ => False
  | _, _, .comp s t => s.NoBlockSplit ∧ t.NoBlockSplit
  | _, _, .prodMap s t => s.NoBlockSplit ∧ t.NoBlockSplit
  | _, _, .sumMap s t => s.NoBlockSplit ∧ t.NoBlockSplit
  | _, _, .map t => t.NoBlockSplit
  | _, _, _ => True

/-- A polyregular term **does not use the atomic function `pref`**, group prefix
multiplication. -/
def PolyTerm.NoPref : {A B : Ty} → PolyTerm A B → Prop
  | _, _, .pref _ _ _ => False
  | _, _, .comp s t => s.NoPref ∧ t.NoPref
  | _, _, .prodMap s t => s.NoPref ∧ t.NoPref
  | _, _, .sumMap s t => s.NoPref ∧ t.NoPref
  | _, _, .map t => t.NoPref
  | _, _, _ => True

/-- The auxiliary predicate that the terms of this file are built to satisfy: they use none of
`reverse`, the block split and `pref`.  Each exercise needs only part of this, and the three
lemmas below extract the part it needs. -/
def PolyTerm.Reduced : {A B : Ty} → PolyTerm A B → Prop
  | _, _, .reverse _ => False
  | _, _, .split _ _ => False
  | _, _, .pref _ _ _ => False
  | _, _, .comp s t => s.Reduced ∧ t.Reduced
  | _, _, .prodMap s t => s.Reduced ∧ t.Reduced
  | _, _, .sumMap s t => s.Reduced ∧ t.Reduced
  | _, _, .map t => t.Reduced
  | _, _, _ => True

theorem PolyTerm.Reduced.noReverse :
    ∀ {A B : Ty} (t : PolyTerm A B), t.Reduced → t.NoReverse
  | _, _, .reverse _, h => h.elim
  | _, _, .comp s t, h => ⟨noReverse s h.1, noReverse t h.2⟩
  | _, _, .prodMap s t, h => ⟨noReverse s h.1, noReverse t h.2⟩
  | _, _, .sumMap s t, h => ⟨noReverse s h.1, noReverse t h.2⟩
  | _, _, .map t, h => noReverse t h
  | _, _, .id _, _ => trivial
  | _, _, .fst _ _, _ => trivial
  | _, _, .snd _ _, _ => trivial
  | _, _, .inl _ _, _ => trivial
  | _, _, .inr _ _, _ => trivial
  | _, _, .diag _, _ => trivial
  | _, _, .codiag _, _ => trivial
  | _, _, .distr _ _ _, _ => trivial
  | _, _, .cons _, _ => trivial
  | _, _, .uncons _, _ => trivial
  | _, _, .concat _, _ => trivial
  | _, _, .split _ _, _ => trivial
  | _, _, .pref _ _ _, _ => trivial
  | _, _, .splits _, _ => trivial

theorem PolyTerm.Reduced.noBlockSplit :
    ∀ {A B : Ty} (t : PolyTerm A B), t.Reduced → t.NoBlockSplit
  | _, _, .split _ _, h => h.elim
  | _, _, .comp s t, h => ⟨noBlockSplit s h.1, noBlockSplit t h.2⟩
  | _, _, .prodMap s t, h => ⟨noBlockSplit s h.1, noBlockSplit t h.2⟩
  | _, _, .sumMap s t, h => ⟨noBlockSplit s h.1, noBlockSplit t h.2⟩
  | _, _, .map t, h => noBlockSplit t h
  | _, _, .id _, _ => trivial
  | _, _, .fst _ _, _ => trivial
  | _, _, .snd _ _, _ => trivial
  | _, _, .inl _ _, _ => trivial
  | _, _, .inr _ _, _ => trivial
  | _, _, .diag _, _ => trivial
  | _, _, .codiag _, _ => trivial
  | _, _, .distr _ _ _, _ => trivial
  | _, _, .cons _, _ => trivial
  | _, _, .uncons _, _ => trivial
  | _, _, .reverse _, _ => trivial
  | _, _, .concat _, _ => trivial
  | _, _, .pref _ _ _, _ => trivial
  | _, _, .splits _, _ => trivial

theorem PolyTerm.Reduced.noPref :
    ∀ {A B : Ty} (t : PolyTerm A B), t.Reduced → t.NoPref
  | _, _, .pref _ _ _, h => h.elim
  | _, _, .comp s t, h => ⟨noPref s h.1, noPref t h.2⟩
  | _, _, .prodMap s t, h => ⟨noPref s h.1, noPref t h.2⟩
  | _, _, .sumMap s t, h => ⟨noPref s h.1, noPref t h.2⟩
  | _, _, .map t, h => noPref t h
  | _, _, .id _, _ => trivial
  | _, _, .fst _ _, _ => trivial
  | _, _, .snd _ _, _ => trivial
  | _, _, .inl _ _, _ => trivial
  | _, _, .inr _ _, _ => trivial
  | _, _, .diag _, _ => trivial
  | _, _, .codiag _, _ => trivial
  | _, _, .distr _ _ _, _ => trivial
  | _, _, .cons _, _ => trivial
  | _, _, .uncons _, _ => trivial
  | _, _, .reverse _, _ => trivial
  | _, _, .concat _, _ => trivial
  | _, _, .split _ _, _ => trivial
  | _, _, .splits _, _ => trivial

/-! ## The polyregular terms with the atomic function `mult`

Exercise `nolabel:exer-pref-from-mult` asks for a term that uses the product `mult : G* → G` of a list,
which is not one of the atomic functions of Definition `def:polyregular-terms`.  The syntax below
adds it: a term is built from the polyregular terms and from `mult` by composition and the three
functoriality combinators.  Since the polyregular terms are themselves closed under those
combinators, this is exactly "the polyregular terms with one more atomic function". -/

/-- The product of a list of elements of a group type: the semantics of the atomic function
`mult`. -/
def groupListProd (G : Ty) (grp : Group G.Elt) (l : List G.Elt) : G.Elt :=
  letI := grp
  l.prod

/-- **The polyregular terms extended by the atomic function `mult`** of Lemma `lem:fewer-atomic`,
the setting of Exercise `nolabel:exer-pref-from-mult`. -/
inductive PolyMultTerm : Ty → Ty → Type
  /-- A polyregular term of Definition `def:polyregular-terms`. -/
  | ofPoly {A B : Ty} : PolyTerm A B → PolyMultTerm A B
  /-- The product `G* → G` of a list, for a group whose underlying set is a finite type. -/
  | mult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : PolyMultTerm (.list G) G
  /-- Composition. -/
  | comp {A B C : Ty} : PolyMultTerm A B → PolyMultTerm B C → PolyMultTerm A C
  /-- Functoriality for products: `f₁ × f₂`. -/
  | prodMap {A₁ A₂ B₁ B₂ : Ty} :
      PolyMultTerm A₁ B₁ → PolyMultTerm A₂ B₂ → PolyMultTerm (.prod A₁ A₂) (.prod B₁ B₂)
  /-- Functoriality for co-products: `f₁ + f₂`. -/
  | sumMap {A₁ A₂ B₁ B₂ : Ty} :
      PolyMultTerm A₁ B₁ → PolyMultTerm A₂ B₂ → PolyMultTerm (.sum A₁ A₂) (.sum B₁ B₂)
  /-- Functoriality for lists: `f*`. -/
  | map {A B : Ty} : PolyMultTerm A B → PolyMultTerm (.list A) (.list B)

/-- The semantics of a term of the extended syntax. -/
def PolyMultTerm.eval : {A B : Ty} → PolyMultTerm A B → A.Elt → B.Elt
  | _, _, .ofPoly t => t.eval
  | _, _, .mult G grp _ => fun l => groupListProd G grp l
  | _, _, .comp s t => fun x => t.eval (s.eval x)
  | _, _, .prodMap s t => fun p => (s.eval p.1, t.eval p.2)
  | _, _, .sumMap s t => fun x => Sum.map s.eval t.eval x
  | _, _, .map t => fun l => l.map t.eval

namespace PolyMultTerm

variable {A B C A₁ A₂ B₁ B₂ : Ty}

lemma eval_ofPoly (t : PolyTerm A B) (x : A.Elt) : (PolyMultTerm.ofPoly t).eval x = t.eval x := rfl

lemma eval_mult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) (l : List G.Elt) :
    (PolyMultTerm.mult G grp hfin).eval l = groupListProd G grp l := rfl

lemma eval_comp (s : PolyMultTerm A B) (t : PolyMultTerm B C) (x : A.Elt) :
    (s.comp t).eval x = t.eval (s.eval x) := rfl

lemma eval_prodMap (s : PolyMultTerm A₁ B₁) (t : PolyMultTerm A₂ B₂) (p : (Ty.prod A₁ A₂).Elt) :
    (s.prodMap t).eval p = (s.eval p.1, t.eval p.2) := rfl

lemma eval_sumMap_inl (s : PolyMultTerm A₁ B₁) (t : PolyMultTerm A₂ B₂) (x : A₁.Elt) :
    (s.sumMap t).eval (Sum.inl x) = Sum.inl (s.eval x) := rfl

lemma eval_sumMap_inr (s : PolyMultTerm A₁ B₁) (t : PolyMultTerm A₂ B₂) (x : A₂.Elt) :
    (s.sumMap t).eval (Sum.inr x) = Sum.inr (t.eval x) := rfl

lemma eval_map (t : PolyMultTerm A B) (l : List A.Elt) : t.map.eval l = l.map t.eval := rfl

end PolyMultTerm

/-- A term of the extended syntax **does not use the atomic function `pref`**, group prefix
multiplication. -/
def PolyMultTerm.NoPref : {A B : Ty} → PolyMultTerm A B → Prop
  | _, _, .ofPoly t => t.NoPref
  | _, _, .mult _ _ _ => True
  | _, _, .comp s t => s.NoPref ∧ t.NoPref
  | _, _, .prodMap s t => s.NoPref ∧ t.NoPref
  | _, _, .sumMap s t => s.NoPref ∧ t.NoPref
  | _, _, .map t => t.NoPref

namespace Exercises

/-! ## The building blocks

Every term of this section is `Transducers.PolyTerm.Reduced`: it uses none of `reverse`, the block
split and `pref`. -/

/-- The unique function `A → 1`, by induction on the type. -/
def polyBang : (A : Ty) → PolyTerm A .one
  | .one => .id .one
  | .prod A B => (PolyTerm.fst A B).comp (polyBang A)
  | .sum A B => (PolyTerm.sumMap (polyBang A) (polyBang B)).comp (.codiag .one)
  | .list A =>
      (PolyTerm.uncons A).comp
        ((PolyTerm.sumMap (.id .one) ((PolyTerm.fst A (.list A)).comp (polyBang A))).comp
          (.codiag .one))

@[simp] lemma polyBang_eval (A : Ty) (x : A.Elt) : (polyBang A).eval x = () := rfl

theorem polyBang_reduced : ∀ A : Ty, (polyBang A).Reduced
  | .one => trivial
  | .prod A _ => ⟨trivial, polyBang_reduced A⟩
  | .sum A B => ⟨⟨polyBang_reduced A, polyBang_reduced B⟩, trivial⟩
  | .list A => ⟨trivial, ⟨⟨trivial, ⟨trivial, polyBang_reduced A⟩⟩, trivial⟩⟩

/-- The constant empty list. -/
def polyNil (A B : Ty) : PolyTerm A (.list B) :=
  ((polyBang A).comp (PolyTerm.inl .one (.prod B (.list B)))).comp (PolyTerm.cons B)

@[simp] lemma polyNil_eval (A B : Ty) (x : A.Elt) : (polyNil A B).eval x = [] := rfl

theorem polyNil_reduced (A B : Ty) : (polyNil A B).Reduced :=
  ⟨⟨polyBang_reduced A, trivial⟩, trivial⟩

/-- The singleton list. -/
def polyPure (A : Ty) : PolyTerm A (.list A) :=
  (((PolyTerm.diag A).comp (PolyTerm.prodMap (.id A) (polyNil A A))).comp
    (PolyTerm.inr .one (.prod A (.list A)))).comp (PolyTerm.cons A)

@[simp] lemma polyPure_eval (A : Ty) (a : A.Elt) : (polyPure A).eval a = [a] := rfl

theorem polyPure_reduced (A : Ty) : (polyPure A).Reduced :=
  ⟨⟨⟨trivial, ⟨trivial, polyNil_reduced A A⟩⟩, trivial⟩, trivial⟩

/-- Swapping the two components of a pair. -/
def polySwap (A B : Ty) : PolyTerm (.prod A B) (.prod B A) :=
  (PolyTerm.diag (.prod A B)).comp (PolyTerm.prodMap (.snd A B) (.fst A B))

@[simp] lemma polySwap_eval (A B : Ty) (p : (Ty.prod A B).Elt) :
    (polySwap A B).eval p = (p.2, p.1) := rfl

theorem polySwap_reduced (A B : Ty) : (polySwap A B).Reduced := ⟨trivial, trivial, trivial⟩

/-! ## Exercise `exer:reverse-from-split` -/

/-- The version of `head` of the author's solution: the first entry of a list, as a list of at
most one entry. -/
def polyHeadAsList (A : Ty) : PolyTerm (.list A) (.list A) :=
  (PolyTerm.uncons A).comp
    ((PolyTerm.sumMap (polyNil .one A) ((PolyTerm.fst A (.list A)).comp (polyPure A))).comp
      (PolyTerm.codiag (.list A)))

@[simp] lemma polyHeadAsList_eval (A : Ty) :
    (polyHeadAsList A).eval = fun l => headAsList l := by
  funext l
  cases l <;> rfl

theorem polyHeadAsList_reduced (A : Ty) : (polyHeadAsList A).Reduced :=
  ⟨trivial, ⟨⟨polyNil_reduced .one A, ⟨trivial, polyPure_reduced A⟩⟩, trivial⟩⟩

/-- **Exercise `exer:reverse-from-split`**, the term: apply `split`, then `snd*`, then the version
of `head` above, then `concat`. -/
def polyReverse (A : Ty) : PolyTerm (.list A) (.list A) :=
  (((PolyTerm.splits A).comp (PolyTerm.map (PolyTerm.snd (.list A) (.list A)))).comp
    (PolyTerm.map (polyHeadAsList A))).comp (PolyTerm.concat A)

@[simp] lemma polyReverse_eval (A : Ty) : (polyReverse A).eval = fun l => l.reverse := by
  funext l
  show (((splitsList l).map (fun z => z.2)).map (polyHeadAsList A).eval).flatten = l.reverse
  rw [List.map_map, polyHeadAsList_eval]
  exact flatten_headAsList_splits l

theorem polyReverse_reduced (A : Ty) : (polyReverse A).Reduced :=
  ⟨⟨⟨trivial, trivial⟩, polyHeadAsList_reduced A⟩, trivial⟩

/-! ## Exercise `exer:block-from-split` -/

/-- The entry of a list over `A + B`, as a list of at most one entry, kept when it comes from
`B`. -/
def polyInrStep (A B : Ty) : PolyTerm (.sum A B) (.list B) :=
  (PolyTerm.sumMap (polyNil A B) (polyPure B)).comp (PolyTerm.codiag (.list B))

@[simp] lemma polyInrStep_eval (A B : Ty) : (polyInrStep A B).eval
    = fun x => (match x with | Sum.inl _ => ([] : List B.Elt) | Sum.inr b => [b]) := by
  funext x
  cases x <;> rfl

theorem polyInrStep_reduced (A B : Ty) : (polyInrStep A B).Reduced :=
  ⟨⟨polyNil_reduced A B, polyPure_reduced B⟩, trivial⟩

/-- The entries of a list over `A + B` that come from `B`. -/
def polyInrPart (A B : Ty) : PolyTerm (.list (.sum A B)) (.list B) :=
  (PolyTerm.map (polyInrStep A B)).comp (PolyTerm.concat B)

@[simp] lemma polyInrPart_eval (A B : Ty) : (polyInrPart A B).eval = fun u => inrPart u := by
  funext u
  show ((u.map (polyInrStep A B).eval).flatten) = inrPart u
  rw [inrPart]
  congr 1
  refine List.map_congr_left (fun x _ => ?_)
  cases x <;> rfl

theorem polyInrPart_reduced (A B : Ty) : (polyInrPart A B).Reduced :=
  ⟨polyInrStep_reduced A B, trivial⟩

/-- The entry of a list over `A + B`, as a list of at most one entry, kept when it comes from
`A`. -/
def polyInlStep (A B : Ty) : PolyTerm (.sum A B) (.list A) :=
  (PolyTerm.sumMap (polyPure A) (polyNil B A)).comp (PolyTerm.codiag (.list A))

@[simp] lemma polyInlStep_eval (A B : Ty) : (polyInlStep A B).eval
    = fun x => (match x with | Sum.inl a => [a] | Sum.inr _ => ([] : List A.Elt)) := by
  funext x
  cases x <;> rfl

theorem polyInlStep_reduced (A B : Ty) : (polyInlStep A B).Reduced :=
  ⟨⟨polyPure_reduced A, polyNil_reduced B A⟩, trivial⟩

/-- The first entry of a list over `A + B`, if it comes from `A`. -/
def polyHeadInl (A B : Ty) : PolyTerm (.list (.sum A B)) (.list A) :=
  (PolyTerm.uncons (.sum A B)).comp
    ((PolyTerm.sumMap (polyNil .one A)
        ((PolyTerm.fst (.sum A B) (.list (.sum A B))).comp (polyInlStep A B))).comp
      (PolyTerm.codiag (.list A)))

@[simp] lemma polyHeadInl_eval (A B : Ty) : (polyHeadInl A B).eval = fun v => headInl v := by
  funext v
  match v with
  | [] => rfl
  | Sum.inl a :: v => rfl
  | Sum.inr b :: v => rfl

theorem polyHeadInl_reduced (A B : Ty) : (polyHeadInl A B).Reduced :=
  ⟨trivial, ⟨⟨polyNil_reduced .one A, ⟨trivial, polyInlStep_reduced A B⟩⟩, trivial⟩⟩

/-- The contribution of one cut to the longest prefix of entries from `A`: a cut whose prefix
contains no entry from `B` contributes the first entry of its suffix, if that entry comes from
`A`. -/
def polyStepTwi (A B : Ty) :
    PolyTerm (.prod (.list (.sum A B)) (.list (.sum A B))) (.list A) :=
  (((((PolyTerm.prodMap (polyInrPart A B) (.id (.list (.sum A B)))).comp
      (polySwap (.list B) (.list (.sum A B)))).comp
      (PolyTerm.prodMap (.id (.list (.sum A B))) (PolyTerm.uncons B))).comp
      (PolyTerm.distr (.list (.sum A B)) .one (.prod B (.list B)))).comp
      (PolyTerm.sumMap
        ((PolyTerm.fst (.list (.sum A B)) .one).comp (polyHeadInl A B))
        (polyNil (.prod (.list (.sum A B)) (.prod B (.list B))) A))).comp
    (PolyTerm.codiag (.list A))

@[simp] lemma polyStepTwi_eval (A B : Ty) : (polyStepTwi A B).eval
    = fun z => (match inrPart z.1 with | [] => headInl z.2 | _ => []) := by
  funext z
  obtain ⟨u, v⟩ := z
  simp only [polyStepTwi, PolyTerm.eval_comp, PolyTerm.eval_prodMap, PolyTerm.eval_id,
    polySwap_eval, polyInrPart_eval]
  cases h : inrPart u with
  | nil => exact congrFun (polyHeadInl_eval A B) v
  | cons b w => rfl

theorem polyStepTwi_reduced (A B : Ty) : (polyStepTwi A B).Reduced :=
  ⟨⟨⟨⟨⟨⟨polyInrPart_reduced A B, trivial⟩, polySwap_reduced _ _⟩, ⟨trivial, trivial⟩⟩, trivial⟩,
    ⟨⟨trivial, polyHeadInl_reduced A B⟩, polyNil_reduced _ A⟩⟩, trivial⟩

/-- The first component of the block split: the longest prefix of entries from `A`. -/
def polyTwi (A B : Ty) : PolyTerm (.list (.sum A B)) (.list A) :=
  (((PolyTerm.splits (.sum A B)).comp
      (polyReverse (.prod (.list (.sum A B)) (.list (.sum A B))))).comp
    (PolyTerm.map (polyStepTwi A B))).comp (PolyTerm.concat A)

@[simp] lemma polyTwi_eval (A B : Ty) : (polyTwi A B).eval = fun m => twiFun m := by
  funext m
  show ((((polyReverse (.prod (.list (.sum A B)) (.list (.sum A B)))).eval
    (splitsList m)).map (polyStepTwi A B).eval).flatten) = twiFun m
  simp only [polyReverse_eval, polyStepTwi_eval]
  rw [twiFun]
  congr 1
  refine List.map_congr_left (fun z _ => ?_)
  cases inrPart z.1 <;> rfl

theorem polyTwi_reduced (A B : Ty) : (polyTwi A B).Reduced :=
  ⟨⟨⟨trivial, polyReverse_reduced _⟩, polyStepTwi_reduced A B⟩, trivial⟩

/-- The contribution of one cut whose suffix begins with an entry from `B`: that entry, together
with the block of entries from `A` that follows it. -/
def polyBlockStep (A B : Ty) :
    PolyTerm (.prod (.list (.sum A B)) B) (.list (.prod B (.list A))) :=
  (((PolyTerm.prodMap (polyTwi A B) (.id B)).comp (polySwap (.list A) B)).comp
    (polyPure (.prod B (.list A))))

@[simp] lemma polyBlockStep_eval (A B : Ty) : (polyBlockStep A B).eval
    = fun p => [(p.2, twiFun p.1)] := by
  funext p
  obtain ⟨rest, b⟩ := p
  show [(b, (polyTwi A B).eval rest)] = _
  rw [polyTwi_eval]

theorem polyBlockStep_reduced (A B : Ty) : (polyBlockStep A B).Reduced :=
  ⟨⟨⟨polyTwi_reduced A B, trivial⟩, polySwap_reduced _ _⟩, polyPure_reduced _⟩

/-- The contribution of one cut to the second component of the block split. -/
def polyStepBs (A B : Ty) :
    PolyTerm (.prod (.list (.sum A B)) (.list (.sum A B))) (.list (.prod B (.list A))) :=
  (((PolyTerm.snd (.list (.sum A B)) (.list (.sum A B))).comp
      (PolyTerm.uncons (.sum A B))).comp
      (PolyTerm.sumMap (polyNil .one (.prod B (.list A)))
        ((((polySwap (.sum A B) (.list (.sum A B))).comp
            (PolyTerm.distr (.list (.sum A B)) A B)).comp
            (PolyTerm.sumMap
              (polyNil (.prod (.list (.sum A B)) A) (.prod B (.list A)))
              (polyBlockStep A B))).comp
          (PolyTerm.codiag (.list (.prod B (.list A))))))).comp
    (PolyTerm.codiag (.list (.prod B (.list A))))

@[simp] lemma polyStepBs_eval (A B : Ty) : (polyStepBs A B).eval
    = fun z => (match z.2 with
        | Sum.inr b :: rest => [(b, twiFun rest)]
        | _ => []) := by
  funext z
  obtain ⟨u, v⟩ := z
  match v with
  | [] => rfl
  | Sum.inl a :: rest => rfl
  | Sum.inr b :: rest =>
      show (polyBlockStep A B).eval (rest, b) = _
      rw [polyBlockStep_eval]

theorem polyStepBs_reduced (A B : Ty) : (polyStepBs A B).Reduced :=
  ⟨⟨⟨trivial, trivial⟩,
    ⟨polyNil_reduced .one _,
      ⟨⟨⟨polySwap_reduced _ _, trivial⟩,
        ⟨polyNil_reduced _ _, polyBlockStep_reduced A B⟩⟩, trivial⟩⟩⟩, trivial⟩

/-- The second component of the block split. -/
def polyBs (A B : Ty) : PolyTerm (.list (.sum A B)) (.list (.prod B (.list A))) :=
  (((PolyTerm.splits (.sum A B)).comp
      (polyReverse (.prod (.list (.sum A B)) (.list (.sum A B))))).comp
    (PolyTerm.map (polyStepBs A B))).comp (PolyTerm.concat (.prod B (.list A)))

@[simp] lemma polyBs_eval (A B : Ty) : (polyBs A B).eval = fun l => bsFun l := by
  funext l
  show ((((polyReverse (.prod (.list (.sum A B)) (.list (.sum A B)))).eval
    (splitsList l)).map (polyStepBs A B).eval).flatten) = bsFun l
  simp only [polyReverse_eval, polyStepBs_eval]
  rw [bsFun]
  congr 1
  refine List.map_congr_left (fun z _ => ?_)
  cases hz : z.2 with
  | nil => rfl
  | cons x rest => cases x <;> rfl

theorem polyBs_reduced (A B : Ty) : (polyBs A B).Reduced :=
  ⟨⟨⟨trivial, polyReverse_reduced _⟩, polyStepBs_reduced A B⟩, trivial⟩

/-- **Exercise `exer:block-from-split`**, the term: the two components, each computed by running
over the cuts of the input list. -/
def polyBlockSplit (A B : Ty) :
    PolyTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A)))) :=
  (PolyTerm.diag (.list (.sum A B))).comp (PolyTerm.prodMap (polyTwi A B) (polyBs A B))

@[simp] lemma polyBlockSplit_eval (A B : Ty) :
    (polyBlockSplit A B).eval = fun l => splitList l := by
  funext l
  show ((polyTwi A B).eval l, (polyBs A B).eval l) = splitList l
  simp only [polyTwi_eval, polyBs_eval, twiFun_eq, bsFun_eq]
  rfl

theorem polyBlockSplit_reduced (A B : Ty) : (polyBlockSplit A B).Reduced :=
  ⟨trivial, polyTwi_reduced A B, polyBs_reduced A B⟩

/-! ## Exercise `nolabel:exer-pref-from-mult` -/

/-- The contribution of one cut to the prefix products: a non-empty prefix contributes its
product, computed by `mult`, and the empty prefix contributes nothing. -/
def polyPrefStep (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    PolyMultTerm (.list G) (.list G) :=
  (((PolyMultTerm.ofPoly ((PolyTerm.diag (.list G)).comp
      (PolyTerm.prodMap (.id (.list G)) (PolyTerm.uncons G)))).comp
      (PolyMultTerm.ofPoly (PolyTerm.distr (.list G) .one (.prod G (.list G))))).comp
      (PolyMultTerm.sumMap
        (PolyMultTerm.ofPoly (polyNil (.prod (.list G) .one) G))
        (((PolyMultTerm.ofPoly (PolyTerm.fst (.list G) (.prod G (.list G)))).comp
            (PolyMultTerm.mult G grp hfin)).comp
          (PolyMultTerm.ofPoly (polyPure G))))).comp
    (PolyMultTerm.ofPoly (PolyTerm.codiag (.list G)))

lemma polyPrefStep_eval (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    ∀ u : List G.Elt, (polyPrefStep G grp hfin).eval u
      = (match u with | [] => [] | a :: v => [groupListProd G grp (a :: v)])
  | [] => rfl
  | _ :: _ => rfl

theorem polyPrefStep_noPref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    (polyPrefStep G grp hfin).NoPref :=
  ⟨⟨⟨⟨trivial, trivial, trivial⟩, trivial⟩,
    ⟨(polyNil_reduced _ G).noPref _, ⟨trivial, trivial⟩, (polyPure_reduced G).noPref _⟩⟩, trivial⟩

/-- **Exercise `nolabel:exer-pref-from-mult`**, the term: every non-empty prefix of the input list
contributes its product, and the products are collected in the order of the cuts. -/
def polyPref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    PolyMultTerm (.list G) (.list G) :=
  ((PolyMultTerm.ofPoly ((PolyTerm.splits G).comp
      (polyReverse (.prod (.list G) (.list G))))).comp
    (PolyMultTerm.map
      ((PolyMultTerm.ofPoly (PolyTerm.fst (.list G) (.list G))).comp
        (polyPrefStep G grp hfin)))).comp
    (PolyMultTerm.ofPoly (PolyTerm.concat G))

lemma polyPref_eval (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) (l : List G.Elt) :
    (polyPref G grp hfin).eval l = (PolyTerm.pref G grp hfin).eval l := by
  letI := grp
  have hstep : ∀ u : List G.Elt, (polyPrefStep G grp hfin).eval u = prefStep u := by
    intro u
    match u with
    | [] => rfl
    | a :: u => rfl
  show ((((polyReverse (.prod (.list G) (.list G))).eval (splitsList l)).map
    (fun z => (polyPrefStep G grp hfin).eval z.1)).flatten) = _
  simp only [polyReverse_eval, hstep]
  exact prefFun_eq l

theorem polyPref_noPref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    (polyPref G grp hfin).NoPref :=
  ⟨⟨⟨trivial, (polyReverse_reduced _).noPref _⟩,
    ⟨trivial, polyPrefStep_noPref G grp hfin⟩⟩, trivial⟩

/-! ## The three exercises -/

/-- **Exercise `exer:reverse-from-split`.**  The atomic function `reverse` is defined by a
polyregular term that does not use it: the term applies the atomic function `split` of Definition
`def:polyregular-terms`, keeps the suffix of every cut, replaces it by the list of its first entry,
and concatenates. -/
theorem reverse_from_split (A : Ty) :
    ∃ t : PolyTerm (.list A) (.list A), t.NoReverse ∧
      ∀ l : List A.Elt, t.eval l = l.reverse :=
  ⟨polyReverse A, (polyReverse_reduced A).noReverse _,
    fun l => congrFun (polyReverse_eval A) l⟩

/-- **Exercise `exer:block-from-split`.**  The block split of Example `ex:block` is defined by a
polyregular term that uses neither it nor `reverse`. -/
theorem block_from_split (A B : Ty) :
    ∃ t : PolyTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A)))),
      t.NoBlockSplit ∧ t.NoReverse ∧
        ∀ l : List (A.Elt ⊕ B.Elt), t.eval l = splitList l :=
  ⟨polyBlockSplit A B, (polyBlockSplit_reduced A B).noBlockSplit _,
    (polyBlockSplit_reduced A B).noReverse _, fun l => congrFun (polyBlockSplit_eval A B) l⟩

/-- **No longer an exercise of the book.**  Group prefix multiplication is defined by a term of the
polyregular syntax extended by the product `mult` of a list, which does not use group prefix
multiplication itself.

This was Exercise `nolabel:exer-pref-from-mult`, which the author has withdrawn, replacing it with
`exer:split-triple`.  The statement is kept because it is proved and the fact is worth having; it
is no longer aliased in `RequestProject/Labels.lean`, where the withdrawal is recorded. -/
theorem pref_from_mult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    ∃ t : PolyMultTerm (.list G) (.list G), t.NoPref ∧
      ∀ l : List G.Elt, t.eval l = (PolyTerm.pref G grp hfin).eval l :=
  ⟨polyPref G grp hfin, polyPref_noPref G grp hfin, fun l => polyPref_eval G grp hfin l⟩

/-! ## The three statements in the higher-order syntax

These are the ones that the proof of Lemma `lem:fewer-atomic` appeals to, in
`RequestProject/PartD/HOFewer.lean`; they are weaker than the exercises above, since a polyregular
term is in particular a higher-order term. -/

/-- The higher-order form of Exercise `exer:reverse-from-split`: the atomic function `reverse` is
defined by a closed higher-order term that uses only the reduced set of atomic functions of Lemma
`lem:fewer-atomic`. -/
theorem reverse_from_split_higherOrder (A : HTy) :
    ∃ t : HTerm [] (.arrow (.list A) (.list A)), t.Small ∧
      ∀ l : List A.Sem, t.eval .nil l = l.reverse :=
  ⟨HTerm.reverseTerm [] A, HAtom.smallImpl_small (.reverse A) [],
    fun l => congrFun (HTerm.reverseTerm_eval (Γ := []) (A := A) .nil) l⟩

/-- The higher-order form of Exercise `exer:block-from-split`: the block split is defined by a
closed higher-order term that uses neither it nor `reverse`. -/
theorem block_from_split_higherOrder (A B : HTy) :
    ∃ t : HTerm [] (.arrow (.list (.sum A B))
      (.prod (.list A) (.list (.prod B (.list A))))), t.Small ∧
        ∀ l : List (A.Sem ⊕ B.Sem), t.eval .nil l = splitList l :=
  ⟨HTerm.blockSplitTerm [] A B, HAtom.smallImpl_small (.blockSplit A B) [],
    fun l => congrFun (HTerm.blockSplitTerm_eval (Γ := []) (A := A) (B := B) .nil) l⟩

/-- The higher-order form of Exercise `nolabel:exer-pref-from-mult`: group prefix multiplication is
defined by a closed higher-order term that does not use it, but uses the product `mult` of a
list. -/
theorem pref_from_mult_higherOrder (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    ∃ t : HTerm [] (.arrow (.list (HTy.ofTy G)) (.list (HTy.ofTy G))), t.Small ∧
      ∀ l : List (HTy.ofTy G).Sem, t.eval .nil l = groupPrefixProd G grp l :=
  ⟨HTerm.prefTerm [] G grp hfin, HAtom.smallImpl_small (.pref G grp hfin) [],
    fun l => congrFun (HTerm.prefTerm_eval (Γ := []) (G := G) (grp := grp) (hfin := hfin) .nil) l⟩

end Exercises
end Transducers
