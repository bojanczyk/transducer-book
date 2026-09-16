/-
Part D: Polyregular functions
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Part D and the statements of its
theorems and lemmas.  All of them are proved: Theorem
`thm:polyregular-functions-are-continuous`, Theorem `thm:for-transducers-are-polyregular`, Lemma
`lem:prenex-normal-form`, Lemma `lem:for-closed-under-composition`, Theorem
`thm:pebble-are-continuous` and Theorem `thm:pebble-are-for`.

The five results of Section *Pebble transducers* that speak about the string representation of
configurations and of child configuration graphs -- Lemma `lem:reachability-pebble-automaton` and
Claim `claim:reachability-basic-run` (`RequestProject/PartD/PebReach.lean`), Claim
`claim:from-child-configuration-graph-to-children` (`RequestProject/PartD/ChildGraphFor.lean`), and
Claim `claim:from-configuration-to-child-configuration-graph` together with Lemma
`lem:children-of-configuration-in-pebble-run` (`RequestProject/PartD/CGFor.lean`) -- are proved as
well, but in files that come *after* this one, because two of them are obtained from Theorem
`thm:pebble-are-for` and Theorem `thm:for-transducers-are-polyregular`, which are stated here.
The two headline theorems are therefore not proved through those five results: Theorem
`thm:pebble-are-continuous` is proved from the regularity of the languages of pebble automata
(`RequestProject/PartD/PebbleLev1.lean`), of which Lemma `lem:reachability-pebble-automaton` is
another consequence, and the step of Theorem `thm:pebble-are-for` for which the book uses Lemma
`lem:children-of-configuration-in-pebble-run` -- that a pebble transducer computes a polyregular
function -- is proved by the induction on the number of pebbles of
`RequestProject/PartD/PebblePoly.lean`. -/
import RequestProject.PartC.MSO
import RequestProject.PartD.PolyDef
import RequestProject.PartD.ForCompTop
import RequestProject.PartD.PolyFor
import RequestProject.PartD.PebbleReg
import RequestProject.PartD.PebblePoly
import RequestProject.PartD.PebbleForTop
import RequestProject.PartD.PolyTermComplete
import RequestProject.PartD.HOEasy
import RequestProject.PartD.HOFund
import RequestProject.PartD.HOFewer
import RequestProject.PartD.HONat
import RequestProject.PartD.HOTiling

namespace Transducers

/-! ## Polyregular functions (Definition `def:polyregular-functions`) -/

/-! **Example 33 (Marked squaring)** (`markedSquare`) is defined in
`RequestProject/PartD/MarkedSquare.lean`, together with the proof that it is continuous, which is
the main step in the proof of Theorem `thm:polyregular-functions-are-continuous` below. -/

/-! The family of prime polyregular functions (`Transducers.PolyregularFam`) and Definition
`def:polyregular-functions` itself (`Transducers.IsPolyregular`) are defined, unchanged, in
`RequestProject/PartD/PolyDef.lean`, so that the constructions proving Theorem
`thm:for-transducers-are-polyregular` can be developed before the statements below. -/

/-- **Theorem `thm:polyregular-functions-are-continuous`.**  Polyregular functions are continuous. -/
theorem polyregular_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPolyregular f) : Continuous f := by
  induction hf with
  | base h =>
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact continuous_of_isRegularFun hreg
      · exact Continuous.congr
          ((continuous_map (e'.symm : A₀ ⊕ A₀ → _)).comp
            ((continuous_markedSquare A₀).comp (continuous_map (e : _ → A₀))))
          (fun w => (hfe w).symm)
  | id A => exact continuous_id
  | comp _ _ ihf ihg => exact ihg.comp ihf

/-! ## For-transducers

The syntax and the semantics of the for-transducers -- `Transducers.ForTest`,
`Transducers.ForProg`, `Transducers.ForTest.Holds`, `Transducers.forLoopRun`,
`Transducers.ForProg.exec`, `Transducers.ForProg.eval`, `Transducers.ForProg.LoopFree`,
`Transducers.ForProg.nestLoops`, `Transducers.ForProg.OutputsAtMostOne`, Definition
`def:prenex-normal-form-for-transducers` (`Transducers.ForProg.PrenexForm`) and
`Transducers.IsForTransducer` -- are defined, unchanged, in
`RequestProject/PartD/ForDef.lean`, so that the constructions proving Lemma
`lem:prenex-normal-form` and Lemma `lem:for-closed-under-composition` can be developed before
the statements below. -/

/-! ### Equivalence with polyregular functions -/

/-- **Theorem `thm:for-transducers-are-polyregular`.**  A string-to-string function is polyregular
if and only if it is computed by a for-transducer. -/
theorem polyregular_iff_forTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f :=
  ⟨fun hf => isForTransducer_of_isPolyregular hf ‹Finite A› ‹Finite B›,
    PolyEnum.isPolyregular_of_isForTransducer⟩

/-- **Lemma `lem:prenex-normal-form`.**  Every for-transducer is equivalent to one in prenex
form. -/
theorem forTransducer_prenex {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w :=
  forTransducer_prenex_aux P

/-- **Lemma `lem:for-closed-under-composition`.**  String-to-string functions computed by
for-transducers are closed under composition. -/
theorem forTransducer_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f) :=
  forTransducer_comp_aux hf hg

/-! ## A functional programming language

Definition `def:polyregular-terms` -- the syntax `Transducers.PolyTerm` of the polyregular terms,
their semantics `Transducers.PolyTerm.eval`, the type-to-type functions
`Transducers.IsPolyregularTermFun` that they define, and the new atomic function
`Transducers.splitsList` -- is in `RequestProject/PartD/PolyTerms.lean`, and the notion of a
type-to-type function that is polyregular under string representation,
`Transducers.IsPolyregularUnderRepr`, is in `RequestProject/PartD/PolyRepr.lean`, so that the
constructions proving the theorem below can be developed before it is stated.  The two directions
of the theorem are `Transducers.polyregularTerm_isPolyregular`
(`RequestProject/PartD/PolyTermEasy.lean`) and `Transducers.polyregularTerm_of_isPolyregular`
(`RequestProject/PartD/PolyTermComplete.lean`). -/

/-- **Theorem `thm:polyregular-terms`.**  A type-to-type function is polyregular under string
representation if and only if it is defined by some polyregular term. -/
theorem polyregular_iff_polyregularTerm {A B : Ty} (f : A.Elt → B.Elt) :
    IsPolyregularUnderRepr f ↔ IsPolyregularTermFun f :=
  ⟨polyregularTerm_of_isPolyregular, polyregularTerm_isPolyregular⟩

/-! ### Higher-order terms

Definition `def:higher-order-types` (`Transducers.HTy`, with its semantics `Transducers.HTy.Sem`
and the arrow-free types `Transducers.HTy.ArrowFree`) and Definition `def:higher-order-terms` (the
syntax `Transducers.HTerm`, its semantics `Transducers.HTerm.eval` and the type-to-type functions
`Transducers.IsHigherOrderTermFun` that the closed terms define) are in
`RequestProject/PartD/HOSyntax.lean`, so that the constructions proving the theorem below can be
developed before it is stated.  Lemma `lem:fewer-atomic` is
`Transducers.exists_small_higherOrderTerm` (`RequestProject/PartD/HOFewer.lean`), and the two
directions of the theorem are `Transducers.isHigherOrderTermFun_of_isPolyregularTermFun`
(`RequestProject/PartD/HOEasy.lean`) and
`Transducers.isPolyregularUnderRepr_of_smallHigherOrderTermFun`
(`RequestProject/PartD/HOFund.lean`), the latter applied to the term with the reduced set of
atomic functions that Lemma `lem:fewer-atomic` provides.

The hard direction follows the book's own route: the *good functions* of the Fundamental Lemma,
which are a Kripke logical relation over the polyregular functions (`Transducers.Rel`,
`RequestProject/PartD/HORel.lean`).  A term of arrow type is related to a family of functions when
it maps related arguments to related results, uniformly in a parameter and after any polyregular
change of parameters, and at an arrow-free type being related to a family means that the family is
polyregular under string representation -- which is Lemma
`lem:good-functions-are-polyregular-at-arrow-free-types`, `Transducers.Rel.iff_polyregular`.  Claim
`claim:logical-relations-closed-under-precomposition` is `Transducers.Rel.reindex` of the same
file.  The Fundamental Lemma itself, which carries no label in the book, is
`Transducers.HTerm.rel_eval` (`RequestProject/PartD/HOFund.lean`): every term is related to its own
semantics, which at an arrow-free type is exactly the statement of the theorem.

The naturality that the book uses in the induction basis of the Fundamental Lemma, for the atomic
functions, is in `RequestProject/PartD/HONat.lean`: the arrow-free type functors
`Transducers.TyFun` and their action on functions, the Definition of a natural transformation
(`Transducers.IsNaturalTransformation`, which carries no label in the book), Claim
`claim:atomic-functions-are-natural-transformations` (`Transducers.atoms_are_natural`) and Claim
`claim:functors-applied-to-good` (`Transducers.good_of_functor_applied`). -/

/-- **Theorem `thm:higher-order-terms`.**  A function between two arrow-free types is polyregular
if and only if it is defined by a higher-order term.  Arrow-freeness is expressed here by taking
the two types in `Transducers.Ty`, the types of Definition `def:types`, which are the arrow-free
higher-order types (`Transducers.HTy.exists_ofTy`); polyregularity of a function between types is,
as in Theorem `thm:polyregular-terms`, polyregularity under string representation. -/
theorem polyregular_iff_higherOrderTerm {A B : Ty} (f : A.Elt → B.Elt) :
    IsPolyregularUnderRepr f ↔ IsHigherOrderTermFun f :=
  ⟨fun h => isHigherOrderTermFun_of_isPolyregularTermFun
      ((polyregular_iff_polyregularTerm f).mp h),
    fun h => isPolyregularUnderRepr_of_smallHigherOrderTermFun
      (isSmallHigherOrderTermFun_of_isHigherOrderTermFun h)⟩

/-! ### Undecidability of equivalence at higher-order types

Of the three results of this subsection, one is formalised.

* Lemma `lem:tiling-checker` is `Transducers.tiling_checker` below; the term it provides is
  `Transducers.HOTile.checkTerm` (`RequestProject/PartD/HOTiling.lean`), and the tiling problem it
  is about -- which the book states inside the proof of Theorem `thm:undecidability-higher-order`,
  referring to a picture that the sources available here do not contain -- is
  `Transducers.Tiling.Instance`, `Transducers.Tiling.IsSolution` and
  `Transducers.Tiling.Solvable` (`RequestProject/PartD/Tiling.lean`), where the conditions on a
  solution are taken from the author's own proof of Lemma `lem:tiling-checker`.
* Lemma `lem:tiling` (the tiling problem is undecidable) and Theorem
  `thm:undecidability-higher-order` (the equivalence problem for higher-order polyregular terms is
  undecidable) are **not formalised**.  `THEOREMS.md` says precisely what each of them would
  require; in short, the first needs the reduction of the halting problem to the tiling problem,
  which is a development of its own, and the second needs, on top of it, an encoding of the terms
  of Definition `def:higher-order-terms` as data, so that "decidable" can be said of a problem
  about terms at all.

What *is* proved about the reduction, and is the other half of the proof of Theorem
`thm:undecidability-higher-order`, is `Transducers.HOTile.checkTerm_eq_falseTerm_iff`: the term of
Lemma `lem:tiling-checker` has the same semantics as the constant `false` term exactly when the
instance has no solution. -/

/-- **Lemma `lem:tiling-checker`.**  For every instance of the tiling problem there is a
higher-order polyregular term of type

    1* × ((1* × 1*) → T) → (1 + 1),

where `T` is the type of the tiles of the instance, which answers whether the restriction of `f`
to `{0,…,n} × {0,…,n}` is a solution.  The number `n` is given in unary, as a list of units, and
the solution is read off from `f` by `Transducers.HOTile.gridOf`.

The instance is assumed well formed (`Transducers.Tiling.Instance.WF`): its two corner tiles and
the tiles of its local constraint are tiles of the instance.  This is not a restriction of the
book's statement, where `s, t ∈ T` and `C ⊆ T⁴` hold by fiat; it has to be said here because the
tiles of an instance are presented as the natural numbers `0, …, maxTile`. -/
theorem tiling_checker (I : Tiling.Instance) (hI : I.WF) :
    ∃ chk : HTerm []
      (.arrow (.prod (.list .one)
        (.arrow (.prod (.list .one) (.list .one)) (HOTile.tileTy I.maxTile))) (.sum .one .one)),
      ∀ (n : List Unit) (f : List Unit × List Unit → (HOTile.tileTy I.maxTile).Sem),
        chk.eval .nil (n, f) = HOTile.trueS ↔
          Tiling.IsSolution I n.length (HOTile.gridOf I.maxTile f) :=
  ⟨HOTile.checkTerm I, HOTile.eval_checkTerm I hI⟩

/-! ## Pebble transducers

The syntax and the semantics of the pebble transducers -- `Transducers.PebbleView`,
`Transducers.viewOf`, `Transducers.PebbleAction`, `Transducers.Pebble`,
`Transducers.PebbleCfg`, `Transducers.Pebble.stepCfg`, `Transducers.Pebble.Reaches`,
`Transducers.Pebble.Computes` and `Transducers.IsPebbleTransducer` -- are defined, unchanged, in
`RequestProject/PartD/PebbleDef.lean`, so that the constructions proving Theorem
`thm:pebble-are-continuous` can be developed before the statements below. -/

/-! ### Continuity -/

/-- **Theorem `thm:pebble-are-continuous`.**  Pebble transducers compute continuous functions. -/
theorem pebble_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPebbleTransducer f) : Continuous f :=
  continuous_of_isPebbleTransducer hf

/-! ### Equivalence with for-transducers -/

/-- **Theorem `thm:pebble-are-for`.**  Pebble transducers and for-transducers compute the same
string-to-string functions. -/
theorem pebble_iff_forTransducer {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsPebbleTransducer f ↔ IsForTransducer f :=
  ⟨fun h => (polyregular_iff_forTransducer f).mp (isPolyregular_of_isPebbleTransducer h),
    PebFor.isPebbleTransducer_of_isForTransducer⟩

end Transducers
