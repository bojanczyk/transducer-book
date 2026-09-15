# Section D.3 brought back into line with the rewritten `higher-order.tex`

Section *A functional programming language* has been rewritten by the author.
The normalisation proof of Theorem `thm:higher-order-terms` is gone from the
book, replaced wholesale by the *good functions* argument, which is what the
formalisation was already using; three results of the new text were already
formalised under no name, and three more are new.  This run relabels, deletes
and adds accordingly.  Everything below is proved outright: `lake build`
succeeds, no file contains `sorry`, `axiom` or `native_decide`, and
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for
every alias.

## 1. The normalisation proof is gone

Eight labels disappeared from the book with it — the definition of a resource
bound, the claim that the terms consistent with one are parsed by a finite
automaton, the reduction-strategy lemma, the normalisation corollary, the lemma
on the normal forms of arrow-free terms, the definition of majorants, and the
two majorisation claims — and `tools/tex_numbering.py --check` failed on all
eight.  Their rows in `LABELS.md` and in the index of `THEOREMS.md` and their
aliases in `RequestProject/Labels.lean` are removed, and so are the three
`## Status` sections of `THEOREMS.md` that described that route: the checker
rejects any mention of a label the book does not have.

The Lean behind them was the machinery of the old route and renders no result of
the book any more, so it is deleted rather than left to compile:

| deleted file | what it held |
| --- | --- |
| `PartD/HOBound.lean` | the resource bounds and consistency with one |
| `PartD/HOStr.lean` | the string representation of a higher-order term |
| `PartD/HOParse.lean` | regularity of the language of the terms with a resource bound |
| `PartD/HORed.lean` | substitution and the one-step reduction of terms |
| `PartD/HONormal.lean` | the normal forms of arrow-free terms |
| `PartD/HOMaj.lean` | the majorants of a type |

Nothing on the live path used them: the only file that imported any of them was
`PartD/Statements.lean`, whose imports and prose are updated.
`Common/RegLangClosure.lean` is kept — it is a general-purpose library about
regular languages, with nothing in it about transducers or about the deleted
route — and its docstring now says that nothing uses it at present.

## 2. Results the book now states whose Lean already existed

Checked against the book's text and aliased:

* **Lemma `lem:good-functions-are-polyregular-at-arrow-free-types`** (D.3.9) —
  `Transducers.Rel.iff_polyregular` (`PartD/HORel.lean`).
* **Claim `claim:logical-relations-closed-under-precomposition`** (D.3.10) —
  `Transducers.Rel.reindex` (same file).

`Transducers.Rel` is the book's class of good functions in the form the book
states it: at an arrow type, for every arrow-free type `P` of new parameters,
every polyregular change of parameters `r : P → Q` and every good `σ : P → A`,
the function `p ↦ ρ(r(p))(σ(p))` is good.  Its docstrings now name the two
labels.

## 3. Natural transformations: new work

`RequestProject/PartD/HONat.lean` is new.  `Transducers.HTyFun` is the syntax of
an expression built from type variables `var i` (indexed by `ℕ`, as
`Transducers.Exercises.TyFun` of the Part C exercises already is) and from fixed
arrow-free types, by `1`, `×`, `+` and `*`; `HTyFun.app` applies it to a
valuation of the variables by *higher-order* types, and `HTyFun.map` is the
lifting `F(ρ₁,…,ρₙ)`.  `Transducers.IsNaturalTransformation` is the book's
definition of a natural transformation: the square commutes for functions `ρᵢ`
that are required to be neither good nor polyregular.

* **Claim `claim:atomic-functions-are-natural-transformations`** (D.3.12) —
  `Transducers.atoms_are_natural`, one conjunct for each atomic function of
  `Transducers.HAtom` whose type has the shape `F(A₁,…,Aₙ) → G(A₁,…,Aₙ)`.  `map`
  and `either` are absent, and must be: their arguments are functions, so the
  book's definition does not apply to them, and the book treats them in the
  combinator case of the Fundamental Lemma instead.
* **Claim `claim:functors-applied-to-good`** (D.3.13) —
  `Transducers.good_of_functor_applied`, the equivalence of the claim, by the
  book's induction on the expression.  Merging two factorisations into one uses
  the co-pairing of good functions (`Transducers.Rel.copair`, from
  `Transducers.Rel.glue` and `Transducers.Rel.reindex`), which is the step the
  book performs by hand for the list constructor.

## 4. The three exercises

`RequestProject/Exercises/HOAtomsFromSplit.lean` states them, from the terms
that the proof of Lemma `lem:fewer-atomic` in `PartD/HOFewer.lean` already
builds; they are listed in `EXERCISES.md` and aliased.

| exercise | Lean name |
| --- | --- |
| `exer:reverse-from-split` (D.3.1) | `Transducers.Exercises.reverse_from_split` |
| `exer:block-from-split` (D.3.2) | `Transducers.Exercises.block_from_split` |
| `exer:pref-from-mult` (D.3.3) | `Transducers.Exercises.pref_from_mult` |

Each says that one atomic function dropped by Lemma `lem:fewer-atomic` is
defined by a closed term whose atomic functions are all in the reduced set — so
in particular the dropped one, and for the block split also `reverse`, is not
used.  The book phrases them for polyregular terms; they are stated here for the
higher-order terms with the reduced set, which is the setting in which the book
appeals to them.

## 5. The stale reference

`PartD/HOFewer.lean` and `PartD/HOFewerAux.lean` cited `ex:reverse-from-split`
on four lines; the book has renamed that exercise, and the four lines now cite
`exer:reverse-from-split`.  The two places where those files said that the other
two exercises carry no label are updated as well, since they now do.

## 6. Three environments of the section carry no label

They cannot be aliased, and no placeholder tag is invented for them.  All three
are formalised, and `THEOREMS.md` and `LABELS.md` record them:

* the **Fundamental Lemma** (D.3.7) — `Transducers.HTerm.rel_eval`
  (`PartD/HOFund.lean`), whose statement is unchanged;
* the definition of the **good functions** (D.3.8) — `Transducers.Rel`
  (`PartD/HORel.lean`);
* the definition of a **natural transformation** (D.3.11) —
  `Transducers.IsNaturalTransformation` (`PartD/HONat.lean`).

`Transducers.polyregular_iff_higherOrderTerm` (Theorem `thm:higher-order-terms`)
also keeps its statement.

## Verification

`lake build` succeeds with no errors and no warnings.
`tools/gen_labels.py --check`, `tools/decl_files.py --check` and
`tools/tex_numbering.py --check LABELS.md` all pass, and
`tools/print_axioms.sh` reports that all 278 aliases of
`RequestProject/Labels.lean` depend only on `propext`, `Classical.choice`,
`Quot.sound`.
