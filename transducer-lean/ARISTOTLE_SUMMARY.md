# Two exercises of Part B, and the renumbering of Section *Combinators*

## The two exercises

Both are proved outright, by the author's own solutions, and `#print axioms`
reports only `propext`, `Classical.choice`, `Quot.sound` for each.

* **Exercise `exer:duplication-not-rational`** (`myhill-nerode.tex`) — string
  duplication is not rational, by the argument that is used for string reversal
  in `RequestProject/Exercises/ReverseNotRational.lean`: the relation `∼` of
  Theorem `thm:machine-independent-rational-functions`
  (`Transducers.BoundedVarRel`) has infinite index, and no two distinct strings
  are related.  The new file is
  `RequestProject/Exercises/DuplicateNotRational.lean`, with
  `Transducers.Exercises.not_boundedVarRel_duplicate` and
  `Transducers.Exercises.not_isRationalFun_duplicate_boundedVar`.

  The statement was already in the project: duplication is also the second item
  of Exercise `exer:non-rational`, proved there by the other argument of the
  book, so `Transducers.Exercises.not_isRationalFun_duplicate` already existed
  in `Exercises/PartBC.lean`.  It is left exactly as it was and is the first
  alias of the new label; the proof by the relation `∼` is the second alias.

* **Exercise `exer:no-reverse-reversible`** (`rational-functions.tex`) — the
  reversal of a reversible Mealy machine is not needed among the primes of
  Theorem `thm:rational-primes`.  The new file is
  `RequestProject/Exercises/NoReverseReversible.lean`;
  `Transducers.Exercises.rational_primes_no_reverse_reversible` states that a
  string-to-string function is rational if and only if it is a composition of
  functions from the shortened list
  `Transducers.Exercises.PrimeRatNoRevRevFam` — prime Mealy machines,
  right-to-left *flip-flop* Mealy machines, string homomorphisms and `w ↦ w#`.

  The construction is the author's: append the separator; run a left-to-right
  reversible machine over `Equiv.Perm Q` labelling every position with the
  product of the permutations of the letters before it, and the separator with
  the product over the whole input; broadcast that product leftwards with a
  right-to-left flip-flop machine; and recover the output letter with a
  homomorphism, by cancellation in the group of permutations.

## The renumbering of Section *Combinators*

The section gained a labelled environment, Claim `claim:pairing-copairing`
(C.5.8), which shifted the nine numbers after it.  `LABELS.md` is updated, the
claim has a row in the index of `THEOREMS.md` and an alias in
`RequestProject/Labels.lean`, and it is proved:
`Transducers.IsRegularTermFun.pair` and `Transducers.IsRegularTermFun.copair`
of `PartC/CombFinite.lean`.

The syntax `Transducers.RegTerm` of `PartC/CombTerms.lean` follows the book's
list: the diagonal and the co-diagonal are atomic terms, the combinators are
composition and the three functoriality combinators `f × g`, `f + g` and `f*`
(`Transducers.IsRegularTermFun.prodMap`, `sumMap`, `mapList`), and pairing and
co-pairing are derived from them, which is the claim.

`tools/decl_files.py --check` also failed before this run, for an unrelated
reason: a line of the docstring of `Transducers.terms_define_append_hash` began
with the word `end-marker`, which the script reads as the end of a namespace, so
it could not find the declaration.  The docstring is reworded.

## Verification

`lake build` succeeds with no errors and no warnings.  No file added or changed
by this run contains a `sorry`, an `axiom` or a `native_decide`.
`tools/gen_labels.py --check`, `tools/decl_files.py --check` and
`tools/tex_numbering.py --check` all pass, and `tools/print_axioms.sh` reports
that all 240 aliases depend only on `propext`, `Classical.choice`, `Quot.sound`.

## Verification pass (re-checked end to end)

The state of Section *Combinators* described above was re-verified from a clean
build in a later pass:

* `lake build` of the whole project succeeds with no errors and no warnings
  (8499 jobs).
* `RequestProject/PartC/CombTerms.lean` contains the only regular-term syntax in
  the project: `Transducers.RegTerm` has the book's atomic terms (diagonal and
  co-diagonal among them) and exactly four combinators — composition and the
  three functoriality combinators — with no `pair`/`copair` constructors, and
  Claim `claim:pairing-copairing` is a theorem
  (`Transducers.IsRegularTermFun.pair`, `Transducers.IsRegularTermFun.copair`)
  rather than an assumption.
* Theorem `thm:regular-terms` is proved in both directions as
  `Transducers.regular_iff_regularTerm`.
* `tools/gen_labels.py --check`, `tools/decl_files.py --check` and
  `tools/tex_numbering.py --check` all pass, and `tools/print_axioms.sh` reports
  that all 240 aliases depend only on `propext`, `Classical.choice`,
  `Quot.sound`.  No `sorry`, `axiom` or `native_decide` occurs in the sources.

## Theorem `thm:rational-terms` (C.5.18): the rational terms

This run proved Theorem `thm:rational-terms` outright, as the equivalence

```
theorem Transducers.rational_iff_rationalTerm {A B : Ty} (f : A.Elt → B.Elt) :
    IsRationalUnderRepr f ↔ IsRatTermFun f
```

in `RequestProject/PartC/RatRepr.lean`, with the syntax
`Transducers.RatTerm` in `RequestProject/PartC/RatTerms.lean`: the atomic terms
and combinators of Definition `def:regular-terms` without reverse and without
the diagonal, plus adjoining units, left distributivity and the list
deconstructor on the right.  The two directions are
`Transducers.ratTerm_isRational` (`RatEasy.lean`) and
`Transducers.ratTerm_of_isRational` (`RatRepr.lean`), and
`Transducers.Book.«thm:rational-terms»` is the alias.

New files: `PartC/RatTerms.lean`, `RatFinite.lean`, `RatDerived.lean`,
`RatStrFam.lean`, `RatAtomA.lean`, `RatAtomB.lean`, `RatAtomC.lean`,
`RatComb.lean`, `RatEasy.lean`, `RatMealyFF.lean`, `RatMealyRev.lean`,
`RatComplete.lean`, `RatRepr.lean`.  The section
*Status (Theorem `thm:rational-terms`: the rational terms)* of `THEOREMS.md`
records the argument and the three places where the missing atoms had to be
worked around: the right-to-left flip-flop machine, which is redone in the
right-to-left direction rather than by reversal; the right-to-left reversible
machines, which Exercise `exer:no-reverse-reversible` removes from the list of
primes; and the inverse of the representation of a product, which uses the
pair-marking machine and two splits instead of pairing.

## Verification

`lake build` succeeds with no errors and no warnings (8512 jobs).  No file added
or changed by this run contains a `sorry`, an `axiom` or a `native_decide`.
`tools/gen_labels.py --check`, `tools/decl_files.py --check` and
`tools/tex_numbering.py --check` all pass, and `tools/print_axioms.sh` reports
that all 243 aliases depend only on `propext`, `Classical.choice`, `Quot.sound`.
