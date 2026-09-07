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

In this project pairing and co-pairing are constructors of the term syntax and
the book's diagonal, co-diagonal and functoriality combinators are derived from
them (`Transducers.tfun_prodMap`, `Transducers.tfun_sumMap`), which is the
reverse of the book's order; the two presentations define the same class of
terms.  The divergence is recorded in `THEOREMS.md` and in the docstring of
`PartC/CombTerms.lean`.

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
