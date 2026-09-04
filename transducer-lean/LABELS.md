# How the Lean files refer to the results of the book

The numbers of the results of *Transducers* (`Theorem C.1.4`) change whenever the
LaTeX sources are edited, so the Lean files do not use them.  A result is
referred to by its LaTeX **label**, in backticks, as in

```
/-- **Theorem `thm:decidable-equivalence-regular`.**  ... -/
```

Some environments of the book carry no `\label`.  For those the Lean files use a
descriptive tag with the prefix `nolabel:`, which marks it as a placeholder
chosen in this project and not as a label of the book; if a label is added to the
LaTeX source, the placeholder should be replaced by it.

Sections and subsections carry no labels either, and are referred to by their
titles, as in `Section *Rational relations and weighted automata*`.

The number column of the dictionary below is read out of the `\newlabel`
entries of `main.aux` by `tools/tex_numbering.py`; `tools/relabel.py` checks that
no book number is left in the sources of this project, and
`tools/gen_labels.py --check` checks `RequestProject/Labels.lean` against this
dictionary and against the index tables.  The numbers are those of the
sources as of this writing and are recorded only to make the table easy to check
against the pdf -- nothing in the project refers to a result by its number.

Two rows of Section *Combinators* carry a `nolabel:` tag although they are
numbered: the lemma that distributivity is regular under string representation
(C.5.5) and the claim that the representations of the elements of a type form a
regular language (C.5.6) carry no `\label` in the sources, so the tags are
placeholders chosen here, and their numbers are read off from the labelled
environments that surround them rather than from `main.aux`.

The one row with no number is the withdrawn Theorem
`nolabel:thm-fo-transduction-into-primes`: the book no longer states it as a
numbered environment, only as an unnumbered paragraph at the end of `logic.tex`,
so it has neither a number nor a `\label`, and the placeholder tag stays.

## The correspondence is checked by Lean

The file `RequestProject/Labels.lean` turns the table below into part of the
formalisation.  For every formalised result it declares, in the namespace
`Transducers.Book`, an alias whose Lean name *is* the label of the result:

```lean
alias «thm:decidable-equivalence-regular» := Transducers.regular_equivalence_decidable
assert_no_sorry «thm:decidable-equivalence-regular»
```

So the compiler checks that every declaration named in the documentation exists,
and a result formalised by several declarations gets the label followed by `#2`,
`#3`, ....  The status of a result is checked as well: `assert_no_sorry` fails if
the declaration depends on `sorryAx`, and the statements that are formalised but
not proved yet carry `assert_uses_sorry` instead, so the statuses recorded in
`THEOREMS.md` cannot silently go stale.  The file ends with a comment listing the
theorem-like environments of the book that are not aliased, with a reason for
each, so that all of them are accounted for.  Nothing in it is used in a proof.

The file is kept in step with the status tables of `THEOREMS.md` and
`EXERCISES.md` by `tools/gen_labels.py`: `--check` (the default) verifies that
every formalised result has an alias and every alias a row, that each alias
target is named in its row, that the kinds agree, that the `#2`, `#3`, ...
suffixes run consecutively, that every environment of the dictionary above is
either aliased or listed with a reason in the trailing comment, and that every
label the project mentions is a label of the book; `--emit LABEL` prints the
boilerplate for a new entry.  It stops short of rewriting the file, because
several entries carry a docstring note that the tables do not contain — the
sense in which a reorganised Lean step renders a claim of the book, say — and a
generator working from the tables alone would delete them.

## Dictionary of labels

| Number | Kind | Label used in the Lean files | LaTeX file |
| --- | --- | --- | --- |
| .0.1 | definition | `def:continuity` | `intro.tex` |
| A.1.1 | definition | `def:mealy-machine` | `mealy.tex` |
| A.1.2 | theorem | `thm:equivalence-decidable-mealy` | `mealy.tex` |
| A.1.3 | theorem | `thm:composition-mealy` | `mealy.tex` |
| A.1.4 | theorem | `thm:continuity-mealy` | `mealy.tex` |
| A.2.1 | definition | `def:prime-mealy-machines` | `krohn-rhodes.tex` |
| A.2.2 | theorem | `thm:krohn-rhodes` | `krohn-rhodes.tex` |
| A.2.3 | definition | `def:map-lifting` | `krohn-rhodes.tex` |
| A.2.4 | lemma | `lem:map-lifting-decomposition-mealy` | `krohn-rhodes.tex` |
| A.2.5 | lemma | `lem:Mealy-map-lifting` | `krohn-rhodes.tex` |
| A.2.6 | lemma | `lem:reversible-composition` | `krohn-rhodes.tex` |
| A.2.7 | definition | `def:aperiodic-mealy` | `krohn-rhodes.tex` |
| A.2.8 | theorem | `thm:aperiodic-mealy` | `krohn-rhodes.tex` |
| A.2.9 | claim | `claim:aperiodic-pumping` | `krohn-rhodes.tex` |
| A.2.10 | lemma | `lemma:derivatives` | `krohn-rhodes.tex` |
| A.2.11 | lemma | `lem:aperiodicity-minimal-machine` | `krohn-rhodes.tex` |
| B.1.1 | definition | `def:nfa-with-output` | `rational-relations.tex` |
| B.1.2 | definition | `def:rational-relation` | `rational-relations.tex` |
| B.1.3 | definition | `def:rational-recognisable-subsets` | `rational-relations.tex` |
| B.1.4 | theorem | `thm:composition-rational-relations` | `rational-relations.tex` |
| B.1.5 | theorem | `thm:continuity-rational-relations` | `rational-relations.tex` |
| B.1.6 | theorem | `thm:undecidable-equivalence-rational-relations` | `rational-relations.tex` |
| B.1.7 | claim | `claim:homomorphism-complement-rational` | `rational-relations.tex` |
| B.2.1 | definition | `def:rational-function` | `rational-functions.tex` |
| B.2.2 | definition | `def:bimachine` | `rational-functions.tex` |
| B.2.3 | theorem | `thm:bimachines` | `rational-functions.tex` |
| B.2.4 | lemma | `lemma:eliminate-epsilon-transitions` | `rational-functions.tex` |
| B.2.5 | lemma | `lem:uniformisation` | `rational-functions.tex` |
| B.2.6 | theorem | `thm:rational-primes` | `rational-functions.tex` |
| B.2.7 | theorem | `thm:rational-is-mealy-characterisation` | `rational-functions.tex` |
| B.3.1 | definition | `def:semiring` | `weighted.tex` |
| B.3.2 | definition | `def:weighted-automaton` | `weighted.tex` |
| B.3.3 | theorem | `thm:equivalence-weighted-automata` | `weighted.tex` |
| B.3.4 | theorem | `thm:equivalence-rational-functions` | `weighted.tex` |
| B.3.5 | lemma | `lem:closure-weighted-automata-precomposition` | `weighted.tex` |
| B.3.6 | theorem | `thm:characterisation-rational-functions-weighted-automata` | `weighted.tex` |
| B.3.7 | theorem | `thm:zeroness-weighted-automata` | `weighted.tex` |
| B.4.1 | theorem | `thm:mealy-machine-independent` | `myhill-nerode.tex` |
| B.4.2 | theorem | `thm:decide-if-mealy` | `myhill-nerode.tex` |
| B.4.3 | lemma | `lem:decide-if-length-preserving` | `myhill-nerode.tex` |
| B.4.4 | claim | `claim:typing-length-preserving` | `myhill-nerode.tex` |
| B.4.5 | lemma | `lem:characterisation-length-preserving` | `myhill-nerode.tex` |
| B.4.6 | theorem | `thm:sequential-function-independent` | `myhill-nerode.tex` |
| B.4.7 | definition | `def:left-distance` | `myhill-nerode.tex` |
| B.4.8 | theorem | `thm:subsequential-functions` | `myhill-nerode.tex` |
| B.4.9 | claim | `claim:bounded-extensions` | `myhill-nerode.tex` |
| B.4.10 | claim | `claim:computing-branching-part` | `myhill-nerode.tex` |
| B.4.11 | claim | `claim:offsets-are-regular` | `myhill-nerode.tex` |
| B.4.12 | claim | `claim:eliminating-negative-letters` | `myhill-nerode.tex` |
| B.4.13 | theorem | `thm:machine-independent-rational-functions` | `myhill-nerode.tex` |
| C.0.1 | definition | `def:regular-functions` | `regular-intro.tex` |
| C.1.1 | theorem | `thm:regular-functions-are-continuous-and-closed-under-composition` | `regular-primes.tex` |
| C.1.2 | lemma | `lem:reversal-duplication-continuous` | `regular-primes.tex` |
| C.1.3 | lemma | `lem:map-lifting-continuous` | `regular-primes.tex` |
| C.1.4 | theorem | `thm:decidable-equivalence-regular` | `regular-primes.tex` |
| C.1.5 | conjecture | `conj:regular-via-weighted-automata` | `regular-primes.tex` |
| C.2.1 | definition | `def:two-way-transducer` | `2dfa.tex` |
| C.2.2 | theorem | `thm:continuity-2dfas` | `2dfa.tex` |
| C.2.3 | lemma | `lem:compute-configuration-graph` | `2dfa.tex` |
| C.2.4 | lemma | `lem:check-if-output-string-of-configuration-graph-belongs-to-L` | `2dfa.tex` |
| C.2.5 | theorem | `thm:composition-of-two-way-transducers` | `2dfa.tex` |
| C.2.6 | lemma | `lem:2dfa-precomposition-with-mealy` | `2dfa.tex` |
| C.2.7 | corollary | `cor:2dfa-closure-under-composition` | `2dfa.tex` |
| C.2.8 | corollary | `cor:2dfa-computes-all-regular-functions` | `2dfa.tex` |
| C.2.9 | theorem | `thm:2dfa-decomposition-into-primes` | `2dfa.tex` |
| C.2.10 | lemma | `lem:regular-closure-properties` | `2dfa.tex` |
| C.2.11 | claim | `claim:conditional` | `2dfa.tex` |
| C.2.12 | lemma | `lem:output-of-snake-graph-is-regular` | `2dfa.tex` |
| C.3.1 | definition | `def:sst` | `sst.tex` |
| C.3.2 | theorem | `theorem:sst-two-way-equivalence` | `sst.tex` |
| C.4.1 | theorem | `thm:mso-logic-languages` | `logic.tex` |
| C.4.2 | lemma | `lem:mso-free-variables` | `logic.tex` |
| C.4.3 | definition | `def:mso-relabeling` | `logic.tex` |
| C.4.4 | theorem | `thm:logic-rational-functions` | `logic.tex` |
| C.4.5 | claim | `claim:transition-formula` | `logic.tex` |
| C.4.6 | claim | `claim:mso-annotation-regular` | `logic.tex` |
| C.4.7 | definition | `def:mso-transduction` | `logic.tex` |
| C.4.8 | theorem | `thm:logic-regular-functions` | `logic.tex` |
| C.4.9 | lemma | `lem:logic-reduction-to-type-n` | `logic.tex` |
| C.4.10 | lemma | `lem:logic-precomputation` | `logic.tex` |
| C.4.11 | theorem | `thm:logic-aperiodic` | `logic.tex` |
| C.4.12 | definition | `def:k-types` | `logic.tex` |
| C.4.13 | lemma | `lem:k-types-fo-equivalence` | `logic.tex` |
| C.4.14 | claim | `claim:fo-composition-quantifier-rank` | `logic.tex` |
| C.4.15 | lemma | `lem:k-types-properties` | `logic.tex` |
| C.4.16 | theorem | `thm:fo-rational-functions` | `logic.tex` |
| (unnumbered) | paragraph | `nolabel:thm-fo-transduction-into-primes` | `logic.tex` |
| C.5.1 | definition | `def:types` | `combinators.tex` |
| C.5.2 | definition | `def:regular-functions-on-types-under-string-representation` | `combinators.tex` |
| C.5.3 | definition | `def:regular-terms` | `combinators.tex` |
| C.5.4 | theorem | `thm:regular-terms` | `combinators.tex` |
| C.5.5 | lemma | `nolabel:lem-distributivity-under-string-representation` | `combinators.tex` |
| C.5.6 | claim | `nolabel:claim-representations-are-a-regular-language` | `combinators.tex` |
| C.5.7 | lemma | `lem:terms-define-string-homomorphisms` | `combinators.tex` |
| C.5.8 | claim | `claim:finite-type-bijection-disjoint-units` | `combinators.tex` |
| C.5.9 | claim | `claim:finite-domain-regular-list-function` | `combinators.tex` |
| C.5.10 | lemma | `lem:terms-define-append-hash` | `combinators.tex` |
| C.5.11 | claim | `claim:bang-definable` | `combinators.tex` |
| C.5.12 | lemma | `lem:terms-define-map-reverse-duplicate` | `combinators.tex` |
| C.5.13 | lemma | `lem:terms-define-flip-flop` | `combinators.tex` |
| C.5.14 | lemma | `lem:terms-define-reversible` | `combinators.tex` |
| C.5.15 | lemma | `lem:terms-define-string-representation` | `combinators.tex` |
| C.5.16 | claim | `claim:head` | `combinators.tex` |
| D.0.1 | definition | `def:polyregular-functions` | `polyregular-intro.tex` |
| D.0.2 | theorem | `thm:polyregular-functions-are-continuous` | `polyregular-intro.tex` |
| D.1.1 | theorem | `thm:for-transducers-are-polyregular` | `polyregular-for.tex` |
| D.1.2 | definition | `def:prenex-normal-form-for-transducers` | `polyregular-for.tex` |
| D.1.3 | lemma | `lemma:prenex-normal-form` | `polyregular-for.tex` |
| D.1.4 | lemma | `lem:for-closed-under-composition` | `polyregular-for.tex` |
| D.2.1 | theorem | `thm:pebble-are-continuous` | `polyregular-pebble.tex` |
| D.2.2 | lemma | `lem:reachability-pebble-automaton` | `polyregular-pebble.tex` |
| D.2.3 | claim | `claim:reachability-basic-run` | `polyregular-pebble.tex` |
| D.2.4 | theorem | `thm:pebble-are-for` | `polyregular-pebble.tex` |
| D.2.5 | lemma | `lem:children-of-configuration-in-pebble-run` | `polyregular-pebble.tex` |
| D.2.6 | claim | `claim:from-configuration-to-child-configuration-graph` | `polyregular-pebble.tex` |
| D.2.7 | claim | `claim:from-child-configuration-graph-to-children` | `polyregular-pebble.tex` |

Sections and subsections:

| Number | Kind | Title | LaTeX file |
| --- | --- | --- | --- |
| A.1 | section | *Mealy machines* | `mealy.tex` |
| A.1.1 | subsection | *Equivalence, compositions and continuity* | `mealy.tex` |
| A.2 | section | *The Krohn-Rhodes Decomposition Theorem* | `krohn-rhodes.tex` |
| A.2.1 | subsection | *Map lifting* | `krohn-rhodes.tex` |
| A.2.2 | subsection | *State transformations* | `krohn-rhodes.tex` |
| A.2.3 | subsection | *Aperiodic Mealy machines* | `krohn-rhodes.tex` |
| B.1 | section | *Rational relations* | `rational-relations.tex` |
| B.1.1 | subsection | *Composition and continuity* | `rational-relations.tex` |
| B.1.2 | subsection | *Undecidable equivalence* | `rational-relations.tex` |
| B.2 | section | *Rational functions* | `rational-functions.tex` |
| B.2.1 | subsection | *Bimachines* | `rational-functions.tex` |
| B.2.2 | subsection | *Decomposition into primes* | `rational-functions.tex` |
| B.2.3 | subsection | *Mealy machines as a subset of the rational functions* | `rational-functions.tex` |
| B.3 | section | *Rational relations and weighted automata* | `weighted.tex` |
| B.3.1 | subsection | *Weighted automata* | `weighted.tex` |
| B.3.2 | subsection | *Decidable equivalence* | `weighted.tex` |
| B.3.3 | subsection | *Decidability of equivalence for weighted automata over a field* | `weighted.tex` |
| B.4 | section | *Machine independent characterisations* | `myhill-nerode.tex` |
| B.4.1 | subsection | *Mealy machines* | `myhill-nerode.tex` |
| B.4.2 | subsection | *Sequential functions* | `myhill-nerode.tex` |
| B.4.3 | subsection | *Subsequential functions* | `myhill-nerode.tex` |
| B.4.4 | subsection | *Rational functions* | `myhill-nerode.tex` |
| C.1 | section | *The prime regular functions* | `regular-primes.tex` |
| C.2 | section | *Two-way transducers* | `2dfa.tex` |
| C.2.1 | subsection | *Continuity* | `2dfa.tex` |
| C.2.2 | subsection | *Closure under composition* | `2dfa.tex` |
| C.2.3 | subsection | *Decidability of equivalence* | `2dfa.tex` |
| C.2.4 | subsection | *Decomposition into prime functions* | `2dfa.tex` |
| C.3 | section | *Streaming string transducers* | `sst.tex` |
| C.3.1 | subsection | *Equivalence with regular functions* | `sst.tex` |
| C.4 | section | *Logic* | `logic.tex` |
| C.4.1 | subsection | *Monadic second-order logic* | `logic.tex` |
| C.4.2 | subsection | *Rational functions in terms of logic* | `logic.tex` |
| C.4.3 | subsection | *Regular functions in terms of logic* | `logic.tex` |
| C.4.4 | subsection | *The first-order fragment* | `logic.tex` |
| C.5 | section | *Combinators* | `combinators.tex` |
| C.5.1 | subsection | *Regular terms* | `combinators.tex` |
| D.1 | section | *For-transducers* | `polyregular-for.tex` |
| D.1.1 | subsection | *Equivalence with polyregular functions* | `polyregular-for.tex` |
| D.2 | section | *Pebble transducers* | `polyregular-pebble.tex` |
| D.2.1 | subsection | *Continuity* | `polyregular-pebble.tex` |
| D.2.2 | subsection | *Equivalence with for-transducers* | `polyregular-pebble.tex` |
