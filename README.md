This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

A Lean 4 formalisation of the numbered results of the book `main.pdf`
(*Transducers*, M. Bojańczyk).  `THEOREMS.md` indexes every numbered result
together with its Lean name, its file and its current status.  The exercises of
the book are not numbered results; those that are formalised are indexed
separately, in `EXERCISES.md`.  `FORMALISATION.md` is a short prose companion
addressed to a reader of the book: what is formalised, what the conventions are,
what had to be corrected, and what is left out.

The results of the book are referred to by their LaTeX labels
(Theorem `thm:decidable-equivalence-regular`) rather than by their numbers,
which change when the sources are edited; `LABELS.md` explains the convention
and lists the labels.  The correspondence is checked by Lean in
`RequestProject/Labels.lean`, which declares, for every formalised result, an
alias whose Lean name is the label of the result together with an assertion
recording whether it is proved outright.

`tools/` holds the scripts that keep this bookkeeping honest:
`tools/tex_numbering.py` reads the label-to-number dictionary of the book out of
`main.aux` and can check the number column of `LABELS.md` against it;
`tools/relabel.py` finds (and, with `--fix`, rewrites) any place where a result
of the book is still named by its number; `tools/gen_labels.py --check`
verifies `RequestProject/Labels.lean` against `LABELS.md`, `THEOREMS.md` and
`EXERCISES.md`, with `--emit LABEL` printing the boilerplate for a new entry;
`tools/decl_files.py --check` verifies the `File` column of the index of
`THEOREMS.md` against the files that actually declare the named declarations;
and `tools/print_axioms.sh` runs `#print axioms` on every alias of
`RequestProject/Labels.lean` and reports any that depends on `sorryAx` or on an
axiom other than `propext`, `Classical.choice`, `Quot.sound`.  The first three
expect the LaTeX sources of the book, and `main.aux` in particular, in the
parent directory; pass `--book DIR` if they are elsewhere.  `lake build` is run
from this directory (`transducer-lean/`), which is the root of the Lean
package.

Structure of the sources (`RequestProject.lean` imports everything):

```
RequestProject/
  Common.lean   Common/        -- shared notions and auxiliary lemmas
  PartA.lean    PartA/         -- Part A: Mealy machines
  PartB.lean    PartB/         -- Part B: rational relations and functions
  PartC.lean    PartC/         -- Part C: regular functions
  PartD.lean    PartD/         -- Part D: polyregular functions
  Exercises.lean Exercises/    -- the exercises of the book (indexed in `EXERCISES.md`)
  Labels.lean                  -- the results of the book indexed by their LaTeX labels
  Main.lean                    -- global options used by the project
```

Each part directory has a roll-up file of the same name that imports its
contents.  Inside a part, the definitions and the statements of the numbered
results are in `Statements.lean` (for Part B, in `RationalStatements.lean` and
`WeightedStatements.lean`); the other files contain the constructions used in
their proofs.  A few results are stated elsewhere because they are proved from
the contents of `Statements.lean`: in Part D, the five results of Section
*Pebble transducers* that speak about the string representation of
configurations are in `PartD/PebReach.lean`, `PartD/ChildGraphFor.lean` and
`PartD/CGFor.lean`.  `THEOREMS.md` gives the file of every result.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
