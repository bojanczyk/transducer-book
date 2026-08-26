This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

A Lean 4 formalisation of the numbered results of the book `main.pdf`
(*Transducers*, M. Bojańczyk).  `THEOREMS.md` indexes every numbered result
together with its Lean name and its current status.  The exercises of the book
are not numbered results; those that are formalised are indexed separately, in
`EXERCISES.md`.

The results of the book are referred to by their LaTeX labels
(Theorem `thm:decidable-equivalence-regular`) rather than by their numbers,
which change when the sources are edited; `LABELS.md` explains the convention
and lists the labels.  The correspondence is checked by Lean in
`RequestProject/Labels.lean`, which declares, for every formalised result, an
alias whose Lean name is the label of the result together with an assertion
recording whether it is proved outright.

`tools/` holds the three scripts that keep this bookkeeping honest:
`tools/tex_numbering.py` reads the label-to-number dictionary of the book out of
`main.aux` and can check the number column of `LABELS.md` against it;
`tools/relabel.py` finds (and, with `--fix`, rewrites) any place where a result
of the book is still named by its number; and `tools/gen_labels.py --check`
verifies `RequestProject/Labels.lean` against `LABELS.md`, `THEOREMS.md` and
`EXERCISES.md`, with `--emit LABEL` printing the boilerplate for a new entry.
All three expect the LaTeX sources of the book, and `main.aux` in particular, in
the parent directory; pass `--book DIR` if they are elsewhere.

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
their proofs.

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
