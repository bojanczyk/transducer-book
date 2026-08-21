This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

A Lean 4 formalisation of the numbered results of the book `main.pdf`
(*Transducers*, M. Bojańczyk).  `THEOREMS.md` indexes every numbered result
together with its Lean name and its current status.

Structure of the sources (`RequestProject.lean` imports everything):

```
RequestProject/
  Common.lean   Common/        -- shared notions and auxiliary lemmas
  PartA.lean    PartA/         -- Part A: Mealy machines
  PartB.lean    PartB/         -- Part B: rational relations and functions
  PartC.lean    PartC/         -- Part C: regular functions
  PartD.lean    PartD/         -- Part D: polyregular functions
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
