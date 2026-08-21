/-
A formalisation of the numbered results of *Transducers* (M. Bojańczyk).

The project is organised as follows.

* `RequestProject/Common` — shared notions (continuity, prefix and length
  preservation, aperiodicity, the map lifting, closure under composition) and
  auxiliary lemmas about lists and regular languages.
* `RequestProject/PartA` — Part A: Mealy machines and the Krohn-Rhodes theorem.
* `RequestProject/PartB` — Part B: rational relations and rational functions,
  weighted automata and the machine independent characterisations.
* `RequestProject/PartC` — Part C: regular functions, two-way transducers,
  streaming string transducers and monadic second-order logic.
* `RequestProject/PartD` — Part D: polyregular functions, for-transducers and
  pebble transducers.

In each part, the file `Statements.lean` (for Part B, `RationalStatements.lean`
and `WeightedStatements.lean`) contains the definitions and the statements of
the numbered results; the remaining files contain the constructions used in
their proofs.  `THEOREMS.md` indexes every numbered result of the book together
with its Lean name and its current status.
-/
import RequestProject.Common
import RequestProject.PartA
import RequestProject.PartB
import RequestProject.PartC
import RequestProject.PartD
