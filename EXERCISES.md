# Exercises of *Transducers* (M. Bojańczyk) — formal statements

The exercises of the book are written in the LaTeX sources as
`\exer{statement}{solution}`, and the second argument is the author's own
solution.  The printed edition does not typeset the solutions, so they have
never been checked by anything; here each exercise is stated in Lean and proved,
following the author's solution unless the docstring of the declaration says
otherwise.

An exercise is not a numbered result of the book, so it does not belong in the
tables of `THEOREMS.md`; the exercises are indexed here instead, in the same
style.  As everywhere in this project, a result of the book is identified by its
LaTeX label rather than by its number: every exercise of Part A carries a
`\label`, and those labels are the ones used below.  The correspondence between
the labels and the Lean names is checked by Lean, in
`RequestProject/Labels.lean`, in the section *Exercises*: each labelled exercise
gets an alias whose Lean name is its label, followed by `assert_no_sorry`.

Everything lives in the namespace `Transducers`, in the file
`RequestProject/Exercises/PartA.lean` (rolled up by
`RequestProject/Exercises.lean`), one section per chapter, in the order in which
the book states the exercises.

## Index

### Mealy machines (`mealy.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:letter-to-letter-not-mealy` (a continuous letter-to-letter function that is not Mealy) | `Transducers.reverse_continuous_lengthPreserving_not_mealy` | proved |
| Exercise `exer:composition-needs-many-states` (a composition of `n` Mealy machines may need exponentially many states) | `Transducers.mealy_composition_state_blowup` (with `Transducers.MealyChain`) | proved |
| Exercise `exer:invertible` (invertibility is decidable) | `Transducers.mealy_invertible_iff`, `Transducers.decidableInvertible` (with `Transducers.Mealy.Invertible`, `Transducers.Mealy.AllReachable`) | proved |
| Exercise `exer:invertible-mealy-group` (a finitely generated group of invertible Mealy machines need not be finite) | `Transducers.exists_invertible_mealy_infinite_order` | proved |
| Exercise `exer:polynomial-image-growth-decidable` (polynomial growth of the image is decidable) | `Transducers.mealy_imageGrowth_polyBounded_iff`, `Transducers.decidableImageGrowthPolyBounded` (with `Transducers.imageGrowth`, `Transducers.PolyBounded`, `Transducers.Mealy.AmbiguousCycle`) | proved |
| Exercise `exer:regular-complete-mealy` (a regular-complete language under Mealy reductions exists) | `Transducers.lastLetterTrue_regularCompleteMealy` (with `Transducers.RegularCompleteMealy`, `Transducers.lastLetterTrue`) | proved |
| Exercise `exer:regular-complete-mealy-2` (deciding regular-completeness) | `Transducers.regularCompleteMealy_dfa_iff`, `Transducers.decidableRegularCompleteMealy` | proved |

### The Krohn-Rhodes Decomposition Theorem (`krohn-rhodes.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:flip-flop-from-sequential-composition` (a flip-flop machine is a composition of two-state flip-flops) | `Transducers.flipflop_twoState_decomposition` (with `Transducers.TwoStateFlipFlopFam`) | proved |
| Exercise `exer:delay-not-flip-flop-composition` (the delay function is not a composition of reversible machines) | `Transducers.delay_not_reversible_composition` | proved |
| Exercise `exer:alternating-not-flip-flop-composition` (the alternating function is not a composition of flip-flops) | `Transducers.alternating_not_flipflop_composition` (with `Transducers.alternating`) | proved |
| Exercise `exer:invertible-mealy-is-reversible` (invertible and reversible are incomparable) | `Transducers.invertible_reversible_independent` (with `Transducers.swapPrev`, `Transducers.constOut`) | proved |
| Exercise `ex:map-lifting-continuous` (the map lifting of a continuous function is continuous) | `Transducers.mapLift_continuous_of_continuous` | proved (an instance of Lemma `lem:map-lifting-continuous` of the main text, `Transducers.mapLift_continuous`) |

## How the exercises are stated

Some of the exercises are not mathematical statements as they stand — "give an
example of …", "is the generated subgroup necessarily finite?", "give an
algorithm which …".  For those, what is formalised is the concrete claim that
the author's own solution establishes; the choice is recorded in the docstring
of the declaration in each case.  In detail:

* `exer:letter-to-letter-not-mealy` asks for an example.  The formal statement
  is that the example of the solution — string reversal over an alphabet with
  two distinct letters — is continuous, letter-to-letter and not computed by a
  Mealy machine.  Its continuity is Lemma
  `nolabel:lem-reverse-and-duplicate-continuous` of the main text, which is
  reused, not restated.
* `exer:composition-needs-many-states` is stated as: for every `n` there is a
  composition of `n` Mealy machines with at most two states each that no Mealy
  machine with fewer than `2 ^ n` states computes.  The composition used is a
  binary counter rather than the author's sieve on the first `n` primes: in the
  author's construction the `i`-th machine has `pᵢ` states, so the lower bound
  `p₁ ⋯ pₙ` is exponential in the number of machines but not obviously in the
  number of their states without a bound on the primorial.  The lower-bound
  argument itself is the author's: the shortest input producing an output letter
  with all bits set has length `2 ⁿ` (resp. `p₁ ⋯ pₙ`).
* `exer:invertible` asks for a decision procedure.  It is formalised in two
  parts, as in the solution: the criterion (*) — in every state the output
  letters of the outgoing transitions depend bijectively on the input letter —
  and the resulting `Decidable` instance.  As in the solution, the criterion is
  stated for machines all of whose states are reachable.
* `exer:invertible-mealy-group` is a yes/no question.  The formalised statement
  is the answer of the solution, in its stronger form: there is a single
  invertible Mealy machine whose powers are pairwise distinct, so that the group
  it generates is infinite.  The machine is the author's — adding one to a
  binary number — with the bits written least significant first, so that the
  carry travels left to right and the machine has two states.
* `exer:polynomial-image-growth-decidable` asks for a decision procedure; again
  the criterion and the `Decidable` instance are both stated.  The criterion is
  the one of the solution, transported from the automaton of the output language
  to the machine itself: polynomial growth fails exactly when there are two
  cycles of the same length around a common reachable state that produce
  different outputs.
* `exer:regular-complete-mealy` asks for a language, and the formal statement is
  that the author's language — the nonempty binary strings whose last letter is
  `true` — is regular and regular-complete under Mealy reductions.
* `exer:regular-complete-mealy-2` asks for an algorithm, and the formalisation
  is the criterion (*) of the solution for a language given by a deterministic
  automaton, together with the resulting decidability.  The polynomial running
  time claimed in the solution (through the safety game between Prover and
  Refuter) is not formalised: the project has no model of running time, and the
  criterion is decided here by quantifying over the subsets of the state space.
* `exer:invertible-mealy-is-reversible` is a two-part yes/no question; the
  formalised statement is the answer of the solution — neither implication holds
  — witnessed by the two machines of the solution.
* The remaining exercises (`exer:flip-flop-from-sequential-composition`,
  `exer:delay-not-flip-flop-composition`,
  `exer:alternating-not-flip-flop-composition`, `ex:map-lifting-continuous`) are
  mathematical statements already, and are formalised literally.  Two notes:
  `exer:delay-not-flip-flop-composition` is about *reversible* machines, as its
  text says, although its label mentions flip-flops, and it needs the input
  alphabet to be nonempty (over the empty alphabet the delay function is the
  identity); and
  `exer:flip-flop-from-sequential-composition` is proved with one two-state
  machine per state of the given machine rather than per bit of a binary
  encoding of the states, since the exercise does not ask for a logarithmic
  number of machines.

## Status

All twelve exercises of Part A are proved, with no `sorry`; each depends only on
`propext`, `Classical.choice` and `Quot.sound`, which is what the
`assert_no_sorry` lines of `RequestProject/Labels.lean` record for the aliases
named after the labels.
