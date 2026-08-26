# Exercises of *Transducers* (M. Bojańczyk) — formal statements

This file is to the exercises of the book what `THEOREMS.md` is to its numbered
results.  An exercise is not a numbered result of the main text, so it does not
appear in the tables of `THEOREMS.md`; it is listed here instead, together with
the name of the Lean declaration that formalises it and its status.

As everywhere else in this project, an exercise is identified by its LaTeX
label, in backticks, as in Exercise `exer:reverse-continuous`, and not by its
number, which changes whenever the sources are edited.  Only some exercises
carry a `\label`; an exercise that carries none is identified here by the
chapter file it belongs to and by its position among the exercises of that
chapter, and it gets a descriptive Lean name.  Every *labelled* exercise also
gets an alias in `RequestProject/Labels.lean`, whose Lean name is its label,
followed by the `assert_no_sorry` (or `assert_uses_sorry`) that records its
status; so the statuses below are checked by Lean.

Where an exercise is formalised by several declarations, they are all listed in
the same row, and the label alias of the first one is followed by `#2`, `#3`, …
for the others.

## Layout

```
RequestProject/
  Exercises.lean   Exercises/   -- the exercises, one pair of files per chapter
    Intro.lean                  -- the exercises of the introduction (intro.tex)
    IntroAux.lean               -- the auxiliary facts their solutions take for granted
```

| File | Contents |
| --- | --- |
| `Exercises/Intro.lean` | the eleven exercises of the introduction: continuity of reversal, duplication, squaring, the factorial function and factorial powers; continuity for functions with finitely many output values and the necessity of that assumption; the middle letter function; the distance given by the number of states needed to separate two strings, the discreteness of the induced topology, and the identification of continuity with uniform continuity |
| `Exercises/IntroAux.lean` | the elementary facts about dfas and regular languages that those solutions take for granted: transporting a dfa to the state set `Fin n`, complementing a dfa, shifting its acceptance condition by a suffix, finiteness of the set of dfas over a finite alphabet, regularity of singletons, of subsingletons and of finite unions, the run of a dfa on a power `wⁿ`, and the eventual stabilisation of the iterates of a self-map of a finite set |

## Conventions

The conventions are those of `THEOREMS.md`: strings are `List A`, languages are
`Language A = Set (List A)`, regularity is Mathlib's `Language.IsRegular`, and
continuity in the sense of Definition `def:continuity` is
`Transducers.Continuous`.  The exercises live in the namespace
`Transducers.Exercises`; the names below are relative to it.  Powers of a
string are `Transducers.npow`.

`Transducers.Exercises.strDist` is the distance of Exercise `ex:distance` and
`Transducers.Exercises.strMetric` is the `MetricSpace` structure it defines; the
last two exercises are stated for that structure, installed as a local
instance, so that `_root_.Continuous` and `UniformContinuous` there are
Mathlib's topological notions (inside those files, plain `Continuous` is
`Transducers.Continuous`, the continuity of Definition `def:continuity`).

## Index

### Introduction (`intro.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:reverse-continuous` (continuity of reversal) | `reverse_continuous` | proved |
| Exercise `exer:duplication-continuous` (continuity of duplication `w ↦ ww`) | `duplication_continuous` | proved |
| Exercise `exer:squaring-continuous` (continuity of squaring `w ↦ w^{\|w\|}`) | `squaring_continuous` | proved |
| Exercise `exer:factorial-continuous` (continuity of `w ↦ w^{\|w\|!}`) | `factorial_continuous` | proved |
| Exercise `exer:factorial-power-continuous` (continuity of `w ↦ w^{g(\|w\|)!}` for `g` non-decreasing) | `factorial_power_continuous` | proved |
| Exercise `ex:continuity-for-finite-images` (finitely many output values: continuity is regularity of the fibres) | `continuous_iff_regular_fibers` | proved |
| Exercise `exer:finite-images-assumption-necessary` (that assumption is necessary) | `exists_regular_fibers_not_continuous` | proved |
| Exercise `exer:middle-letter-not-continuous` (the middle letter function is not continuous) | `middleLetter_not_continuous` | proved |
| Exercise `ex:distance` (the distance given by the number of states needed to separate two strings) | `strDist`, `strDist_isMetric`, `strDist_ultrametric`, `strMetric` | proved |
| Exercise `exer:all-functions-continuous-for-metric` (all functions are continuous for that distance) | `strDist_all_continuous` | proved |
| Exercise `exer:continuous-iff-uniformly-continuous` (continuity = uniform continuity for that distance) | `continuous_iff_uniformContinuous` | proved |

All eleven exercises of the introduction carry a `\label` in the sources, so
all eleven are aliased in `RequestProject/Labels.lean`.

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

### The Krohn-Rhodes Decomposition Theorem (`krohn-rhodes.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:flip-flop-from-sequential-composition` (a flip-flop machine is a composition of two-state flip-flops) | `Transducers.flipflop_twoState_decomposition` (with `Transducers.TwoStateFlipFlopFam`) | proved |
| Exercise `exer:delay-not-flip-flop-composition` (the delay function is not a composition of reversible machines) | `Transducers.delay_not_reversible_composition` | proved |
| Exercise `exer:alternating-not-flip-flop-composition` (the alternating function is not a composition of flip-flops) | `Transducers.alternating_not_flipflop_composition` (with `Transducers.alternating`) | proved |
| Exercise `exer:invertible-mealy-is-reversible` (invertible and reversible are incomparable) | `Transducers.invertible_reversible_independent` (with `Transducers.swapPrev`, `Transducers.constOut`) | proved |
| Exercise `ex:map-lifting-continuous` (the map lifting of a continuous function is continuous) | `Transducers.mapLift_continuous_of_continuous` | proved (an instance of Lemma `lem:map-lifting-continuous` of the main text, `Transducers.mapLift_continuous`) |

## Notes on the statements

* **`exer:reverse-continuous` and `exer:duplication-continuous`.**  These two
  exercises are also the two halves of Lemma
  `lem:reversal-duplication-continuous` of the main text, which is
  formalised in `PartC/ContAux.lean` (`Transducers.continuous_reverse` and
  `Transducers.continuous_dup`).  Rather than restating the proof, the two
  exercises are deduced from that lemma.
* **`exer:squaring-continuous`.**  Formalised with the transformation monoid of
  a dfa recognising the output language in place of the abstract monoid of the
  author's solution: the state of the automaton for the inverse image is a pair
  `(δ_w, t ↦ t^{|w|})`.
* **`exer:factorial-continuous`.**  Deduced from
  `exer:factorial-power-continuous` for `g = id`.  The update rule that the
  author's solution gives for the third component ("multiply the previous value
  coordinatewise with the new value of the second coordinate") computes
  `m ↦ m^{|w|! + |w|}` and not `m ↦ m^{|w|!}`; the correct rule composes the two
  components, `ψ' = φ' ∘ ψ`.  This is recorded in the docstring of
  `factorial_continuous`.
* **`ex:continuity-for-finite-images`.**  Stated with the condition quantified
  over *all* output strings, which is equivalent since the inverse image of a
  value that is not attained is empty, hence regular.  The "if" direction is
  the author's argument, with the inverse image of a regular language written
  as the finite union of the inverse images of the attained values that belong
  to it (and not, as the solution puts it, with the regular language written as
  a finite union of singletons, which is false for an infinite language).
* **`exer:finite-images-assumption-necessary`.**  This exercise asks to show
  that an assumption is necessary, which is not by itself a mathematical
  statement; what is formalised is the concrete claim the author's solution
  establishes: over an alphabet with two letters there is an *injective*
  function — so one all of whose fibres are regular, being empty or singletons
  — that is not continuous.  The witness is the one of the solution: mark the
  input with a letter recording whether its middle letter is `a`, and copy the
  input after the mark.
* **`exer:middle-letter-not-continuous`.**  The middle letter function is
  `middleLetter`, and "the alphabet has at least two letters" is the hypothesis
  `a ≠ b` for two letters `a b : A`.  The non-regularity of the language of the
  strings of odd length whose middle letter is `a` is proved with Mathlib's
  pumping lemma, as in the author's solution.
* **`ex:distance`.**  "Show that this is indeed a distance" is formalised as
  `strDist_isMetric`, the conjunction of the four axioms of a distance, and the
  `MetricSpace` structure `strMetric` that they define; `strDist_ultrametric`
  is the stronger inequality with `max` in place of `+` that the author's
  solution proves.  The minimal number of states is `sepStates`, an `sInf` over
  the numbers of states of the dfas with state set `Fin n` that accept the one
  string and not the other; it is `0` when there is no such dfa, which happens
  exactly for two equal strings, so `strDist` follows the book in treating that
  case separately.
* **`exer:all-functions-continuous-for-metric`.**  Formalised as topological
  continuity for the metric `strMetric` on both sides, and proved through the
  discreteness of the induced topology, which is the topological description
  given at the end of the author's solution.
* **`exer:continuous-iff-uniformly-continuous`.**  Both alphabets are assumed
  finite, as they are everywhere in the book: the author's solution counts the
  automata with at most a given number of states over a given alphabet, and
  that number is finite only for a finite alphabet.  Uniform continuity is
  Mathlib's `UniformContinuous` for `strMetric`.

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

All eleven exercises of the introduction are proved, with no `sorry` anywhere
in `Exercises/`, and each of the declarations above depends only on `propext`,
`Classical.choice`, `Quot.sound` (checked with `#print axioms`).  No other
chapter of the book has its exercises formalised yet.


All twelve exercises of Part A are proved, with no `sorry`; each depends only on
`propext`, `Classical.choice` and `Quot.sound`, which is what the
`assert_no_sorry` lines of `RequestProject/Labels.lean` record for the aliases
named after the labels.
