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
    PartBC.lean                 -- the exercises of Parts B and C
    PartBCAux.lean              -- the auxiliary facts their solutions take for granted
    PartBCPCP.lean              -- the reduction from the Post correspondence problem
    PartBCUnary.lean            -- bimachines over a one-letter input alphabet
    KrohnRhodes.lean            -- further exercises of krohn-rhodes.tex
    MyhillNerode.lean           -- the exercises of myhill-nerode.tex
    RegularPrimes.lean          -- further exercises of regular-primes.tex
    TwoDFAEx.lean               -- the exercises of 2dfa.tex
    TwoDFALoop.lean             -- loop elimination for two-way transducers
    SSTAux.lean                 -- the auxiliary facts of the sst exercises
    SST.lean                    -- the exercises of sst.tex
    SSTPoly.lean                -- copyful ssts and polynomial automata
```

| File | Contents |
| --- | --- |
| `Exercises/Intro.lean` | the eleven exercises of the introduction: continuity of reversal, duplication, squaring, the factorial function and factorial powers; continuity for functions with finitely many output values and the necessity of that assumption; the middle letter function; the distance given by the number of states needed to separate two strings, the discreteness of the induced topology, and the identification of continuity with uniform continuity |
| `Exercises/IntroAux.lean` | the elementary facts about dfas and regular languages that those solutions take for granted: transporting a dfa to the state set `Fin n`, complementing a dfa, shifting its acceptance condition by a suffix, finiteness of the set of dfas over a finite alphabet, regularity of singletons, of subsingletons and of finite unions, the run of a dfa on a power `wⁿ`, and the eventual stabilisation of the iterates of a self-map of a finite set |
| `Exercises/PartBC.lean` | the exercises of Parts B and C that are formalised: six exercises on rational relations (the domain and the range, the inputs with at most one output, closure under intersection, the undecidability of a nonempty intersection, the size of the outputs, the recognisable subsets of `A* x B*`), eight on rational functions (the three examples as bimachines, the two functions that are not rational, the undecidability of the collision problem, the graph of a rational function over a one-letter input alphabet, the function that becomes rational after every rational function into a one-letter alphabet, two families of ideals, the ideals whose functions all have finite range, the one-sided inverse of a surjective rational function), the exercise on two-letter alphabets for the prime regular functions, and the exercise on Mealy machines as restricted mso relabellings |
| `Exercises/PartBCPCP.lean` | the reduction from the Post correspondence problem that the solution to `exer:rational-relations-intersection-undecidable` asks for: the two-state automaton computing the graph of a homomorphism on nonempty inputs, its code, the relation it describes, and the computability of the reduction |
| `Exercises/PartBCAux.lean` | the auxiliary facts those solutions take for granted: the symmetry of rational relations in input and output (so that the inverse of a rational relation is rational), the small regular languages given by explicit dfas that guess-and-check is applied to, the non-regularity, by the pumping lemma, of the languages the counterexamples produce (`bⁿcⁿ`, the balanced strings, `aⁱbʲ` with `j ≤ i`, and the squares `uu`), bounds on the length of the output of a run, the dfa that marks the position where a Mealy machine outputs a given letter, the encoding of an arbitrary finite alphabet by blocks over a two-letter one, and the two directions of the identification of the regular languages with the languages recognised by a homomorphism into a finite monoid |
| `Exercises/KrohnRhodes.lean` | the two exercises of `krohn-rhodes.tex` on the first-letter function: its decomposition as a flip-flop followed by a letter-to-letter map, and the fact that it is not a composition of reversible machines |
| `Exercises/MyhillNerode.lean` | the exercises of `myhill-nerode.tex` that are formalised: the uniqueness of the minimal sequential transducer, the failure of uniqueness for subsequential transducers, and the failure of uniqueness for bimachines |
| `Exercises/RegularPrimes.lean` | the exercise of `regular-primes.tex` on the semiring of weighted functions: a regular function that is not obtained by precomposing a weighted function |
| `Exercises/TwoDFAEx.lean` | the exercise of `2dfa.tex` on Boolean combinations: the languages of deterministic two-way automata are closed under complement, union and intersection |
| `Exercises/TwoDFALoop.lean` | loop elimination: the set of inputs on which a deterministic two-way transducer terminates is a regular language |
| `Exercises/SSTAux.lean` | the auxiliary facts the sst exercises take for granted |
| `Exercises/SST.lean` | the exercises of `sst.tex`: sorting by an sst, the continuity of the functions of copyful ssts, the exponential bound on their output length and its attainment, the failure of closure under composition, and the two polynomial automata (single and doubly exponential) |
| `Exercises/SSTPoly.lean` | the reduction of equivalence of copyful ssts to equivalence of polynomial automata |
| `Exercises/PartBCUnary.lean` | bimachines over a one-letter input alphabet, used by the solution to `exer:rational-one-letter-input`: the eventual periodicity of the runs of the prefix and of the suffix automaton, the output of the bimachine as the concatenation of the pieces of its gaps, and the resulting form `x yᵏ z` of the output on the inputs of a fixed length modulo the period |

The file `Exercises/PartA.lean` holds the twelve exercises of Part A.  An
earlier note here said that it was built but could not be imported together
with the rest of the project, because several of its auxiliary declarations
had names that already occurred in the main development (`Transducers.dfaMealy`,
`Transducers.annot`, `Transducers.bits`, `Transducers.Reach`); that clash has
since been resolved — the file now reuses `Transducers.dfaMealy` of
`PartC/FOMealy.lean` and keeps the other three to itself — so
`RequestProject/Exercises.lean` imports it like every other exercise file, and
its exercises are indexed below, in *Mealy machines* and in *The Krohn-Rhodes
Decomposition Theorem*.

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

### Rational relations (`rational-relations.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:regular-languages-for-rational-relations` (the domain and the range of a rational relation are regular) | `rationalRel_domain_isRegular`, `rationalRel_range_isRegular` | proved |
| Exercise `exer:non-regular-languages-for-rational-relations` (the inputs with at most one output need not be regular) | `exists_rationalRel_atMostOneOutput_not_isRegular` | proved |
| Exercise `exer:rational-relations-not-closed-under-intersection` (rational relations are not closed under intersection) | `exists_rationalRel_inter_not_rationalRel` | proved |
| Exercise `exer:rational-relations-intersection-undecidable` (nonemptiness of the intersection is undecidable) | `rationalRel_intersection_undecidable` | proved from the undecidability of the Post correspondence problem |
| Exercise `exer:rational-output-size` (finitely many outputs ⟺ affine bound on the output length) | `rationalRel_finiteOutputs_iff_affine` | proved |
| Exercise `ex:recognisable-relations` (the recognisable subsets of `A* × B*`) | `IsRecognisableRel`, `isRecognisableRel_iff_finite_union` | proved |

### Rational functions (`rational-functions.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:examples-of-rational-fun` (three functions as bimachines and as rational functions) | `isBimachine_isRationalFun_evenLength`, `isBimachine_isRationalFun_swapFirstLast`, `isBimachine_isRationalFun_upToLastHash` | proved |
| Exercise `exer:non-rational` (the first half of the input, and duplication, are not rational) | `not_isRationalFun_firstHalf`, `not_isRationalFun_duplicate` | proved |
| Exercise `exer:decide-unambiguous` (unambiguity of an nfa is decidable) | — | not formalised |
| Exercise `exer:decide-rational-colision` (equal outputs, outputs of equal length) | `rationalFun_collision_undecidable` (item (a) only) | proved from an explicit hypothesis |
| Exercise `exer:rational-one-letter-input` (rational functions on a one-letter input alphabet) | `rationalFun_unary_graph` | proved |
| Exercise `exer:function-that-is-not-rational` (not rational, yet rational after every rational function into `1*`) | `exists_not_isRationalFun_unary_compositions_rational` | proved from the hypothesis that reversal is not rational |
| Exercise `exer:some-ideals` (two families of ideals of rational functions) | `IsIdeal`, `isIdeal_rangeAtMost`, `isIdeal_outputsPoly` | proved |
| Exercise `exer:finite-range-ideals` (the ideals whose functions have finite range) | `ideal_mem_of_ncard_le`, `finite_range_ideal_classification` | proved |
| Exercise `exer:full-ideal` (the ideal of all rational functions) | — | not formalised |
| Exercise `exer:polynomial-ideals` (the ideals of polynomial growth) | — | not formalised |
| Exercise `exer:all-ideals` (the classification of the ideals) | — | not formalised |
| Exercise `exer:decide-same-ideal` (equality of the generated ideals is decidable) | — | not formalised |
| Exercise `exer:surjective-rational-function` (a surjective rational function has a rational one-sided inverse) | `exists_rationalFun_leftInverse` | proved |
| Exercise `exer:rational-injectivity-decidable` (injectivity is decidable) | — | not formalised |
| Exercise `exer:rational-composition-finiteness-undecidable` (finiteness of the iterates is undecidable) | — | not formalised |

### Regular functions (`regular-primes.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:two-letter-alphabet-suffices` (a two-letter alphabet suffices for map reverse and map duplicate) | `RegularFam2`, `isRegularFun_iff_compClosure2` | proved |

### Logic (`logic.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:mealy-as-restricted-mso-relabelling` (Mealy machines are the restricted mso relabellings) | `RestrictedRelabelling`, `isMealy_iff_restrictedRelabelling` | proved |

Every exercise of these four chapters carries a `\label` in the sources, so
every formalised one is aliased in `RequestProject/Labels.lean`.

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
  `lem:reversal-duplication-continuous` of the main text, which is
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
`Classical.choice`, `Quot.sound` (checked with `#print axioms`).  (The last
sentence of this paragraph used to read "no other chapter of the book has its
exercises formalised yet"; that was true when it was written, and the chapters
formalised since are indexed above and described in the sections below.)


All twelve exercises of Part A are proved, with no `sorry`; each depends only on
`propext`, `Classical.choice` and `Quot.sound`, which is what the
`assert_no_sorry` lines of `RequestProject/Labels.lean` record for the aliases
named after the labels.
* **`exer:regular-languages-for-rational-relations`.**  The domain is the
  inverse image of `B*`, which is regular by the continuity of rational
  relations, Theorem `thm:continuity-rational-relations`; the range is the
  domain of the inverse relation, which is rational because rational relations
  are symmetric in input and output (`isRationalRel_inv`, in
  `Exercises/PartBCAux.lean`).
* **`exer:non-regular-languages-for-rational-relations`.**  The relation is the
  author's, over the input alphabet `Bool` and the one-letter output alphabet
  `Unit`: the union of "keep only the `a`s" and "keep only the `b`s".  Its
  rationality is guess and check (`isRationalRel_of_regular_nivat`), the
  annotation recording in each position which of the two functions is applied.
* **`exer:rational-relations-not-closed-under-intersection`.**  The two
  relations are the author's, `{(aⁿ, bⁿcᵐ)}` and `{(aⁿ, bᵐcⁿ)}`; their
  intersection is not rational because its range `{bⁿcⁿ}` is not regular, by the
  second item of Exercise `exer:regular-languages-for-rational-relations`.
* **`exer:rational-relations-intersection-undecidable`.**  Undecidability is
  stated as it is for the numbered results of Part B: a decision problem about
  rational relations is a problem about their codes (`Transducers.RelCode`),
  and the undecidability of the Post correspondence problem itself is taken as
  an explicit hypothesis, exactly as in Theorem
  `thm:undecidable-equivalence-rational-relations`.  The reduction is the
  author's, with the two-state automaton he describes.
* **`exer:rational-output-size`.**  For the direction that the author proves by
  shortening runs by hand, the formalisation reuses the same analysis as it is
  already carried out for Lemma `lemma:eliminate-epsilon-transitions`: a
  rational relation with finitely many outputs is computed by an nfa with
  output in which every transition of an accepting run reads exactly one letter
  (and a run on the empty input is a single transition), which gives the affine
  bound directly.
* **`ex:recognisable-relations`.**  `IsRecognisableRel` is the book's Definition
  `def:rational-recognisable-subsets` specialised to the monoid `A* × B*`; the
  general notion, for an arbitrary monoid, is still not formalised, and this
  exercise is the only place that needs it.  Recognisability is taken in the
  form the author's solution uses -- the inverse image of a subset of a finite
  monoid under a monoid homomorphism -- and a homomorphism out of a free monoid
  is given by a plain function together with the two equations it satisfies, so
  that no monoid instance has to be put on `List A × List B`.  The finite union
  is indexed by `Fin n`.  Both directions are the author's; the identification
  of the regular languages with the languages recognised by a homomorphism into
  a finite monoid, which the solution recalls as standard, is proved in
  `Exercises/PartBCAux.lean` (`isRegular_of_wordHom` and
  `exists_wordHom_of_isRegular`, the latter through the transition monoid of a
  dfa).
* **`exer:examples-of-rational-fun`.**  Each of the three functions is shown to
  be computed by the bimachine of the author's solution and, by Theorem
  `thm:bimachines`, to be rational; the two claims are the two halves of a
  single conjunction.  For item (c) the convention of the solution is used: on
  an input without `#`, every letter is replaced by `#`.
* **`exer:non-rational`.**  Both items are the author's arguments, over the
  two-letter alphabet `Bool`: the first half of the input is not continuous, and
  the range of duplication is the language of squares, which is not regular.
* **`exer:decide-rational-colision`.**  Only item (a) is formalised, the
  undecidability of the existence of an input on which the two rational
  functions give the same output.  As for the numbered results of Part B, the
  problem is stated about codes `RelCode` under the promise `CodeFunctional`,
  and the undecidability of the Post correspondence problem is the explicit
  hypothesis `hPCP`.  The reduction is the author's, including the point that
  the two functions have to be made to differ on the empty input.  Item (b),
  the decidable one, is not formalised: it goes through the semilinearity of
  Parikh images of regular languages, which the project does not have.
* **`exer:rational-one-letter-input`.**  The one-letter input alphabet is
  `Unit`, to which any one-letter alphabet is isomorphic; the graph is stated as
  a set of pairs and the finite union is indexed by `Fin n`; the repetition
  `yᵏ` is `(List.replicate k y).flatten`, since strings are lists.  The output
  alphabet is assumed finite, as everywhere in the book, because Theorem
  `thm:bimachines` is used.  The proof is the author's, through a bimachine and
  the eventual periodicity of its two automata over a one-letter alphabet; the
  analysis of the gaps is in `Exercises/PartBCUnary.lean`
  (`Unary.eval_replicate_period`), and the inputs shorter than
  `2 * lam + per` are the members of the union with `β = 0`.
* **`exer:function-that-is-not-rational`.**  That string reversal is not
  rational is Example `ex:string-reversal-not-rational` of the main text, which
  is not part of this formalisation (examples are not numbered results here);
  it is therefore carried as the explicit hypothesis `hrev` of the statement,
  and everything else the exercise asks for is proved: for a rational
  `g : B* → 1*`, the bimachine of `g` with its prefix and suffix automata
  swapped computes `g` on the reversed input, since it produces the same pieces
  of output in the opposite order.
* **`exer:some-ideals`.**  `IsIdeal` renders the book's `I = Rational · I ·
  Rational` as: every member of `I` is a rational function, and `I` is closed
  under pre- and post-composition with rational functions.  The other inclusion
  of the book's equality is automatic, since the identity is rational.  A class
  of functions is indexed by the pair of alphabets, as `RegularFam` is in the
  main text, and all alphabets are finite.  The two families of the exercise
  are `RangeAtMost k` (a range of at most `k` elements) and `OutputsPoly k`
  (the number of outputs on the inputs of length at most `n` is `O(n^k)`, in
  the explicit form `≤ C·(n+1)^k`).
* **`exer:finite-range-ideals`.**  The classification is stated as a
  disjunction: an ideal all of whose functions have a finite range either
  equals `RangeAtMost k` for some `k`, or equals `OutputsPoly 0`.  The
  hypothesis that every member has a finite range is the hypothesis `hfin` of
  the statement.  The empty ideal is covered by the first alternative with
  `k = 0`, since a function always has at least one output and `RangeAtMost 0`
  is empty too; `outputsPoly_zero_iff_finite_range` identifies `OutputsPoly 0`
  with the rational functions that have finitely many outputs, as the author
  does.  The key step, `ideal_mem_of_ncard_le`, is the author's factorisation
  argument.
* **`exer:surjective-rational-function`.**  The author's solution, with the
  Uniformisation Lemma `lem:uniformisation` in the form
  `exists_rationalFun_of_total_rel`.  The book writes the conclusion as
  `g · f = id` with composition from left to right, that is `f (g v) = v`.
* **`exer:two-letter-alphabet-suffices`.**  `RegularFam2` is Definition
  `def:regular-functions` with map reverse and map duplicate restricted to the
  alphabet `Bool + 1`.  The exercise is stated for functions between *finite*
  alphabets: the definition allows infinite input and output alphabets (only
  the intermediate ones must be finite), and over an infinite alphabet the
  prime functions cannot be simulated over a two-letter one.  This is recorded
  in the docstring.
* **`exer:mealy-as-restricted-mso-relabelling`.**  The three restrictions the
  exercise imposes on Definition `def:mso-relabeling` are the fields of
  `RestrictedRelabelling`: the output on the empty input is empty, each formula
  produces exactly one letter, and the formulas depend only on the prefix up to
  and including the current position.

## Exercises that are not formalised

The exercises listed as *not formalised* above are all of the same two kinds,
and each is left out rather than replaced by a statement the book does not
make.

* Decidability and undecidability of problems about rational relations and
  functions: `exer:decide-unambiguous`, item (b) of
  `exer:decide-rational-colision`, `exer:decide-same-ideal`,
  `exer:rational-injectivity-decidable`,
  `exer:rational-composition-finiteness-undecidable`.  In this project such a
  statement is about *codes* of automata (`Transducers.RelCode`) and about
  `ComputablePred`, and the corresponding reductions are not carried out.
* Statements resting on theory that the project does not have: the growth rates
  of regular languages, together with the pattern analysis that Exercise
  `exer:polynomial-image-growth-decidable` of Part A asks for, for the series
  of exercises on ideals that follows `exer:finite-range-ideals`:
  `exer:full-ideal`, `exer:polynomial-ideals`, `exer:all-ideals`.

## Status

All eleven exercises of the introduction, and the sixteen formalised exercises
of Parts B and C, are proved: there is no `sorry` in `Exercises/`, and each of
the declarations above depends only on `propext`, `Classical.choice`,
`Quot.sound` (checked with `#print axioms`, and by the `assert_no_sorry` that
follows every alias in `RequestProject/Labels.lean`).  Three statements carry
an assumption: `exer:function-that-is-not-rational`, which takes the
non-rationality of string reversal — an *example* of the main text, not a
numbered result — as an explicit hypothesis, and
`exer:rational-relations-intersection-undecidable` together with item (a) of
`exer:decide-rational-colision`, which take the undecidability of the Post
correspondence problem as an explicit hypothesis, as the numbered
undecidability results of the book do.

The exercises of the remaining chapters are not formalised.  Those of Part A
are in `Exercises/PartA.lean`, and are indexed above, in *Mealy machines* and
in *The Krohn-Rhodes Decomposition Theorem*; that file is imported by
`RequestProject/Exercises.lean` like every other exercise file.

Counted by rows of the index: thirty-nine exercises are formalised — eleven of
the introduction, twelve of Part A, sixteen of Parts B and C — and seven are
not, all seven of them in *Rational functions*.
Each of the thirty-nine has an alias in `RequestProject/Labels.lean` carrying
`assert_no_sorry`, and none of the seven has one, which is what makes this
index self-checking; `#print axioms` on all thirty-nine reports only `propext`,
`Classical.choice`, `Quot.sound`.
