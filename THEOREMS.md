# Theorems of *Transducers* (M. Bojańczyk) — formal statements

This project contains Lean 4 statements of the theorems, lemmas, corollaries and
claims of the book `main.pdf`, together with the definitions needed to state
them.  Everything lives in the namespace `Transducers`.

All the results of **Part A** are proved, including the Krohn-Rhodes
Theorem A.2.2, Lemma A.2.5 and both implications of Theorem A.2.8.  Parts B, C
and D are partly proved; the status of every result is recorded in the tables
below.

## Layout

The files are grouped by part of the book.  Each part has a directory and a
roll-up file of the same name that imports everything in it, and
`RequestProject.lean` imports all the parts.  Inside a part, the definitions and
the statements of the numbered results are in `Statements.lean` (for Part B, in
`RationalStatements.lean` and `WeightedStatements.lean`), and the remaining
files contain the constructions used in their proofs.

```
RequestProject.lean            -- imports everything
RequestProject/
  Common.lean   Common/        -- shared notions and auxiliary lemmas
  PartA.lean    PartA/         -- Part A: Mealy machines
  PartB.lean    PartB/         -- Part B: rational relations and functions
  PartC.lean    PartC/         -- Part C: regular functions
  PartD.lean    PartD/         -- Part D: polyregular functions
  Main.lean                    -- global options used by the project
```

| File | Contents |
| --- | --- |
| `Common/Basic.lean` | continuity, prefix/length preservation, aperiodicity, map lifting, left distance, closure under composition |
| `Common/Aux.lean` | auxiliary lemmas on lists and on iterating a function on a finite set |
| `Common/RegularAux.lean` | regularity of the auxiliary languages used in Part B |
| `PartA/MealyBasic.lean` | Mealy machines: definitions, runs, state transformations, products, the associated dfa |
| `PartA/PrimeClosure.lean` | closure properties of compositions of prime Mealy machines (pairing the output with the input) |
| `PartA/MapLift.lean` | the map lifting: its description position by position, and Lemma A.2.4 |
| `PartA/StateTrans.lean` | the state transformation transducer of a pre-automaton and the proof of Lemma A.2.5 (the induction of the Krohn-Rhodes Theorem) |
| `PartA/FlipFlopClosure.lean` | closure properties of compositions of flip-flop Mealy machines (the flip-flop analogues of `PrimeClosure.lean` and Lemma A.2.4) |
| `PartA/StateTransAperiodic.lean` | the aperiodic case of the Krohn-Rhodes construction: condition (*) is inherited by the smaller pre-automata, and all the machines are flip-flops |
| `PartA/Statements.lean` | Part A: Mealy machines |
| `PartB/LabAut.lean` | automata with labelled transitions, nfas with output, rational relations and functions |
| `PartB/Atomize.lean`, `PartB/OutLang.lean`, `PartB/EpsElim.lean`, `PartB/RatComp.lean`, `PartB/RatCont.lean`, `PartB/HomComplement.lean`, `PartB/LenNormalForm.lean`, `PartB/MealyChar.lean`, `PartB/Typing.lean`, `PartB/SeqChar.lean`, `PartB/Unambig.lean`, `PartB/Uniform.lean`, `PartB/Bimachine.lean`, `PartB/RatBimach.lean`, `PartB/PrimeRat.lean`, `PartB/BimachPrime.lean` | the constructions used in the proofs of Part B (see the list at the end of the Part B section below) |
| `PartB/Codes.lean` | finite descriptions (codes) of nfas with output, and the formalisation of (un)decidability statements |
| `PartB/PCPRed.lean` | the Post correspondence problem and the reduction proving Theorem B.1.6 |
| `PartB/PathComb.lean` | combinatorics of paths: splitting at a visited state, pigeonhole extraction of a short loop, replacement by a simple path |
| `PartB/LenDec.lean` | the decision procedure for Lemma B.4.3 and its correctness and computability |
| `PartB/RationalStatements.lean` | Sections B.1–B.2: rational relations, rational functions, bimachines |
| `PartB/WeightedNF.lean`, `PartB/WeightedLinRep.lean`, `PartB/WeightedPrecomp.lean`, `PartB/WeightedRegular.lean`, `PartB/WeightedZero.lean` | normal forms and linear representations of weighted automata, the proofs of Lemma B.3.5 and Theorem B.3.6, and Schützenberger's zeroness criterion |
| `PartB/WeightedStatements.lean` | Sections B.3–B.4: weighted automata, machine independent characterisations |
| `PartC/ContAux.lean` | continuity: closure under composition, letter-to-letter maps, reversal, duplication, and the map lifting (Lemma C.1.3) |
| `PartC/TwoDFA.lean` | deterministic two-way automata and Shepherdson's Theorem (their languages are regular) |
| `PartC/TwoWayCont.lean` | two-way transducers (Definition C.2.1) and their continuity (Theorem C.2.2) |
| `PartC/TwoWayPrecomp.lean` | pre-composition of a two-way transducer with a Mealy machine (Lemma C.2.6), via the Krohn-Rhodes Theorem: the reversible case, the flip-flop case, and pre-composition with reversal |
| `PartC/KTypes.lean` | `k`-types of strings (Definition C.4.12) and their properties (Lemma C.4.15) |
| `PartC/Statements.lean` | Sections C.1–C.3: regular functions, two-way transducers, streaming string transducers |
| `PartC/MSO.lean` | Section C.4: monadic second-order logic, relabellings, transductions, the first-order fragment |
| `PartD/MarkedSquare.lean` | marked squaring and its continuity |
| `PartD/Statements.lean` | Part D: polyregular functions, for-transducers, pebble transducers |

## Conventions

* Strings are `List A`, languages are `Language A = Set (List A)`, regularity is
  Mathlib's `Language.IsRegular`.
* Finiteness of an alphabet or a state space is an instance argument
  `[Finite A]` or an existential `∃ (Q : Type) (_ : Finite Q), …`.
* **Decidability statements.**  "Problem `P` is decidable" is formalised as
  `DecidableUnderPromise promise P`: there is a `Computable` `Bool`-valued
  function that answers `P` correctly on all finite descriptions (codes)
  satisfying the promise (for instance, that the code describes a function
  rather than a relation).  Since a code has only finitely many transitions it
  reads only finitely many letters of the ambient alphabet `ℕ`, so the promise
  `CodeFunctional` asks for a total function on the strings over the alphabet of
  the code; `Transducers.not_codeTotalFunctional` shows that asking for totality
  on all of `ℕ*` would be vacuous.  Undecidability (Theorem B.1.6) is
  `¬ ComputablePred …`.  Theorem A.1.2 is stated instead in the equivalent
  concrete form of a finite check on inputs of bounded length.
* **Compositions of prime functions** are expressed with `CompClosure P`, the
  closure of a family `P` of string-to-string functions under composition.

## Index

### Introduction

| Book | Lean |
| --- | --- |
| Definition .0.1 (continuity) | `Transducers.Continuous` |

### Part A: Mealy machines

| Book | Lean | Status |
| --- | --- | --- |
| Definition A.1.1 (Mealy machine) | `Transducers.Mealy`, `Transducers.Mealy.eval`, `Transducers.IsMealy` | — |
| Theorem A.1.2 (decidable equivalence) | `Transducers.mealy_equiv_iff_bounded` | proved |
| Theorem A.1.3 (composition) | `Transducers.mealy_comp` | proved |
| Theorem A.1.4 (continuity) | `Transducers.mealy_continuous` | proved |
| Definition A.2.1 (prime Mealy machines) | `Transducers.Mealy.Reversible`, `Transducers.Mealy.FlipFlop`, `Transducers.PrimeMealyFam` | — |
| Theorem A.2.2 (Krohn–Rhodes) | `Transducers.krohn_rhodes` | proved |
| Definition A.2.3 (map lifting) | `Transducers.mapLift` | — |
| Lemma A.2.4 (map lifting of a decomposition) | `Transducers.mapLift_prime_decomposition` | proved (in `MapLift.lean`) |
| Lemma A.2.5 (state transformation transducer) | `Transducers.stateTransTransducer_prime_decomposition` | proved (in `StateTrans.lean`): induction basis `stateTransTransducer_prime_of_reversible`, induction step by the tripartite decomposition into `a`-blocks (`krStages_eq`, `krStages_compClosure`) |
| Lemma A.2.6 (reversible machines compose) | `Transducers.reversible_comp` | proved |
| Definition A.2.7 (aperiodic) | `Transducers.Aperiodic` | — |
| Theorem A.2.8 (aperiodic = flip-flops) | `Transducers.aperiodic_iff_flipflop_composition` | proved ("⇐" by `flipflop_composition_aperiodic`, "⇒" by `krohn_rhodes_flipFlop`, which runs the construction of `StateTrans.lean` inside the class of flip-flops, using that only realisable state transformations occur, see `StateTransAperiodic.lean`) |
| Claim A.2.9 (pumping form of aperiodicity) | `Transducers.aperiodic_iff_pumping` | proved |
| Lemma A.2.10 (Myhill–Nerode) | `Transducers.myhill_nerode_mealy` | proved |
| Lemma A.2.11 (condition (*)) | `Transducers.aperiodic_iff_transStabilises` | proved |

Two definitions of Part A had to be corrected in order to make the corresponding
statements true; both corrections are documented in the docstrings.

* `Aperiodic` (Definition A.2.7) asks that the sequence of last letters of
  `f (u vⁿ w)` is eventually constant *as an element of `Option B`*.  Requiring
  an actual output letter would make the notion unsatisfiable, since for
  `u = v = w = ε` the output of a letter-to-letter function is empty.
* `deriv` (the derivative used in Lemma A.2.10) removes the `|w|` output letters
  produced while reading `w`: `f⁽ʷ⁾(v) = drop |w| (f (w v))`.  With the literal
  reading `f⁽ʷ⁾(v) = f (w v)` even the identity function would have infinitely
  many derivatives, and Lemma A.2.10 would be false.

Auxiliary results proved along the way and reusable elsewhere:
`Transducers.Mealy.compose` (product of Mealy machines) and
`Transducers.Mealy.dfaComp` (the dfa reading the output of a Mealy machine),
`Transducers.derivMealy` (the minimal machine of a function),
`Transducers.compClosure_zipInput` and `Transducers.compClosure_liftSnd`
(a decomposition into primes can keep a copy of the input in its output),
`Transducers.outputMealy` (recovering the output of a machine from the state
transformations of the prefixes of the input).

### Part B: Rational functions

| Book | Lean | Status |
| --- | --- | --- |
| Definition B.1.1 (nfa with output) | `Transducers.NFAO` (via `Transducers.LabAut`) | — |
| Definition B.1.2 (rational relation) | `Transducers.IsRationalRel` | — |
| Theorem B.1.4 (composition) | `Transducers.rationalRel_comp` | proved (product automaton in `RatComp.lean`, on the atomic normal form of `Atomize.lean`) |
| Theorem B.1.5 (continuity) | `Transducers.rationalRel_continuous` | proved (ε-automaton running a dfa on the output, `RatCont.lean`) |
| Theorem B.1.6 (undecidable equivalence) | `Transducers.rationalRel_equivalence_undecidable` | proved from an explicit hypothesis that the Post correspondence problem is undecidable (reduction in `PCPRed.lean`) |
| Claim B.1.7 (complement of a homomorphism) | `Transducers.hom_complement_rational` | proved (explicit four-state automaton, `HomComplement.lean`) |
| Definition B.2.1 (rational function) | `Transducers.IsRationalFun` | — |
| Definition B.2.2 (bimachine) | `Transducers.Bimachine`, `Transducers.IsBimachine` | — |
| Theorem B.2.3 (rational = unambiguous = bimachine) | `Transducers.rational_iff_unambiguous_iff_bimachine` | proved (unambiguity by the least accepting run, `Unambig.lean` and `Uniform.lean`; bimachine → rational in `Bimachine.lean`, rational → bimachine in `RatBimach.lean`) |
| Lemma B.2.4 (elimination of ε-transitions) | `Transducers.epsilon_elimination` | proved (`EpsElim.lean`, using the regularity of the outputs on a fixed input, `OutLang.lean`) |
| Lemma B.2.5 (uniformisation) | `Transducers.uniformisation` | proved (`Uniform.lean`, from the ε-free normal form of Lemma B.2.4 and the unambiguisation of `Unambig.lean`) |
| Theorem B.2.6 (decomposition into primes) | `Transducers.rational_iff_prime_composition` | proved (`PrimeRat.lean` and `BimachPrime.lean`, from Theorem B.2.3 and the Krohn–Rhodes Theorem) |
| Theorem B.2.7 (Mealy machines inside rational functions) | `Transducers.rational_isMealy_iff` | proved (from Theorem B.4.1 and Theorem B.1.5) |
| Definition B.3.1 (semiring) | Mathlib's `Semiring` | — |
| Definition B.3.2 (weighted automaton) | `Transducers.LabAut.wEval`, `Transducers.IsWeighted` | — |
| Theorem B.3.3 (equivalence over ℚ) | `Transducers.weighted_equivalence_decidable` | statement only |
| Theorem B.3.4 (equivalence of rational functions) | `Transducers.rationalFun_equivalence_decidable` | statement only |
| Lemma B.3.5 (pre-composition) | `Transducers.weighted_precomp_rational` | proved (`WeightedNF.lean`, `WeightedLinRep.lean` and `WeightedPrecomp.lean`) |
| Theorem B.3.6 (characterisation of rationality) | `Transducers.rational_iff_weighted_precomp` | proved ("⇒" is Lemma B.3.5, "⇐" in `WeightedRegular.lean`) |
| Theorem B.3.7 (zeroness) | `Transducers.weighted_zeroness_decidable` | statement only |
| Theorem B.4.1 (characterisation of Mealy machines) | `Transducers.isMealy_iff` | proved (`MealyChar.lean`) |
| Theorem B.4.2 (deciding the Mealy fragment) | `Transducers.rationalFun_isMealy_decidable` | statement only |
| Lemma B.4.3 (deciding length preservation) | `Transducers.rationalFun_lengthPreserving_decidable` | proved (bounded enumeration of transition sequences, `PathComb.lean` and `LenDec.lean`) |
| Claim B.4.4 (typings) | `Transducers.lengthPreserving_iff_typing` | proved (`Typing.lean`) |
| Lemma B.4.5 (length-preserving normal form) | `Transducers.lengthPreserving_rational_normal_form` | proved (`LenNormalForm.lean`) |
| Theorem B.4.6 (sequential functions) | `Transducers.isSequential_iff` | proved (`SeqChar.lean`); the statement of the book needs the extra condition `f [] = []` |
| Definition B.4.7 (left distance) | `Transducers.leftDist` | — |
| Theorem B.4.8 (subsequential functions) | `Transducers.isSubsequential_iff` | proved (`SubseqDef.lean`, `SubseqAlpha.lean`, `SubseqState.lean`, `SubseqBound.lean`, `SubseqChar.lean`) |
| Claims B.4.9–B.4.12 | not formalised as numbered results; they appear as the internal steps `delay_bound`, `key_drop`, `incr_congr` and `exists_deletion_bound` of the proof of Theorem B.4.8 | — |
| Theorem B.4.13 (rational functions) | `Transducers.isRationalFun_iff` | proved (`RatIndex.lean`, `SubseqRat.lean`, `RatAnnot.lean`) |

Supporting files for Part B: `Atomize.lean` (every nfa with output is
equivalent to one whose transitions read and write at most one letter),
`RatComp.lean` (Theorem B.1.4), `RatCont.lean` (Theorem B.1.5),
`HomComplement.lean` (Claim B.1.7), `MealyChar.lean` (Theorem B.4.1),
`Typing.lean` (Claim B.4.4), `LenNormalForm.lean` (Lemma B.4.5: the type
`τ q = |output| − |input|` of a state and the automaton whose states carry the
output that is produced but not yet emitted, or emitted but not yet produced),
`SeqChar.lean` (Theorem B.4.6: the canonical sequential transducer, whose
states are the Myhill–Nerode classes of the length-modulo and suffix
languages), `RegularAux.lean` (regularity of the auxiliary languages),
`OutLang.lean` (for a fixed input, the set of outputs is a regular language over
the output alphabet) and `EpsElim.lean` (Lemma B.2.4).

The files added for Theorem B.4.8 are:

* `Lcp.lean` — the longest common prefix `lcp2` of two strings and its relation
  to the left distance of Definition B.4.7.
* `SubseqDef.lean` — subsequential transducers, the bounded variation property,
  and the easy implication (a subsequential function is continuous and has
  bounded variation).
* `SubseqAlpha.lean` — the *non-branching part* `alpha D w`: the longest common
  prefix of the outputs of the short extensions of `w`, and the delay bound
  saying that these outputs exceed it by a bounded number of letters.
* `SubseqState.lean` — the Myhill–Nerode state of `w` (the left quotients of the
  domain and of the suffix and length-modulo languages) and the proof that it
  determines the branching part, the increment of the non-branching part caused
  by one more letter, and the end-of-input output.
* `SubseqBound.lean` — the pumping argument bounding the deletions in the
  non-branching part: a loop cannot shorten it, hence all but the last `M`
  letters of `alpha D w` are permanent.
* `SubseqChar.lean` — the transducer itself: it outputs `alpha D w` with a delay
  of `M` letters, kept in a buffer that is flushed when it exceeds `2 * M`.

The files added for Theorem B.4.13 are:

* `RatIndex.lean` — the equivalence relation `BoundedVarRel` (`w₁ ∼ w₂` if the
  left distances `‖f (w w₁), f (w w₂)‖` are bounded uniformly in `w`), the proof
  that it is an equivalence relation and a left congruence, and the easy
  implication: for a rational function, presented as a bimachine, two strings
  giving the same state of the suffix automaton are equivalent, so the relation
  has finite index.
* `SubseqRat.lean` — the graph of a subsequential function is a rational
  relation (a subsequential transducer is turned into an nfa with output with
  one extra final state).
* `RatAnnot.lean` — the converse implication.  Every letter of the input is
  annotated with the equivalence class of the suffix that follows it; the
  annotation is a rational relation, the correctly annotated strings form a
  regular language, and the partial function sending a correctly annotated
  string to the value of `f` on the underlying string is continuous and has
  bounded variation, hence subsequential by Theorem B.4.8.  Composing the two
  rational relations gives the graph of `f`.

The files added for Lemma B.3.5 and Theorem B.3.6 are:

* `WeightedNF.lean` — normal forms for weighted automata.  The value of a
  weighted automaton is a sum over *lists of transitions*, so the empty run is
  counted once even if several initial states are final; `initCopy` replaces the
  initial states by copies that are not final and adds one state accounting for
  the empty run, so that at most one state is both initial and final.  `atom`
  splits every transition into a chain of transitions reading one letter each
  (the states of the chain are the pairs consisting of a transition and the part
  of its input that has not been read yet), and `restrict` removes the states
  that lie on no accepting run.  All three constructions leave the computed
  function unchanged, because the accepting runs are in weight-preserving
  bijection.  For an automaton with only useful states and finitely many
  accepting runs, the paths with a fixed source, target and input string form a
  finite set.
* `WeightedLinRep.lean` — the *linear representation* of a weighted automaton in
  the above normal form: the matrix `mu b` of a letter collects the weights of
  the paths reading `b` whose transitions, except the last one, read nothing,
  and the vector `beta` the weights of the accepting paths reading nothing.
  Splitting a run at the first letter gives `wEval M v = ∑_{q ∈ init} (mu v₁ ⋯
  mu v_k *ᵥ beta) q`, and `exists_linRep` produces such a representation for an
  arbitrary weighted automaton.
* `WeightedPrecomp.lean` — Lemma B.3.5: the product of a bimachine for the
  rational function `f` (Theorem B.2.3) with the linear representation of the
  weighted automaton for `h`.  Its states are triples consisting of the state of
  the prefix automaton at the current gap, the *guessed* state of the suffix
  automaton at that gap, and a state of the linear representation; the
  transition reading a letter carries the matrix entry of the output block
  produced at the previous gap.  The guesses are determined by the input, so the
  sum over the accepting runs is exactly `h (f w)`.
* `WeightedRegular.lean` — the implication "⇐" of Theorem B.3.6: over the
  semiring of languages the map `v ↦ {v}` is computed by a weighted automaton,
  so the hypothesis gives a weighted automaton over that semiring computing
  `w ↦ {f w}`.  A concatenation of languages that is nonempty and contained in a
  singleton has singleton factors, so keeping the transitions labelled by a
  singleton language turns this automaton into an nfa with output computing
  `f`.

The files added for Theorems B.2.3, B.2.5 and B.2.6 are:

* `Unambig.lean` — unambiguisation: the runs of an ε-free nfa with output over a
  fixed input are ranked by the *key* `runKey`, a number whose base-`K` digits
  are the ranks of the transitions; the automaton `unambAut` follows a run while
  keeping track of the set of states reachable by a run with a smaller key, and
  accepts exactly the least accepting run.  Hence every ε-free nfa with output
  whose relation is total contains an unambiguous one with the same domain
  (`exists_unambiguous_of_epsFree`).
* `Uniform.lean` — Lemma B.2.5: choosing one output string in each language of
  the extended ε-free automaton of Lemma B.2.4 gives an ordinary nfa with output
  contained in the relation, which is unambiguised as above; the same argument
  gives an unambiguous ε-free automaton for every rational function
  (`exists_unambiguous_aut_of_rationalFun`).
* `Bimachine.lean` — the definition of a bimachine (moved out of
  `RationalStatements.lean`) and the implication “bimachine ⇒ rational”: an nfa
  with output that guesses the state of the suffix automaton at the next gap and
  verifies the guess step by step.
* `RatBimach.lean` — the implication “rational ⇒ bimachine”: the prefix automaton
  is the reachability subset construction, the suffix automaton the
  co-reachability one; unambiguity gives that at every gap the intersection of
  the two sets is a singleton, namely the state of the unique accepting run, and
  the output at a gap is the output of the transition connecting the two
  neighbouring gap states.
* `PrimeRat.lean` — the family `PrimeRationalFam` of prime rational functions
  (moved out of `RationalStatements.lean`) and the easy implication of
  Theorem B.2.6: Mealy machines, homomorphisms and the separator function are
  read directly as nfas with output, a right-to-left Mealy machine is a
  bimachine, and rational functions compose.
* `BimachPrime.lean` — the hard implication of Theorem B.2.6: a bimachine is the
  composition of `w ↦ w#`, a right-to-left Mealy machine annotating the
  positions with the states of the suffix automaton, a left-to-right Mealy
  machine annotating them with the states of the prefix automaton, and a
  homomorphism; the two Mealy machines are decomposed by the Krohn–Rhodes
  Theorem, reversal turning a decomposition into a decomposition of the
  right-to-left variant.

### Part C: Regular functions

| Book | Lean | Status |
| --- | --- | --- |
| Definition C.0.14 (regular functions) | `Transducers.IsRegularFun`, `Transducers.RegularFam` | — |
| Theorem C.1.1 (continuity, composition) | `Transducers.regular_continuous`, `Transducers.regular_comp` | proved (continuity by induction on the decomposition into primes, `ContAux.lean`) |
| Lemma C.1.2 (reversal, duplication) | `Transducers.reverse_duplicate_continuous` | proved (`ContAux.lean`) |
| Lemma C.1.3 (map lifting) | `Transducers.mapLift_continuous` | proved (Myhill–Nerode, `ContAux.lean`) |
| Theorem C.1.4 (decidable equivalence) | `Transducers.regular_equivalence_decidable` | statement only |
| Definition C.2.1 (two-way transducer) | `Transducers.TwoWay`, `Transducers.IsTwoWay` | — |
| Theorem C.2.2 (continuity) | `Transducers.twoWay_continuous` | proved (`TwoWayCont.lean`, from Shepherdson's Theorem in `TwoDFA.lean`) |
| Lemmas C.2.3, C.2.4, C.2.12 | not formalised (configuration-graph encodings used inside proofs) | — |
| Theorem C.2.5 (composition) | `Transducers.twoWay_comp` | statement only |
| Lemma C.2.6 (pre-composition with Mealy machines) | `Transducers.twoWay_precomp_mealy` | proved |
| Corollary C.2.7 (pre-composition with rational functions) | `Transducers.twoWay_precomp_rational` | proved (`TwoWayHom.lean`, `TwoWayBlock.lean`, `TwoWayErase.lean` and `TwoWayRat.lean`, from Theorem B.2.6 and Lemma C.2.6) |
| Corollary C.2.8 (two-way ⊆ regular) | `Transducers.twoWay_isRegular` | statement only |
| Theorem C.2.9 (two-way = regular) | `Transducers.twoWay_iff_regular` | statement only |
| Lemma C.2.10 (closure properties) | `Transducers.regular_closure_properties` | statement only |
| Claim C.2.11 (disjoint sums) | `Transducers.sum_of_regular` | statement only |
| Definition C.3.1 (sst) | `Transducers.SST`, `Transducers.IsSST` | — |
| Theorem C.3.2 (sst = regular) | `Transducers.sst_iff_regular` | statement only |
| Theorem C.4.1 (mso = regular languages) | `Transducers.regular_iff_msoDefinable` | statement only |
| Lemma C.4.2 (formulas with free variables) | `Transducers.mso_annotated_regular` | statement only |
| Definition C.4.3 (mso relabelling) | `Transducers.MSORelabelling`, `Transducers.IsMSORelabelling` | — |
| Theorem C.4.4 (rational = mso relabelling) | `Transducers.rational_iff_msoRelabelling` | statement only |
| Claim C.4.5 | not formalised (internal step of the proof of Theorem C.4.4) | — |
| Claim C.4.6 (annotated relabellings) | `Transducers.msoRelabelling_annotation_regular` | statement only |
| Definition C.4.7 (mso transduction) | `Transducers.MSOTransduction`, `Transducers.IsMSOTransduction` | — |
| Theorem C.4.8 (mso transductions = regular) | `Transducers.msoTransduction_iff_regular` | statement only |
| Lemma C.4.9 | not formalised (normalisation of the type τ inside the proof of Theorem C.4.8) | — |
| Lemma C.4.10 (formulas via rational functions) | `Transducers.mso_formulas_via_rational` | statement only |
| Theorem C.4.11 (first-order = aperiodic) | `Transducers.foDefinable_iff_aperiodic_dfa` | statement only |
| Definition C.4.12 (k-types) | `Transducers.tp` | — |
| Lemma C.4.13 (types and formulas) | `Transducers.tp_eq_iff_fo_equiv` | statement only |
| Claim C.4.14 | not formalised (internal step of the proof of Lemma C.4.13) | — |
| Lemma C.4.15 (properties of types) | `Transducers.tp_properties` | proved (`KTypes.lean`) |
| Theorem C.4.16 (first-order relabellings) | `Transducers.foRelabelling_iff_aperiodicBimachine` | statement only |
| Theorem C.4.17 (first-order transductions) | `Transducers.foTransduction_iff_prime_composition` | statement only |

Supporting files for Part C: `ContAux.lean` (continuity is closed under
composition; letter-to-letter maps, reversal, duplication and the map lifting of
a continuous function are continuous), `TwoDFA.lean` (deterministic two-way
automata and Shepherdson's Theorem: their languages are regular, proved with the
Myhill–Nerode theorem and the profile of a prefix), `TwoWayCont.lean` (the
definitions of two-way transducers, and the two-way automaton obtained by
running a deterministic automaton on the output) and `KTypes.lean` (`k`-types
and Lemma C.4.15).

The files added for Corollary C.2.7 are:

* `TwoWayHom.lean` — a simulation principle for two-way transducers, and
  pre-composition with appending a fixed letter to the input.
* `TwoWayBlock.lean` — pre-composition with a homomorphism all of whose blocks
  have the same positive length `L`: the simulating transducer stores the offset
  of the head of the simulated transducer inside the current block, a step of
  the simulated transducer that stays inside a block being implemented by a step
  to the right followed by a step to the left.
* `TwoWayErase.lean` — pre-composition with an *erasing* homomorphism, i.e. one
  that maps every letter to at most one letter; such a homomorphism is a
  `List.filterMap`.  The simulating transducer keeps its head at the position
  immediately to the left of the next non-erased letter, and finds the letter of
  the image to the left of the head by a scan to the left followed by a return.
* `TwoWayRat.lean` — Corollary C.2.7: an arbitrary homomorphism is a
  block homomorphism whose blocks are padded with a fresh letter, followed by
  the erasing homomorphism that deletes the padding; with Lemma C.2.6, with
  pre-composition with reversal and with appending a letter, this covers all the
  prime rational functions of Theorem B.2.6, and the general case follows by
  induction on the composition.

### Part D: Polyregular functions

| Book | Lean | Status |
| --- | --- | --- |
| Definition D.0.18 (polyregular functions) | `Transducers.IsPolyregular`, `Transducers.markedSquare` | — |
| Theorem D.0.19 (continuity) | `Transducers.polyregular_continuous` | proved (continuity of marked squaring, `MarkedSquare.lean`) |
| For-transducers (Section D.1) | `Transducers.ForProg`, `Transducers.IsForTransducer` | — |
| Theorem D.1.1 (polyregular = for-transducers) | `Transducers.polyregular_iff_forTransducer` | statement only |
| Definition D.1.2 (prenex form) | `Transducers.ForProg.PrenexForm` | — |
| Lemma D.1.3 (prenex normal form) | `Transducers.forTransducer_prenex` | statement only |
| Lemma D.1.4 (composition) | `Transducers.forTransducer_comp` | statement only |
| Pebble transducers (Section D.2) | `Transducers.Pebble`, `Transducers.IsPebbleTransducer` | — |
| Theorem D.2.1 (continuity) | `Transducers.pebble_continuous` | statement only |
| Lemma D.2.2, Claim D.2.3, Lemma D.2.5, Claims D.2.6, D.2.7 | not formalised (configuration encodings used inside proofs) | — |
| Theorem D.2.4 (pebble = for-transducers) | `Transducers.pebble_iff_forTransducer` | statement only |

Supporting file for Part D: `MarkedSquare.lean` (marked squaring and the
right-to-left automaton showing that it is continuous).

## Status

All statements compile.  Part A is proved in full.  In Part B, eighteen of the
numbered results are proved (B.1.4, B.1.5, B.1.7, B.2.3, B.2.4, B.2.5, B.2.6,
B.2.7, B.3.5, B.3.6, B.4.1, B.4.3, B.4.4, B.4.5, B.4.6, B.4.8, B.4.13), and
B.1.6 is proved from an explicit hypothesis stating that the Post correspondence
problem is undecidable.  The ones that are still open are the four remaining
decidability statements (B.3.3, B.3.4, B.3.7, B.4.2); each of them needs a
*total computable* decision procedure on codes of weighted automata over ℚ
(B.3.3, B.3.7) or on codes of rational functions (B.3.4, B.4.2).  The
mathematical content of B.3.3 and B.3.7 — Schützenberger's bound: a function
computed by a weighted automaton over a field vanishes identically as soon as it
vanishes on all inputs of length at most the number of states — is proved in
`PartB/WeightedZero.lean` (`weighted_zero_of_short`, `weighted_eq_of_short`);
what is missing is the effective version of that bound and the computability of
evaluating a coded weighted automaton.  The latter is a substantial obstacle in
this setting: Mathlib's `Primrec`/`Computable` API provides no arithmetic on `ℤ`
or `ℚ`, so a decision procedure manipulating rational weights would have to
develop that API first.
In Part C,
Theorem C.1.1, Lemmas C.1.2 and C.1.3,
Theorem C.2.2, Lemma C.2.6, Corollary C.2.7 and Lemma C.4.15 are proved.  In Part D, Theorem D.0.19 is
proved.  The remaining results are statements only (`sorry`).  Exercises and
examples of the book are not included.
