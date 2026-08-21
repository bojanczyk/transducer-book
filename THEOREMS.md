# Theorems of *Transducers* (M. Bojańczyk) — formal statements

This project contains Lean 4 statements of the theorems, lemmas, corollaries and
claims of the book `main.pdf`, together with the definitions needed to state
them.  Everything lives in the namespace `Transducers`.

All the results of **Part A** are proved, including the Krohn-Rhodes
Theorem A.2.2, Lemma A.2.5 and both implications of Theorem A.2.8.  The
statements of Parts B, C and D are still `sorry`.

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
| `PartB/Atomize.lean`, `PartB/OutLang.lean`, `PartB/EpsElim.lean`, `PartB/RatComp.lean`, `PartB/RatCont.lean`, `PartB/HomComplement.lean`, `PartB/LenNormalForm.lean`, `PartB/MealyChar.lean`, `PartB/Typing.lean`, `PartB/SeqChar.lean` | the constructions used in the proofs of Part B (see the list at the end of the Part B section below) |
| `PartB/RationalStatements.lean` | Sections B.1–B.2: rational relations, rational functions, bimachines |
| `PartB/WeightedStatements.lean` | Sections B.3–B.4: weighted automata, machine independent characterisations |
| `PartC/Statements.lean` | Sections C.1–C.3: regular functions, two-way transducers, streaming string transducers |
| `PartC/MSO.lean` | Section C.4: monadic second-order logic, relabellings, transductions, the first-order fragment |
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
  rather than a relation).  Undecidability (Theorem B.1.6) is
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
| Theorem B.1.6 (undecidable equivalence) | `Transducers.rationalRel_equivalence_undecidable` | statement only |
| Claim B.1.7 (complement of a homomorphism) | `Transducers.hom_complement_rational` | proved (explicit four-state automaton, `HomComplement.lean`) |
| Definition B.2.1 (rational function) | `Transducers.IsRationalFun` | — |
| Definition B.2.2 (bimachine) | `Transducers.Bimachine`, `Transducers.IsBimachine` | — |
| Theorem B.2.3 (rational = unambiguous = bimachine) | `Transducers.rational_iff_unambiguous_iff_bimachine` | statement only |
| Lemma B.2.4 (elimination of ε-transitions) | `Transducers.epsilon_elimination` | proved (`EpsElim.lean`, using the regularity of the outputs on a fixed input, `OutLang.lean`) |
| Lemma B.2.5 (uniformisation) | `Transducers.uniformisation` | statement only |
| Theorem B.2.6 (decomposition into primes) | `Transducers.rational_iff_prime_composition` | statement only |
| Theorem B.2.7 (Mealy machines inside rational functions) | `Transducers.rational_isMealy_iff` | proved (from Theorem B.4.1 and Theorem B.1.5) |
| Definition B.3.1 (semiring) | Mathlib's `Semiring` | — |
| Definition B.3.2 (weighted automaton) | `Transducers.LabAut.wEval`, `Transducers.IsWeighted` | — |
| Theorem B.3.3 (equivalence over ℚ) | `Transducers.weighted_equivalence_decidable` | statement only |
| Theorem B.3.4 (equivalence of rational functions) | `Transducers.rationalFun_equivalence_decidable` | statement only |
| Lemma B.3.5 (pre-composition) | `Transducers.weighted_precomp_rational` | statement only |
| Theorem B.3.6 (characterisation of rationality) | `Transducers.rational_iff_weighted_precomp` | statement only |
| Theorem B.3.7 (zeroness) | `Transducers.weighted_zeroness_decidable` | statement only |
| Theorem B.4.1 (characterisation of Mealy machines) | `Transducers.isMealy_iff` | proved (`MealyChar.lean`) |
| Theorem B.4.2 (deciding the Mealy fragment) | `Transducers.rationalFun_isMealy_decidable` | statement only |
| Lemma B.4.3 (deciding length preservation) | `Transducers.rationalFun_lengthPreserving_decidable` | statement only |
| Claim B.4.4 (typings) | `Transducers.lengthPreserving_iff_typing` | proved (`Typing.lean`) |
| Lemma B.4.5 (length-preserving normal form) | `Transducers.lengthPreserving_rational_normal_form` | proved (`LenNormalForm.lean`) |
| Theorem B.4.6 (sequential functions) | `Transducers.isSequential_iff` | proved (`SeqChar.lean`); the statement of the book needs the extra condition `f [] = []` |
| Definition B.4.7 (left distance) | `Transducers.leftDist` | — |
| Theorem B.4.8 (subsequential functions) | `Transducers.isSubsequential_iff` | statement only |
| Claims B.4.9–B.4.12 | not formalised (internal steps of the proof of Theorem B.4.8) | — |
| Theorem B.4.13 (rational functions) | `Transducers.isRationalFun_iff` | statement only |

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

### Part C: Regular functions

| Book | Lean |
| --- | --- |
| Definition C.0.14 (regular functions) | `Transducers.IsRegularFun`, `Transducers.RegularFam` |
| Theorem C.1.1 (continuity, composition) | `Transducers.regular_continuous`, `Transducers.regular_comp` |
| Lemma C.1.2 (reversal, duplication) | `Transducers.reverse_duplicate_continuous` |
| Lemma C.1.3 (map lifting) | `Transducers.mapLift_continuous` |
| Theorem C.1.4 (decidable equivalence) | `Transducers.regular_equivalence_decidable` |
| Definition C.2.1 (two-way transducer) | `Transducers.TwoWay`, `Transducers.IsTwoWay` |
| Theorem C.2.2 (continuity) | `Transducers.twoWay_continuous` |
| Lemmas C.2.3, C.2.4, C.2.12 | not formalised (configuration-graph encodings used inside proofs) |
| Theorem C.2.5 (composition) | `Transducers.twoWay_comp` |
| Lemma C.2.6 (pre-composition with Mealy machines) | `Transducers.twoWay_precomp_mealy` |
| Corollary C.2.7 (pre-composition with rational functions) | `Transducers.twoWay_precomp_rational` |
| Corollary C.2.8 (two-way ⊆ regular) | `Transducers.twoWay_isRegular` |
| Theorem C.2.9 (two-way = regular) | `Transducers.twoWay_iff_regular` |
| Lemma C.2.10 (closure properties) | `Transducers.regular_closure_properties` |
| Claim C.2.11 (disjoint sums) | `Transducers.sum_of_regular` |
| Definition C.3.1 (sst) | `Transducers.SST`, `Transducers.IsSST` |
| Theorem C.3.2 (sst = regular) | `Transducers.sst_iff_regular` |
| Theorem C.4.1 (mso = regular languages) | `Transducers.regular_iff_msoDefinable` |
| Lemma C.4.2 (formulas with free variables) | `Transducers.mso_annotated_regular` |
| Definition C.4.3 (mso relabelling) | `Transducers.MSORelabelling`, `Transducers.IsMSORelabelling` |
| Theorem C.4.4 (rational = mso relabelling) | `Transducers.rational_iff_msoRelabelling` |
| Claim C.4.5 | not formalised (internal step of the proof of Theorem C.4.4) |
| Claim C.4.6 (annotated relabellings) | `Transducers.msoRelabelling_annotation_regular` |
| Definition C.4.7 (mso transduction) | `Transducers.MSOTransduction`, `Transducers.IsMSOTransduction` |
| Theorem C.4.8 (mso transductions = regular) | `Transducers.msoTransduction_iff_regular` |
| Lemma C.4.9 | not formalised (normalisation of the type τ inside the proof of Theorem C.4.8) |
| Lemma C.4.10 (formulas via rational functions) | `Transducers.mso_formulas_via_rational` |
| Theorem C.4.11 (first-order = aperiodic) | `Transducers.foDefinable_iff_aperiodic_dfa` |
| Definition C.4.12 (k-types) | `Transducers.tp` |
| Lemma C.4.13 (types and formulas) | `Transducers.tp_eq_iff_fo_equiv` |
| Claim C.4.14 | not formalised (internal step of the proof of Lemma C.4.13) |
| Lemma C.4.15 (properties of types) | `Transducers.tp_properties` |
| Theorem C.4.16 (first-order relabellings) | `Transducers.foRelabelling_iff_aperiodicBimachine` |
| Theorem C.4.17 (first-order transductions) | `Transducers.foTransduction_iff_prime_composition` |

### Part D: Polyregular functions

| Book | Lean |
| --- | --- |
| Definition D.0.18 (polyregular functions) | `Transducers.IsPolyregular`, `Transducers.markedSquare` |
| Theorem D.0.19 (continuity) | `Transducers.polyregular_continuous` |
| For-transducers (Section D.1) | `Transducers.ForProg`, `Transducers.IsForTransducer` |
| Theorem D.1.1 (polyregular = for-transducers) | `Transducers.polyregular_iff_forTransducer` |
| Definition D.1.2 (prenex form) | `Transducers.ForProg.PrenexForm` |
| Lemma D.1.3 (prenex normal form) | `Transducers.forTransducer_prenex` |
| Lemma D.1.4 (composition) | `Transducers.forTransducer_comp` |
| Pebble transducers (Section D.2) | `Transducers.Pebble`, `Transducers.IsPebbleTransducer` |
| Theorem D.2.1 (continuity) | `Transducers.pebble_continuous` |
| Lemma D.2.2, Claim D.2.3, Lemma D.2.5, Claims D.2.6, D.2.7 | not formalised (configuration encodings used inside proofs) |
| Theorem D.2.4 (pebble = for-transducers) | `Transducers.pebble_iff_forTransducer` |

## Status

All statements compile.  Part A is proved in full; the proofs of Parts B, C and
D are `sorry`.  Exercises and examples of the book are not included.
