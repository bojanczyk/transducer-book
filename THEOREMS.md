# Theorems of *Transducers* (M. Bojańczyk) — formal statements

This project contains Lean 4 statements of the theorems, lemmas, corollaries and
claims of the book `main.pdf`, together with the definitions needed to state
them.  Everything lives in the namespace `Transducers`.

All the results of **Part A** are proved, including the Krohn-Rhodes
Theorem A.2.2, Lemma A.2.5 and both implications of Theorem A.2.8.  All the
results of **Part B** are proved as well; five of them (B.1.6, B.3.3, B.3.4,
B.3.7 and B.4.2) are proved from explicit hypotheses, which are the
undecidability of the Post correspondence problem and one effectivity
hypothesis about arithmetic on `ℚ` that Mathlib's computability API cannot yet
supply.  Parts C and D are partly proved; the status of every result is recorded
in the tables below.

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
| `PartB/UniformFun.lean` | uniformisation in the form of a function (`Transducers.exists_rationalFun_of_total_rel`): a total rational relation contains the graph of a rational function |
| `PartB/GuessCheck.lean` | "guess and check", one half of Nivat's theorem (`Transducers.isRationalRel_of_regular_nivat`): a regular language of annotated strings, read through one homomorphism and written through another, is a rational relation |
| `PartB/Codes.lean` | finite descriptions (codes) of nfas with output, and the formalisation of (un)decidability statements |
| `PartB/PCPRed.lean` | the Post correspondence problem and the reduction proving Theorem B.1.6 |
| `PartB/PathComb.lean` | combinatorics of paths: splitting at a visited state, pigeonhole extraction of a short loop, replacement by a simple path |
| `PartB/LenDec.lean` | the decision procedure for Lemma B.4.3 and its correctness and computability |
| `PartB/Effective.lean` | the effectivity hypothesis `EffectiveWeightedEvalEq` from which Theorems B.3.3, B.3.4, B.3.7 and B.4.2 are proved, and the statement `EffectiveWeightedBound` of the effective Schützenberger bound (which is *proved*, in `PartB/WeightedBound.lean`) |
| `PartB/WeightedBound.lean` | the effective Schützenberger bound: the useful states of the normalised automaton are covered by an explicit list, so the dimension of the linear representation, and hence the length bound `wcodeBound`, is a primitive recursive function of the code (`effectiveWeightedBound`) |
| `PartB/WCodes.lean` | codes of weighted automata over `ℚ` (`WCode`, `wcodeAut`, `wcodeEval`, `WCodeValid`) |
| `PartB/CodeAtom.lean`, `PartB/CodeMerge.lean`, `PartB/CodeAlpha.lean`, `PartB/CodeEps.lean`, `PartB/RunList.lean` | the letter-atomic normal form of a code, the alphabets of a code, its value on the empty input, and the enumeration of the runs of a letter-atomic code |
| `PartB/Iota.lean`, `PartB/PairWeighted.lean`, `PartB/PairWeightedEval.lean`, `PartB/PairPrimrec.lean` | the numerical encoding of strings and the product weighted automaton reducing Theorem B.3.4 to Theorem B.3.3 |
| `PartB/WeightedDec.lean`, `PartB/RatEqDec.lean`, `PartB/MealyDec.lean` | the decision procedures of Theorems B.3.3 and B.3.7, of Theorem B.3.4 and of Theorem B.4.2 |
| `PartB/PrefixCodes.lean`, `PartB/CodeRat.lean` | the two codes reducing prefix preservation to an equality of rational functions, and the rational function described by a code over its own finite alphabets |
| `PartB/RationalStatements.lean` | Sections B.1–B.2: rational relations, rational functions, bimachines |
| `PartB/WeightedNF.lean`, `PartB/WeightedLinRep.lean`, `PartB/WeightedPrecomp.lean`, `PartB/WeightedRegular.lean`, `PartB/WeightedZero.lean` | normal forms and linear representations of weighted automata, the proofs of Lemma B.3.5 and Theorem B.3.6, and Schützenberger's zeroness criterion |
| `PartB/WeightedStatements.lean` | Sections B.3–B.4: weighted automata, machine independent characterisations |
| `PartC/ContAux.lean` | continuity: closure under composition, letter-to-letter maps, reversal, duplication, and the map lifting (Lemma C.1.3) |
| `PartC/TwoDFA.lean` | deterministic two-way automata and Shepherdson's Theorem (their languages are regular) |
| `PartC/TwoWayCont.lean` | two-way transducers (Definition C.2.1) and their continuity (Theorem C.2.2) |
| `PartC/TwoWayPrecomp.lean` | pre-composition of a two-way transducer with a Mealy machine (Lemma C.2.6), via the Krohn-Rhodes Theorem: the reversible case, the flip-flop case, and pre-composition with reversal |
| `PartC/TwoWayHom.lean`, `PartC/TwoWayBlock.lean`, `PartC/TwoWayErase.lean`, `PartC/TwoWayRat.lean` | pre-composition of a two-way transducer with a homomorphism and with an arbitrary rational function (Corollary C.2.7) |
| `PartC/TwoWayRun.lean`, `PartC/TwoWayVisit.lean`, `PartC/TwoWayAnnot.lean`, `PartC/TwoWayAnnotBim.lean`, `PartC/TwoWayCompAux.lean`, `PartC/TwoWayCompPred.lean`, `PartC/TwoWayComp.lean`, `PartC/TwoWayCompFinal.lean` | the composition of two two-way transducers (Theorem C.2.5) |
| `PartC/TwoWaySweep.lean`, `PartC/TwoWayRegular.lean` | explicit two-way transducers for the identity, for post-composition with a letter-to-letter map, and for map reverse and map duplicate; every regular function is computed by a two-way transducer (corrected Corollary C.2.8) |
| `PartC/RegularDef.lean` | the prime regular functions and the regular functions (Definition C.0.14), moved here unchanged from `PartC/Statements.lean`, together with their elementary closure properties |
| `PartC/RatBuild.lean`, `PartC/RatTools.lean`, `PartC/RatSeq.lean` | a bimachine-based builder for rational functions, and the rational functions used by Lemma C.2.10 and Claim C.2.11 (constants, `cons`, letter-to-letter maps, homomorphisms, conditionals on a regular language, and sequential letter-by-letter transducers) |
| `PartC/MapLiftAux.lean`, `PartC/MapLiftRat.lean`, `PartC/MapLiftPrime.lean`, `PartC/RegMapLift.lean` | closure of the regular functions under map lifting (first item of Lemma C.2.10): the map lifting of a rational function is rational, the map liftings of map reverse and map duplicate are regular, and the general case follows by induction on the composition tree |
| `PartC/SumShape.lean`, `PartC/SumPrime.lean`, `PartC/SumReg.lean`, `PartC/RegSum.lean` | Claim C.2.11: the *marked sum* of two regular functions, its compatibility with composition, its prime base cases, and the passage from the marked sum to the sum of the claim (with the counterexample `Transducers.not_sum_of_regular_nil` to the claim as printed) |
| `PartC/RegClosure.lean` | closure of the regular functions under concatenation and under conditionals over a regular language (second and third items of Lemma C.2.10) |
| `PartC/SnakeWidth.lean` | the *width* of the run of a two-way transducer (the maximal number of visits to a single column) and the bound `width ≤ |Q|` for a halting run |
| `PartC/SnakeBase.lean` | the base cases `k ≤ 1` of the induction on the width in the snake lemma: a halting run of width one never moves left, so it is a left-to-right pass, its output is computed by a bimachine, and the inputs on which it is such a pass form a regular language (`TwoWay.widthOut_zero_isRegular`, `TwoWay.widthOut_one_isRegular`) |
| `PartC/SnakeReg.lean` | the book's snake lemma, as the induction on the width `Transducers.snakeReg` over the predicate `Transducers.SnakeReg` ("the width-`k` output function of *every* two-way transducer over *every* finite alphabet is regular") — the base cases `k ≤ 1` come from `SnakeBase.lean` and the induction step `Transducers.boundedWidth_isRegular_step` (from `SnakeReg (k+1)` to `SnakeReg (k+2)`) is the only remaining `sorry` of Section C.2 — together with `Transducers.boundedWidth_isRegular` and the reduction of the hard half of Theorem C.2.9 to it (`Transducers.isRegularFun_of_isTwoWay`) |
| `PartC/SnakeWalk.lean` | combinatorics of the trajectory of a run, seen as a walk: intermediate values, first and last visit to a column, visit counts, record-breaking columns, and the width bounds for the progress parts and for the two halves of a one-sided loop |
| `PartC/SnakeRec.lean` | the sequence of record-breaking columns of a walk, its stabilisation, the increasing chain of times it defines, and the resulting decomposition of the output of a run into the outputs of the loop parts and of the progress parts |
| `PartC/SnakeConfine.lean` | the confinement of the pieces of the record-breaker decomposition: after the last visit to a record-breaking column the walk stays strictly to its right (`Walk.recSeq_lt_of_recLast_lt`), up to the first visit to one it stays weakly to its left (`Walk.le_recSeq_of_le_recFirst`), so the loop and the progress parts of the `i`-th record-breaker are contained in the columns `x (i-1) < · ≤ x (i+1)` (`Walk.loop_confined`, `Walk.progress_confined`), i.e. in the book's block `wᵢ₋₁ # wᵢ` |
| `PartC/SnakeMirror.lean` | mirroring a two-way transducer (`TwoWay.mirror`: swap the two letters adjacent to the head and the two directions), an involution that turns every run into the mirrored run on the reversed input, with the same output (`TwoWay.stepCfg_mirror`, `TwoWay.reaches_mirror_iff`); this is the book's "reverse the snake" |
| `PartC/SnakeLoop.lean` | splitting a looping part of a walk into pieces of smaller width (intermediate visits to the base column, then the furthest column of each one-sided loop, the left-hand case being reduced to the right-hand one by reflecting the walk), and the induction step of the snake lemma at the level of runs: `Transducers.TwoWay.runOutput_splits` |
| `PartC/SnakeLocal.lean`, `PartC/SnakePiece.lean`, `PartC/SnakePieceRev.lean` | a piece of a run seen as a complete run on a window of the input: the window transducer `TwoWay.withContext`, the transducer `TwoWay.stopRight` that halts on reaching the right end of the window, and the identification of a left-to-right (resp. right-to-left, by mirroring) piece with the whole run of such a transducer, so that the induction hypothesis of the snake lemma applies to it (`TwoWay.widthOut_stopRight`) |
| `PartC/SnakeExc.lean` | the *excursions* of a record-breaking column: the intermediate visits `excT` to the column during its loop part, the time `excS` at which each excursion is at its furthest column `excC`, and the resulting cutting of the loop part into the `2k` halves of excursions |
| `PartC/SnakeParts.lean` | the output of a halting run of width at most `k` as the concatenation of the `2k+1` pieces of each record-breaker (`TwoWay.pieceOutput`, `TwoWay.blockOut`, `TwoWay.runOut_eq_partsOut`) |
| `PartC/SnakePieceIdent.lean` | the identification of a piece with the whole run of a window transducer on the interval between the record-breaking column and the furthest column of the excursion (`TwoWay.exists_widthOut_excHalves` for the two halves of an excursion, `TwoWay.exists_widthOut_prog` for a progress part) |
| `PartC/SnakeFinalConf.lean` | the same for the progress part after the last record-breaker, which reaches the end of the input (`TwoWay.exists_widthOut_finalProg_confined`) |
| `PartC/SnakeRegTools.lean` | the regular-function tools used to build the block function: cutting a factor out of an annotated pair of blocks and reading parameters off its first letter, both by bimachines |
| `PartC/SnakeBlock.lean` | the *block function* of stages 2--4: the annotated alphabet `TwoWay.SnakeLet` with its `2·(2k+1)` piece slots (`TwoWay.slot`), the output `TwoWay.pieceOut` of a piece with given parameters, the regularity of the block function (`TwoWay.isRegularFun_blockFun`), the notion of a correct marking (`TwoWay.IsSnakeMarking`) and the fact that the neighbouring-block map combinator applied to the block function on a correct marking computes the output of the run (`TwoWay.pairMap_blockFun_eq_runOut`) |
| `PartC/SnakeAssemble.lean` | the assembly of a correct marking out of purely numerical data — the cutting points of the blocks and, for every pair of blocks and every slot, the window and the parameters of that piece (`TwoWay.snakeAnn`, `TwoWay.isSnakeMarking_snakeAnn`) |
| `PartC/SnakeData.lean` | the numerical data of the pieces of a run and the existence of a correct marking of every nonempty input whose run halts with width at most `k` (`TwoWay.snakeY`, `TwoWay.exists_pieceData`, `TwoWay.exists_isSnakeMarking`) |
| `PartC/SnakeStage1.lean` | the book's stage 1: the guess-and-check formulation of the marking (`TwoWay.SnakeRel`, `TwoWay.exists_regular_snakeLang` — the only `sorry` of Section C.2 — `TwoWay.exists_rational_snakeRel`, `TwoWay.exists_snakeMarking`) and the equation `widthOut M K w = pairMap (blockFun …) (ann w)` that the induction step consumes (`TwoWay.widthOut_eq_pairMap`) |
| `PartC/TwoWayOrder.lean` | the *order in time* of the visits of a run to a cut is a regular property: a cut marked with a pair of states `(q₁, q₂)` is accepted by the two-way automaton `TwoWay.orderAut` exactly when the run visits it in `q₁` before it ever visits it in `q₂` (`TwoWay.VisitsBefore`, `TwoWay.orderLang_isRegular`), together with the resulting API for the first and the last visit to a cut |
| `PartC/TwoWayAnnotOrd.lean` | the same information as a *rational annotation* of the input (`TwoWay.exists_rational_visitOrder_annot`): from the annotation of the two letters adjacent to a cut one reads off, for every pair of states, which of the two visits comes first, and hence which visit to the cut is the first and which is the last |
| `PartC/RatBi.lean` | *bilateral rewritings*: a rewriting in which the block produced at a letter depends on the letter, on the state of a deterministic automaton run left-to-right on the prefix and on the state of a deterministic automaton run right-to-left on the suffix, is computed by a bimachine and hence rational (`Transducers.isRationalFun_biEval`); the two standard instances are cutting out the factor selected by regular lookaround (`isRationalFun_biFilter`) and cutting the input into the blocks it delimits (`isRationalFun_biMarkSep`) |
| `PartC/RegPair.lean` | the *neighbouring-block map combinator* is a regular operation (`Transducers.RegPair.isRegularFun_pairMap`): if `f` is regular then so is `w₀ # ⋯ # wₙ ↦ f (w₀ # w₁) · f (w₁ # w₂) ⋯ f (wₙ₋₁ # wₙ)`.  This is stages 1--3 of the book's induction step, carried out exactly as in the book: a rational function appends a copy of the separator at the end of every block, map duplicate procures the two copies of every block, and a bilateral rewriting deletes the extra copies of `w₀` and `wₙ` and re-brackets the rest |
| `PartC/SSTDef.lean` | Definition C.3.1: the copyless restriction (`Transducers.Copyless`), streaming string transducers (`Transducers.SST`) and their semantics (`SST.subst`, `SST.runConfig`, `SST.eval`, `Transducers.IsSST`), moved here unchanged from `Statements.lean` so that the constructions of Theorem C.3.2 can precede it |
| `PartC/SSTBasic.lean` | the elementary API of an sst: substitution of register contents, the workable form `Transducers.copyless_iff` of the copyless restriction, the list `Transducers.regsOf` of register occurrences, and the *simulation lemma* `SST.eval_of_sim` by which every construction below is verified |
| `PartC/SSTComp.lean` | the easy cases of the closure of sst's under post-composition with a prime regular function: the identity sst, homomorphisms, the separator function and the case distinction on a regular language |
| `PartC/SSTMealyRev.lean`, `PartC/SSTMealyFF.lean`, `PartC/SSTMealy.lean` | post-composition of an sst with a Mealy machine, hence with an arbitrary rational function: since the naive construction is not copyless, the machine is decomposed by Krohn–Rhodes (Theorem A.2.2) into reversible and flip-flop machines, treated in the first two files, and `SSTMealy.lean` assembles them |
| `PartC/SSTMapRev.lean`, `PartC/SSTMapDup.lean` | post-composition of an sst with map reverse and with map duplicate, the two remaining prime regular functions: the register contents are kept as tuples indexed by the position of the separators inside them, and copylessness is proved by counting register occurrences |
| `PartC/SSTRegular.lean` | the "regular to sst" half of Theorem C.3.2 (`Transducers.isSST_of_isRegularFun`): sst's are closed under post-composition with every prime, hence with every regular function, and applying this to the identity sst gives the statement |
| `PartC/SSTNorm.lean` | *normalised* sst's (`Transducers.NSST`: the register update depends only on the letter read, the state only on the last letter, and no register occurs twice in a final output string) and the reduction of an arbitrary sst to one (`Transducers.exists_nsst_of_sst`): the input letters are annotated by a Mealy machine with the state of the sst before them, and `K + 1` copies of every register are kept so that the occurrences in a final output string can be given pairwise distinct copies |
| `PartC/SSTWalk.lean` | the two-way transducer that traverses the register flow tree of a normalised sst (`Transducers.isTwoWay_of_nsst`): it expands the final output string depth-first, moving left to expand the value of a register and right when an expansion is finished, and the copyless restriction is what makes the place at which the expansion has to be resumed a function of the register and of the letter at the position returned to (`NSSTWalk.findReg_eq`, `NSSTWalk.scan`, `NSSTWalk.top`) |
| `PartC/SSTTwoWay.lean` | the "sst to regular" half of Theorem C.3.2, through Theorem C.2.9 (`Transducers.isTwoWay_of_isSST`): the annotation of `SSTNorm.lean` is rational and two-way transducers are closed under pre-composition with rational functions (Corollary C.2.7) |
| `PartC/KTypes.lean` | `k`-types of strings (Definition C.4.12) and their properties (Lemma C.4.15) |
| `PartC/Statements.lean` | Sections C.1–C.3: regular functions, two-way transducers, streaming string transducers |
| `PartC/MSODef.lean` | the definitions of Section C.4: monadic second-order logic over strings, mso relabellings, mso transductions and the first-order fragment (moved unchanged out of `MSO.lean`, which imports this file) |
| `PartC/MSOSyntax.lean` | elementary syntax and semantics of mso formulas: satisfaction depends only on the free variables (`MSO.sat_congr`), bounds on the variables of a formula, finite conjunctions and disjunctions, universal quantification and implication as abbreviations, and the existential closure of a list of variables |
| `PartC/RegAut.lean` | a toolkit of regular languages used by the translation of formulas into automata: languages defined by a `foldl` and by an nfa, Boolean operations, finite intersections, images and inverse images of letter-to-letter maps, the scanning languages, and the language of strings with exactly one marked position |
| `PartC/MSOAnnot.lean` | Lemma C.4.2: the language `AnnLang` of valid annotated strings satisfying a formula, its regularity by induction on the syntax of the formula, and its identification with the language in the statement of the lemma |
| `PartC/MSOBuchi.lean` | Theorem C.4.1: the language of a sentence is regular (from Lemma C.4.2), and the formula that guesses the run of a dfa as one second-order variable per state |
| `PartC/MSORelab.lean` | Claim C.4.6: the strings over `Γ × 2` with one marked position at which a formula holds form a regular language, and the language of the claim is the intersection, over the finitely many indices, of the complements of the projections of those languages |
| `PartC/MarkStr.lean` | doubly marked strings: the alphabet `Mark2 A = A × 2 × 2`, the marking `markAt2 w x y` of two positions of a string and its decomposition into prefix, marked infix and suffix, and the regular language `markedSat2 φ` of doubly marked strings satisfying a formula (from Lemma C.4.2) |
| `PartC/MarkLogic.lean` | the converse translation: from an automaton over `Mark2 A` back to an mso formula with one free variable (`exists_form_of_regular`), by a syntactic translation of the formula given by Theorem C.4.1 for the language of marked strings |
| `PartC/MarkBimach.lean` | the bimachine that precomputes, in every position of the input, the state of each automaton of a finite family on the unmarked prefix and its state transformation on the unmarked suffix; the function `markFun` it computes, its rationality (from Theorem B.2.3) and, in the letter-to-letter case, its length preservation |
| `PartC/MarkDelay.lean` | the delayed automaton reading letters that carry states and state transformations: it keeps the last letter read pending, since whether a position is the last one is known only when the string ends |
| `PartC/MSORatRelab.lean` | Theorem C.4.4: from a bimachine to an mso relabelling (this is Claim C.4.5 of the book, formalised for the index of a bimachine rather than for an unambiguous transducer), and from an mso relabelling back to a bimachine |
| `PartC/MSOPrecomp.lean` | Lemma C.4.10: the letter-to-letter rational function that decorates every position by the states of the automata of the family, the set of letters for a formula with one free variable, and the delayed language for a formula with two free variables |
| `PartC/MSOSubst.lean` | renaming of all the variables of a formula and the two combinators `MSO.atv`, `MSO.atv2` that plug a formula with one or two free variables under a quantifier |
| `PartC/MSONorm.lean` | Lemma C.4.9: the normalisation of the type `τ` of an mso transduction — a single set of tags, one universe and letter formula with one free variable per tag and one order formula with two free variables per pair of tags (`Transducers.NormT`), with the extra elements of `τ` attached to the first position of the input |
| `PartC/SortedEnum.lean` | the order-theoretic dictionary between a linear order on a finite set and its increasing enumeration (minimum, maximum, successor) |
| `PartC/MSOWalkForms.lean` | the mso formulas that the walking transducer of Theorem C.4.8 asks about — "is this element the first / the last one", "is its successor at the same position, or to the right", "is this element the successor of that one" — and their meaning in terms of the sorted enumeration of the selected elements |
| `PartC/WalkAut.lean` | the walking two-way transducer of Theorem C.4.8, in abstract form (letter-indexed answers to the unary questions and one deterministic automaton with a family of acceptance conditions for the binary ones), and its correctness `Transducers.WalkAut.computes_of_spec` |
| `PartC/MSOWalkData.lean` | the walking transducer of an mso transduction: the product of the family of automata (with the last letter read), the `WalkAut.Data` built from the precomputation of Lemma C.4.10, and the verification of the nine hypotheses of `WalkAut.computes_of_spec` |
| `PartC/MSOReg.lean` | Theorem C.4.8, from mso transductions to regular functions: normalise (Lemma C.4.9), precompute the questions (Lemma C.4.10), walk (`MSOWalkData.lean`), and compose the rational precomputation with the width-bounded output of the walking transducer, which is regular by Theorem C.2.9 |
| `PartC/RunProbe.lean` | probing the run of a two-way transducer by a deterministic two-way automaton that simulates it and stops at the first configuration satisfying a trigger condition (used for the converse half of Theorem C.4.8) |
| `PartC/RunMark.lean` | the regular languages of doubly marked strings describing the run of a two-way transducer: which targets it reaches, which letter it produces there, and which of two targets it reaches first |
| `PartC/MarkLogic2.lean` | the converse translation from an automaton over `Mark2 A` back to an mso formula with **two** free variables |
| `PartC/FlatIndex.lean`, `PartC/RunElts.lean` | the combinatorics of the output positions of a two-way transducer as pairs (step of the run, position inside the string produced at that step), and the list of elements required by `MSOTransduction.Outputs` |
| `PartC/TwoWayMSO.lean` | Theorem C.4.8, from two-way transducers to mso transductions: the mso transduction whose elements are the pairs (configuration, index of a produced letter), with all its formulas obtained from `RunMark.lean` through Theorem C.4.1 |
| `PartC/FORel.lean` | relativisation of a first-order formula to the positions strictly below, at most, or strictly above a variable (`MSO.relLt`, `relLe`, `relGt`), the strict order `MSO.ltVar` and the fact that a first-order sentence does not see its valuations (`MSO.sat_sentence_congr`) |
| `PartC/FOSeg.lean` | factors of a string between two bounds (`MSO.segP`), their splitting, and the transfer of a splitting along an equality of `(k+1)`-types (`Transducers.exists_split_of_tp_succ_eq`) |
| `PartC/FOComp.lean` | Claim C.4.14 (an internal step, not a numbered result): the compositionality of first-order logic — if two strings have the same `k`-type then a marked position on one side can be matched on the other so that all formulas of quantifier rank `k` are preserved (`Transducers.KEquiv`, `sat_iff_of_kEquiv`, `sat_iff_of_tp_eq`) |
| `PartC/FORename.lean` | the effect of renaming and of shifting the variables of a formula on being first-order, on the quantifier rank and on the free variables, and finite conjunctions and disjunctions of first-order formulas |
| `PartC/FOHintikka.lean` | the second half of Lemma C.4.13: a first-order sentence of quantifier rank at most `k` separating two strings of different `k`-type (`Transducers.exists_fo_sentence_of_tp_ne`, `tp_eq_of_fo_equiv`) |
| `PartC/FOTypeDFA.lean` | the easy direction of Theorem C.4.11: the (aperiodic, finite) automaton of `k`-types and the aperiodic dfa recognising a first-order definable language (`Transducers.tpDFA`, `aperiodic_dfa_of_foDefinable`) |
| `PartC/FOSubstRel.lean` | substitution of a sentence for a label test in a first-order formula, relativised to the positions at most a variable (`MSO.substRel`), used for the composition of first-order definable Mealy machines |
| `PartC/FOFlipFlop.lean` | flip-flop machines: the letter-indexed reset target (`Mealy.resetTo`) and the description of the state reached after a prefix as the target of the last resetting letter (`Mealy.trans_take_eq_iff`) |
| `PartC/FOMealy.lean` | the hard direction of Theorem C.4.11: first-order definable Mealy machines (`Transducers.FODefMealy`), their closure under composition, the first-order definability of flip-flops and hence of every composition of flip-flops (through the aperiodic Krohn-Rhodes Theorem A.2.8), and the Mealy machine of a dfa (`Transducers.foDefinable_of_aperiodic_dfa`) |
| `PartC/FORev.lean` | first-order definability and reversal: every first-order definable language is defined by a first-order *sentence* (`FODefinable.exists_sentence`), the characterisation of first-order definability by invariance under `k`-types, the reversal `tpRev` of a `k`-type and `FODefinable.reverse`, and the first-order definability of the languages `{u \| δ*(q₀,u) = q}` and `{u \| δ*(q₀,reverse u) = q}` of an aperiodic transition function |
| `PartC/FOPos.lean` | compositionality at a position: whether a first-order formula of quantifier rank at most `k`, evaluated with the constant valuation at a position, holds depends only on the `k`-type of the prefix, the letter and the `k`-type of the suffix (`Transducers.sat_const_iff_of_tp_split`) |
| `PartC/FORelabBimach.lean` | Theorem C.4.16, from first-order relabellings to aperiodic bimachines: the prefix and suffix automata compute the `k`-type of the prefix and of the suffix, which are aperiodic transition functions, and by `FOPos.lean` the index chosen at a position — hence the output block — is a function of those two types and of the letter |
| `PartC/FOBimachRelab.lean` | Theorem C.4.16, from aperiodic bimachines to first-order relabellings: the formula attached to an index `(q, a, s, last?)` says that the prefix drives the prefix automaton to `q` (a first-order sentence by Theorem C.4.11, relativised to the positions below), the letter is `a`, the suffix drives the suffix automaton to `s` (relativised to the positions above, first-order by `FODefinable.reverse`), and the position is, or is not, the last one; the block of the last gap is appended to the block of the last position |
| `PartC/ITransBuild.lean` | tools for building first-order transductions: the construction of an `ITrans.Outputs` witness from a pairwise-ordered enumeration of the selected elements (`ITrans.outputs_of_pairwise`, `ITrans.outputs_of_forall₂`), the list lemmas `Transducers.forall₂_append` and `Transducers.forall₂_flatMap`, and the first-order transductions given by the identity and by a bijection of alphabets (`Transducers.isFOTransduction_id`, `Transducers.isFOTransduction_map_equiv`) |
| `PartC/BlockPos.lean` | the block combinatorics of the positions of a string over `Option A`: the separators (`Transducers.SepAt`), the equivalence "same block" (`Transducers.SameBlk`) with its symmetry, transitivity and betweenness properties, and the description of both for a string of the shape `u # w'` |
| `PartC/BlockForm.lean` | the first-order formulas `Transducers.sepF`, `Transducers.betweenF` and `Transducers.sameBlkF` expressing the predicates of `BlockPos.lean`, with their quantifier-rank-free-ness and their semantics |
| `PartC/FORelabTrans.lean` | every first-order relabelling is a first-order transduction (`Transducers.isFOTransduction_of_isFORelabelling`) |
| `PartC/FOTransRev.lean` | map reverse is a first-order transduction (`Transducers.isFOTransduction_mapReverse`): the elements are the positions, ordered by `Transducers.revOrd`, which keeps the order of the blocks and reverses the order inside a block |
| `PartC/FOTransTr.lean`, `PartC/FOTransComp.lean` | first-order transductions are closed under composition (`Transducers.isFOTransduction_comp`), by translating the formulas of the second transduction backwards along the first one; this is the first-order substitute for the route through Theorem C.4.8 used in the mso case |
| `PartC/FOTransDup.lean` | map duplicate is a first-order transduction (`Transducers.isFOTransduction_mapDuplicate`): the elements are pairs `(copy, position)` ordered by `Transducers.dupOrd`, which puts the first copy of a block before its second copy |
| `PartC/FOPrimeFam.lean` | the family `Transducers.FORegularFam` of prime first-order regular functions (first-order rational functions, map reverse, map duplicate) |
| `PartC/FOTransPrimeComp.lean` | every composition of the primes of `FORegularFam` is a first-order transduction (`Transducers.isFOTransduction_of_compClosure`), by induction on `CompClosure` from the four files above |
| `PartC/MSO.lean` | Section C.4: the numbered results that are **proved** — Theorem C.4.1, Lemma C.4.2, Theorem C.4.4, Claim C.4.6, Theorem C.4.8, Lemma C.4.10, Theorem C.4.11, Lemma C.4.13, Lemma C.4.15 and Theorem C.4.16 (this file contains no `sorry`) |
| `PartC/MSOOpen.lean` | Section C.4: pointer comments only. It used to hold the results of Section C.4 that were not yet proved; the last one, Theorem C.4.17, has been **removed from the formalised theorems at the user's request** and is kept there only as a comment, so the file now declares nothing and Section C.4 has no `sorry` left |
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
  on all of `ℕ*` would be vacuous.  For the same reason the property decided in
  Theorem B.4.2 is relativised to the strings over the alphabet of the code; the
  original statement is kept as a comment in `PartB/WeightedStatements.lean`,
  with an explanation.  Undecidability (Theorem B.1.6) is
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
| Theorem B.3.3 (equivalence over ℚ) | `Transducers.weighted_equivalence_decidable` | proved from the effectivity hypothesis `EffectiveWeightedEvalEq` (`WeightedDec.lean`) |
| Theorem B.3.4 (equivalence of rational functions) | `Transducers.rationalFun_equivalence_decidable` | proved from `EffectiveWeightedEvalEq` (reduction to B.3.3 in `RatEqDec.lean`) |
| Lemma B.3.5 (pre-composition) | `Transducers.weighted_precomp_rational` | proved (`WeightedNF.lean`, `WeightedLinRep.lean` and `WeightedPrecomp.lean`) |
| Theorem B.3.6 (characterisation of rationality) | `Transducers.rational_iff_weighted_precomp` | proved ("⇒" is Lemma B.3.5, "⇐" in `WeightedRegular.lean`) |
| Theorem B.3.7 (zeroness) | `Transducers.weighted_zeroness_decidable` | proved from `EffectiveWeightedEvalEq` (special case of B.3.3, `WeightedDec.lean`) |
| Theorem B.4.1 (characterisation of Mealy machines) | `Transducers.isMealy_iff` | proved (`MealyChar.lean`) |
| Theorem B.4.2 (deciding the Mealy fragment) | `Transducers.rationalFun_isMealy_decidable` | proved from `EffectiveWeightedEvalEq` (`PrefixCodes.lean`, `CodeRat.lean`, `MealyDec.lean`); the statement is relativised to the strings over the alphabet of the code |
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

#### The four conditional results of Part B (B.3.3, B.3.4, B.3.7, B.4.2)

These four decidability statements are proved from **one explicit effectivity
hypothesis**, in exactly the style already used for Theorem B.1.6 (which takes
the undecidability of the Post correspondence problem as an explicit
hypothesis).  Every other ingredient — Schützenberger's bound *and its effective
form*, the reduction of equivalence of rational functions to equivalence of
weighted automata, the derivation of B.3.4 from B.3.3, and the two code
constructions needed for prefix preservation in B.4.2 — is proved in full, with
no `sorry` anywhere in their dependencies.  Each of the four was checked with
`#print axioms` and depends only on `propext`, `Classical.choice`, `Quot.sound`.

The hypothesis is in `PartB/Effective.lean`:

* `EffectiveWeightedEvalEq` — there is a computable procedure which, given two
  codes of weighted automata over `ℚ` and a string `v`, decides whether the two
  automata take the same value on `v` (correctly at least for valid codes).

It is a true statement about ordinary computability — the value is a finite sum
of products of the rational weights read off the code, and rational arithmetic
is computable — and the docstring in `PartB/Effective.lean` justifies it
informally.  It is assumed rather than proved because Mathlib's
`Primrec`/`Computable` API contains no arithmetic on `ℤ` or on `ℚ`, so no
procedure manipulating rational weights can currently be shown to be
`Computable`; when Mathlib gains that API, the hypothesis becomes provable and
the four results become unconditional.  The unconditional forms of the four
statements are kept in `PartB/WeightedStatements.lean` as commented-out
originals, each with a note explaining the relationship.

The *second* fact these results need, an effective form of Schützenberger's
criterion (`EffectiveWeightedBound`: a computable function which, given two
codes, returns a length bound after which agreement on all shorter strings
forces the two computed functions to be equal), was formerly assumed as well.
It is now **proved**, in `PartB/WeightedBound.lean`
(`Transducers.effectiveWeightedBound`, checked with `#print axioms`: only
`propext`, `Classical.choice`, `Quot.sound`), since the bound depends on the
sizes of the codes only and involves no arithmetic on the weights.

The proofs are organised as follows.

* `Effective.lean` — the hypothesis, with its justification, and the statement
  of the effective bound.
* `WeightedBound.lean` — the effective bound.  `linRep_eq_of_short` (in
  `WeightedZero.lean`) gives Schützenberger's criterion with the explicit bound
  `d₁ + d₂`, the dimensions of two linear representations; the representation
  built in `WeightedNF.lean`/`WeightedLinRep.lean` has one dimension per useful
  state of `atom (initCopy M)`, and a useful state is an initial state or the
  target of a transition, hence occurs in the explicit list `coverList` of the
  copies of the initial states, the extra state `phi`, and the states `cfg t x`
  for `t` a lifted or copied transition and `x` a suffix of its input string.
  This gives `wcodeBound`, a primitive recursive function of the code.
* `WCodes.lean` — codes of weighted automata over `ℚ`, the automaton and the
  function that a code describes, and the validity promise; a coded automaton
  reads only finitely many letters, so it takes the value `0` on every string
  using another letter.
* `WeightedDec.lean` — Theorems B.3.3 and B.3.7: compute the bound from the two
  codes and compare the values on all strings of length at most the bound over
  the letters of the two codes; zeroness is the special case in which the second
  automaton is the empty one.
* `CodeAtom.lean`, `CodeMerge.lean` — the letter-atomic normal form `normCode`
  of a code of an nfa with output: every transition reads exactly one letter and
  the transitions are canonical, so that the runs over a string `w` all have
  `|w|` transitions.
* `RunList.lean` — the explicit enumeration of the runs of a letter-atomic code.
* `CodeAlpha.lean`, `CodeEps.lean` — the alphabets of a code, the test
  `sameAlpha` that two codes read the same letters, and the value of a coded
  function on the empty input.
* `Iota.lean`, `PairWeighted.lean`, `PairWeightedEval.lean`, `PairPrimrec.lean`
  — the numerical encoding `iota K` of strings, additive on the left, and the
  product weighted automaton `pairW K M N` whose value on a nonempty input is
  the encoding of the output of `M` multiplied by the numbers of accepting runs
  of `M` and of `N`; the construction is primitive recursive in the two codes.
* `RatEqDec.lean` — Theorem B.3.4: the two coded functions are equivalent
  exactly when the two codes read the same letters, agree on the empty string,
  and the two symmetric products `pairW K M N` and `pairW K N M` are equivalent
  weighted automata, which is decided by Theorem B.3.3.
* `PrefixCodes.lean` — the codes `dropCode c` (computing `w ↦ dropLast (f w)`)
  and `shiftCode c` (computing `w ↦ f (dropLast w)`); for a length preserving
  coded function, prefix preservation is exactly the equality of the two.
* `CodeRat.lean` — the function `codeFun c` described by a code over its own
  finite alphabets `InA c` and `OutA c`; it is rational, it is computed by a
  Mealy machine exactly when the coded relation is length preserving and prefix
  preserving, and the property appearing in Theorem B.4.2 is equivalent to
  `IsMealy (codeFun c)`.
* `MealyDec.lean` — Theorem B.4.2: decide length preservation with Lemma B.4.3
  and prefix preservation with Theorem B.3.4 applied to `dropCode c` and
  `shiftCode c`.

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
| Theorem C.2.5 (composition) | `Transducers.twoWay_comp` | proved (`TwoWayRun.lean`, `TwoWayVisit.lean`, `TwoWayAnnot.lean`, `TwoWayAnnotBim.lean`, `TwoWayCompAux.lean`, `TwoWayCompPred.lean`, `TwoWayComp.lean`, `TwoWayCompFinal.lean`) |
| Lemma C.2.6 (pre-composition with Mealy machines) | `Transducers.twoWay_precomp_mealy` | proved |
| Corollary C.2.7 (pre-composition with rational functions) | `Transducers.twoWay_precomp_rational` | proved (`TwoWayHom.lean`, `TwoWayBlock.lean`, `TwoWayErase.lean` and `TwoWayRat.lean`, from Theorem B.2.6 and Lemma C.2.6) |
| Corollary C.2.8 (regular ⊆ two-way) | `Transducers.regularFun_isTwoWay`, `Transducers.isTwoWay_of_isRegularFun` | proved (`TwoWaySweep.lean`, `TwoWayRegular.lean`, from Corollary C.2.7 and Theorem C.2.5); the direction printed in the book is a typo — see *A typo in Corollary C.2.8* below |
| Theorem C.2.9 (two-way = regular) | `Transducers.twoWay_iff_regular`, `Transducers.twoWay_isRegular` | the right-to-left implication is proved (it is Corollary C.2.8 above); the left-to-right one, `Transducers.twoWay_isRegular` (two-way ⊆ regular, the inclusion printed in Corollary C.2.8), is **open**: it is reduced, sorry-free, to the snake lemma `Transducers.boundedWidth_isRegular` of `SnakeReg.lean`, whose base cases `k ≤ 1` are proved in `SnakeBase.lean` and whose combinatorial content is proved in `SnakeWalk.lean`, `SnakeRec.lean` and `SnakeLoop.lean`; what is left is the induction step `Transducers.boundedWidth_isRegular_step`, and inside it the single statement `Transducers.TwoWay.exists_regular_snakeLang` of `SnakeStage1.lean` (the book's stage 1: the correct markings of the input form a regular language) — see *What is missing in Theorem C.2.9* below |
| Lemma C.2.10 (closure properties) | `Transducers.regular_closure_properties` | **proved** (`MapLiftAux.lean`, `MapLiftRat.lean`, `MapLiftPrime.lean`, `RegMapLift.lean`, `RatSeq.lean`, `RegClosure.lean`) |
| Claim C.2.11 (disjoint sums) | `Transducers.sum_of_regular` | **proved** (`SumShape.lean`, `SumPrime.lean`, `SumReg.lean`, `RegSum.lean`), in the corrected form — the claim as printed is false on the empty input, see *An error in Claim C.2.11* below |
| Definition C.3.1 (sst) | `Transducers.SST`, `Transducers.IsSST` | — |
| Theorem C.3.2 (sst = regular) | `Transducers.sst_iff_regular` | both implications are **proved** (`SSTComp.lean`, `SSTMealyRev.lean`, `SSTMealyFF.lean`, `SSTMealy.lean`, `SSTMapRev.lean`, `SSTMapDup.lean`, `SSTRegular.lean` for `regular ⊆ sst`; `SSTNorm.lean`, `SSTWalk.lean`, `SSTTwoWay.lean` for `sst ⊆ two-way`), but the statement still depends on `sorryAx`: the direction `sst ⊆ regular` goes through Theorem C.2.9, which is open — see *The proof of Theorem C.3.2* below |
| Theorem C.4.1 (mso = regular languages) | `Transducers.regular_iff_msoDefinable` | **proved** (`MSO.lean`, from `MSOSyntax.lean`, `RegAut.lean`, `MSOAnnot.lean`, `MSOBuchi.lean`) |
| Lemma C.4.2 (formulas with free variables) | `Transducers.mso_annotated_regular` | **proved** (`RegAut.lean`, `MSOSyntax.lean`, `MSOAnnot.lean`) |
| Definition C.4.3 (mso relabelling) | `Transducers.MSORelabelling`, `Transducers.IsMSORelabelling` | — |
| Theorem C.4.4 (rational = mso relabelling) | `Transducers.rational_iff_msoRelabelling` | **proved** (`MSO.lean`, from `MSORatRelab.lean`, `MarkStr.lean`, `MarkLogic.lean`, `MarkBimach.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Claim C.4.5 | not formalised as a numbered result; it is the internal step of Theorem C.4.4 and appears as `Transducers.RatRelab.exists_form` in `MSORatRelab.lean`, stated for the index of a bimachine | — |
| Claim C.4.6 (annotated relabellings) | `Transducers.msoRelabelling_annotation_regular` | **proved** (`MSORelab.lean`, from Lemma C.4.2) |
| Definition C.4.7 (mso transduction) | `Transducers.MSOTransduction`, `Transducers.IsMSOTransduction` | — |
| Theorem C.4.8 (mso transductions = regular) | `Transducers.msoTransduction_iff_regular` | both implications are **proved** (`MSO.lean`, from `MSOReg.lean`, `MSOWalkData.lean`, `WalkAut.lean`, `MSOWalkForms.lean`, `MSONorm.lean`, `SortedEnum.lean` for `mso ⊆ regular`; `TwoWayMSO.lean`, `RunProbe.lean`, `RunMark.lean`, `RunElts.lean`, `MarkLogic2.lean` for `regular ⊆ mso`), but the statement still depends on `sorryAx`: the direction `mso ⊆ regular` goes through Theorem C.2.9, which is open — see *The proof of Theorem C.4.8* below |
| Lemma C.4.9 | not formalised as a numbered result; it is the normalisation of the type τ inside the proof of Theorem C.4.8 and appears as `Transducers.MSOTransduction.exists_norm` in `MSONorm.lean` | — |
| Lemma C.4.10 (formulas via rational functions) | `Transducers.mso_formulas_via_rational` | **proved** (`MSO.lean`, from `MSOPrecomp.lean`, `MarkStr.lean`, `MarkBimach.lean`, `MarkDelay.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Theorem C.4.11 (first-order = aperiodic) | `Transducers.foDefinable_iff_aperiodic_dfa` | **proved** (`MSO.lean`, from `FOTypeDFA.lean` and `FOMealy.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Definition C.4.12 (k-types) | `Transducers.tp` | — |
| Lemma C.4.13 (types and formulas) | `Transducers.tp_eq_iff_fo_equiv` | **proved** (`MSO.lean`, from `FOComp.lean` and `FOHintikka.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Claim C.4.14 | internal step of the proof of Lemma C.4.13; not a numbered result, but formalised as `Transducers.sat_iff_of_kEquiv` (`FOComp.lean`) | — |
| Lemma C.4.15 (properties of types) | `Transducers.tp_properties` | proved (`KTypes.lean`) |
| Theorem C.4.16 (first-order relabellings) | `Transducers.foRelabelling_iff_aperiodicBimachine` | **proved** (`MSO.lean`, from `FORelabBimach.lean` for `first-order relabelling ⊆ aperiodic bimachine` and `FOBimachRelab.lean` for the converse, on top of `FORev.lean` and `FOPos.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Theorem C.4.17 (first-order transductions) | **removed from the formalised theorems at the user's request** (its statement is kept, commented out, in `MSOOpen.lean`) | not formalised as a theorem any more. What remains is the inclusion `compositions of primes ⊆ first-order transductions`, **proved** as `Transducers.isFOTransduction_of_compClosure` (`FOTransPrimeComp.lean`, on top of the closure under composition of `FOTransComp.lean` and the three primes of `FORelabTrans.lean`, `FOTransRev.lean` and `FOTransDup.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) — see *Theorem C.4.17: what was removed and what remains* below |

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

The files added for Theorem C.2.5 are:

* `TwoWayRun.lean` — the run of a two-way transducer indexed by time: it is
  injective up to the halting time, so a configuration on the run has a *unique*
  predecessor on the run (`TwoWay.pred_unique`).  This is what makes it possible
  to walk backwards along the run.
* `TwoWayVisit.lean` — the configurations that lie on the run form a regular
  property of the input: mark one letter with a state and a side, and the marked
  inputs whose run visits the marked cut in the marked state form a regular
  language, by Shepherdson's Theorem applied to the two-way automaton that
  accepts as soon as the run reaches the marked cut.  This replaces the analysis
  of the reachable configuration graph of Lemma C.2.3.
* `TwoWayAnnot.lean`, `TwoWayAnnotBim.lean` — the annotation of every position
  of the input by a window of three letters, the state of the deterministic
  automaton of the previous item after the prefix, and the acceptance function
  of the suffix.  It is computed by a bimachine, hence is a rational function
  (Theorem B.2.3), and from the annotations of the two letters adjacent to a cut
  one can read off which configurations lie on the run there.
* `TwoWayCompAux.lean`, `TwoWayCompPred.lean` — the bookkeeping of the output of
  a stretch of the run, and the computation of the predecessor of a
  configuration on the run from the annotation.
* `TwoWayComp.lean` — the composed transducer, for a first transducer all of
  whose transitions produce an output of the same length ending with a fixed
  letter.  The head of the second transducer is represented by a configuration
  of the first one on the run together with an offset inside the output of the
  transition taken there; moving right follows the run forwards, moving left
  follows it backwards, and a step that does not change the configuration is
  implemented by a *bouncing* step.
* `TwoWayCompFinal.lean` — Theorem C.2.5 in general: the outputs of the first
  transducer are padded with a blank letter to a common length, which is
  harmless because two-way transducers are closed under pre-composition with the
  erasing homomorphism that deletes the blanks.

#### A typo in Corollary C.2.8

The corollary is printed as "if a function is computed by a two-way transducer,
then it is regular", but its proof — "two-way transducers can compute all
rational functions by Corollary C.2.7, and they can compute map reverse and map
duplicate by Example C.2.4; finally, they are closed under composition thanks to
Theorem C.2.5" — establishes the *opposite* inclusion, that every regular
function is computed by a two-way transducer.  The following sentence of the
book confirms this reading: it announces that "the converse inclusion", namely
that two-way transducers can be decomposed into the prime regular functions,
will be proved later in the chapter (Theorem C.2.9).

The printed direction is therefore a typo.  `PartC/Statements.lean` records the
statement as printed in a comment at that place in the file, explaining the typo
and pointing out that this inclusion is exactly the left-to-right implication of
Theorem C.2.9, where it is stated as `Transducers.twoWay_isRegular` and where it
is still open; it is not duplicated as a separate `sorry`.  Corollary C.2.8
itself is formalised in the direction that its proof establishes, as
`Transducers.regularFun_isTwoWay`, and it is proved in full.  Its ingredients
are:

* `TwoWaySweep.lean` — the two-way transducer for the identity, closure under
  post-composition with a letter-to-letter map, and the *block sweeping*
  transducer: on each block of the input (a maximal factor without separators)
  it sweeps left to right, right to left and left to right again, emitting a
  string for each letter it passes.  Map reverse is the instance in which only
  the middle sweep produces output, map duplicate the one in which only the two
  outer sweeps do.
* `TwoWayRegular.lean` — closure under pre-composition with a letter-to-letter
  map (a special case of Corollary C.2.7), and the two instances of the sweeping
  transducer.  The corollary then follows by induction on the composition tree
  of the regular function, using Corollary C.2.7 for the rational primes and
  Theorem C.2.5 for the composition step.

#### An error in Claim C.2.11

The claim, as printed, says that for regular functions `f₁ : A₁* → B₁*` and
`f₂ : A₂* → B₂*` the function on `(A₁ + A₂)*` that applies `f₁` to the words
using only letters of `A₁`, applies `f₂` to the words using only letters of
`A₂`, and returns a fixed string `⊥` (using both output alphabets) on all other
words, is regular.  This is false for the empty word: `ε` uses only letters of
`A₁` *and* only letters of `A₂`, so the first two clauses force
`(f₁ ε).map inl = (f₂ ε).map inr`, which is impossible unless `f₁ ε` and `f₂ ε`
are both empty.  `Transducers.not_sum_of_regular_nil` in `PartC/RegSum.lean` is
an explicit counterexample (take `f₁` constant with a nonempty value and `f₂`
the identity).  The statement is also silently using that `B₁` and `B₂` are
nonempty, which is what makes `⊥` exist.

`PartC/Statements.lean` keeps the statement as printed, commented out, next to
the corrected statement `Transducers.sum_of_regular`, which restricts the first
two clauses to *nonempty* inputs, assumes `[Nonempty B₁] [Nonempty B₂]`, and
leaves the value on the empty input unspecified.  The correction is harmless for
the use the book makes of the claim: in the proof of Lemma C.2.10 the blocks the
sum is applied to always carry a marker and are therefore nonempty.

The proof follows the book: the construction is compatible with composition, so
it suffices to treat the case where one of the two functions is the identity and
the other is a prime.  This is carried out here for the *marked sum*, a variant
in which the two copies of the input are prefixed by a marker
(`mkL u = inl false :: u.map (inr ∘ inl)` and `mkR u = inl true :: u.map (inr ∘ inr)`
over `Bool + A₁ + A₂`); the marker is what makes the two clauses consistent, and
it is removed at the very end by a rational function.  `SumShape.lean` contains
the definition and the composition step, `SumPrime.lean` the base cases for map
reverse and map duplicate (a rational function inserts a separator before every
letter of the part that must stay unchanged, so that it can be recovered
afterwards), `SumReg.lean` the induction on the composition tree, and
`RegSum.lean` the passage to the statement of the claim.

#### What is missing in Theorem C.2.9

The right-to-left implication of Theorem C.2.9 is Corollary C.2.8, so it is
proved.  The left-to-right implication, `Transducers.twoWay_isRegular`, is still
open.  The book proves it by decomposing a two-way transducer as

```
A*  --compute snake graph-->  C*  --output of snake graph-->  B*
```

where a *snake graph* with states `Q`, length `n` and output alphabet `B` is a
directed graph whose vertices are pairs (row in `Q`, column in `{0,…,n}`), whose
edges are labelled by `B + 1` and join adjacent columns, and all of whose edges
lie on a single directed path; its output is the concatenation of the edge
labels along that path.  The first stage is rational, by the construction
already available in this project through `TwoWayVisit.lean` and
`TwoWayAnnot.lean`.  What is missing is the second stage: the book's lemma that
the output of a snake graph is a regular function of its string encoding, proved
by induction on the *width* of the snake graph (the maximal number of visits to
a single column, which is bounded by `|Q|`).

The reduction to that lemma is formalised and contains no `sorry`.  Rather than
introducing an alphabet of snake letters, a snake graph is presented as the run
of a two-way transducer, which is the same thing up to the choice of the input
alphabet: `SnakeWidth.lean` defines the width of a run (`TwoWay.WidthLe`) and
proves that a halting run has width at most the number of states
(`TwoWay.widthLe_card`, by the pigeonhole principle on configurations), and
`SnakeReg.lean` deduces `Transducers.isRegularFun_of_isTwoWay` from the *snake
lemma*

```lean
theorem boundedWidth_isRegular {A B Q : Type} [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) (k : ℕ) : IsRegularFun (TwoWay.widthOut M k)
```

(the function that outputs the run of `M` on the inputs whose run has width at
most `k`, and the empty string on all other inputs, is regular).

The snake lemma is proved by induction on `k`.  Its **base cases are proved**, in
`SnakeBase.lean`:

* `TwoWay.widthOut_zero_isRegular`: the width of a run is never `0`, since the
  initial configuration already visits the leftmost column
  (`TwoWay.not_widthLe_zero`), so the width-`0` output function is constantly
  empty;
* `TwoWay.widthOut_one_isRegular`: a halting run of width `1` never moves left,
  because a leftward step would revisit the column the run has just come from;
  such a run is a left-to-right pass, simulated by the deterministic automaton
  `TwoWay.passDFA` whose language `TwoWay.PassLang` is exactly the set of inputs
  on which the run is such a pass, and on that language the output of the run is
  produced by the bimachine `TwoWay.passBim` (`TwoWay.runOut_eq_passBim`), while
  off it the width-`1` output is empty (`TwoWay.widthOut_one_of_not_pass`); the
  case distinction is a rational function by `isRationalFun_ite_lang`.

The single remaining open statement is therefore the **induction step**, in
`SnakeReg.lean`:

```lean
def SnakeReg (k : ℕ) : Prop :=
  ∀ (A B Q : Type), Finite A → Finite B → Finite Q →
    ∀ M : TwoWay A B Q, IsRegularFun (TwoWay.widthOut M k)

theorem boundedWidth_isRegular_step (k : ℕ) (ih : SnakeReg (k + 1)) : SnakeReg (k + 2)
```

The induction hypothesis is quantified over *all* two-way transducers over *all*
finite input alphabets and state sets, which is how the book quantifies over all
snake graphs of a given width; `Transducers.snakeReg` performs the induction and
`Transducers.boundedWidth_isRegular` specialises it to a single transducer.
This is the only `sorry` of the project that concerns Section C.2.

What *is* proved, sorry-free, is the whole combinatorial content of the book's
induction step, in `SnakeWalk.lean`, `SnakeRec.lean` and `SnakeLoop.lean`:

* the trajectory of a halting run is a walk on the columns
  (`TwoWay.isWalk_traj`) of width at most `k` (`TwoWay.visitsLe_of_widthLe`);
* the record-breaking columns `x₀ < x₁ < ⋯ < x_N` of a walk are defined
  greedily (`Walk.recSeq`), the sequence stabilises (`Walk.recStable_recN`), and
  the first and last visits to them form an increasing chain of times covering
  the whole run, so that the output of the run is the concatenation of the
  outputs of the *loop parts* and of the *progress parts*
  (`TwoWay.outRange_eq_loopProgOut`, `TwoWay.runOutput_eq_loopProgOut`);
* each progress part visits every column at most `k - 1` times
  (`Walk.recProgress_visitsLe` and, for the part after the last record-breaker,
  `Walk.final_progress_visitsLe`);
* each loop part is cut into finitely many pieces of width at most `k - 1`
  (`Walk.loop_splitsInto`): first at the intermediate visits to its base column,
  which leaves one-sided loops, then at the first visit to the furthest column
  of each one-sided loop; the loops lying to the left of their base column are
  reduced to those lying to the right by reflecting the walk (`Walk.mir`);
* altogether, a halting run of width at most `k` (with `k ≥ 2`) splits into
  finitely many consecutive pieces of width at most `k - 1`, and its output is
  the concatenation of their outputs: `TwoWay.run_splitsInto_pred` and
  `TwoWay.runOutput_splits`;
* the pieces are moreover *confined* to two consecutive blocks of the input
  (`SnakeConfine.lean`), which is the book's step 4: after the last visit to a
  record-breaking column the walk stays strictly to its right
  (`Walk.recSeq_lt_of_recLast_lt`, the book's "after visiting this
  record-breaker, the previous one is never visited"), and up to the first
  visit to a record-breaking column it stays weakly to its left
  (`Walk.le_recSeq_of_le_recFirst`); hence the loop part and the progress part
  of the `i`-th record-breaker are contained in the columns
  `x (i-1) < · ≤ x (i+1)` (`Walk.loop_confined`, `Walk.progress_confined`,
  `TwoWay.run_loop_confined`, `TwoWay.run_progress_confined`).  This is what
  makes the rational function that produces one copy of the relevant factor of
  the input for each piece have linear growth, as a regular function must;
* the book's "without loss of generality the source column is before the target
  column; otherwise reverse the snake" is available as `TwoWay.mirror`
  (`SnakeMirror.lean`): swapping the two letters adjacent to the head in the
  transition function and swapping the two directions gives an involution on
  two-way transducers that turns every run into the mirrored run on the
  reversed input, with the same output (`TwoWay.stepCfg_mirror`,
  `TwoWay.reaches_mirror_iff`, `TwoWay.reaches_mirror_reverse`).  No alphabet of
  snake letters has to be introduced for this.

Two further ingredients of the book's induction step are now available as
sorry-free, reusable statements.

* The *gluing* of the pieces, which is stages 1--3 of the book's proof, is
  `Transducers.RegPair.isRegularFun_pairMap` (`RegPair.lean`): if `f` is
  regular, then so is

  ```lean
  w₀ # w₁ # ⋯ # wₙ  ↦  f (w₀ # w₁) · f (w₁ # w₂) ⋯ f (wₙ₋₁ # wₙ).
  ```

  The construction is the book's one: a rational function appends a copy of the
  separator at the end of each block, map duplicate produces
  `w₀$w₀$ # ⋯ # wₙ$wₙ$`, a bilateral rewriting (`RatBi.lean`) deletes the first
  copy of `w₀` and the second copy of `wₙ` and re-brackets the rest, the map
  lifting of `f` (Lemma C.2.10) is applied to every block and a homomorphism
  erases the separators.  The book's stage 3 -- duplicating each block once more,
  because each block carries both a loop part and a progress part -- is not
  needed separately: taking for `f` a concatenation `f = g₁ · g₂ ⋯ g_m` of
  boundedly many regular functions is already allowed, by the concatenation
  closure of Lemma C.2.10.  Likewise, cutting a factor out of a block by regular
  conditions and applying a regular function to it is the composition of
  `Transducers.isRationalFun_biFilter` with that function.
* The *order in time of the visits of the run to a cut*, which is what the
  recursion defining the record-breaking columns refers to, is available as a
  rational annotation of the input,
  `Transducers.TwoWay.exists_rational_visitOrder_annot`
  (`TwoWayOrder.lean`, `TwoWayAnnotOrd.lean`): a two-way automaton decides, for
  a cut marked with a pair of states `(q₁, q₂)`, whether the run visits it in
  `q₁` before it ever visits it in `q₂`, its language is regular, and the
  corresponding bimachine annotation makes the first and the last visit to every
  cut readable locally.

The remaining gap in `boundedWidth_isRegular_step` is therefore no longer
combinatorial but machine-theoretic: it is exactly the book's **stage 1**, the
rational function that marks the record-breaking columns and the pieces that
they delimit.  Everything that is built on top of that marking is proved.

* The pieces are *identified with whole runs of window transducers*, to which
  the induction hypothesis applies: `TwoWay.exists_widthOut_excHalves` and
  `TwoWay.exists_widthOut_prog` (`SnakePieceIdent.lean`) and
  `TwoWay.exists_widthOut_finalProg_confined` (`SnakeFinalConf.lean`).  The two
  window transducers are `TwoWay.stopRight` (`SnakePiece.lean`) for a piece that
  runs from the left end of its window to the right end, and its mirror image
  (`SnakePieceRev.lean`) for a piece that runs the other way; the window of a
  piece is the interval between the record-breaking column and the furthest
  column of the excursion.  No separate notion of a snake with a marked source
  and target is needed.
* The *block function* — the function applied to one pair of neighbouring
  blocks by the map combinator — is regular (`TwoWay.isRegularFun_blockFun`), and
  applying the combinator to it on a correctly marked annotation computes the
  output of the run (`TwoWay.pairMap_blockFun_eq_runOut`), both in
  `SnakeBlock.lean`.  The annotation carries `2·(2k+1)` piece slots per letter,
  two per piece of the pair, because a letter occurs in the pair in which its
  block is the left one and in the pair in which it is the right one
  (`TwoWay.slot`).
* **A correct marking of every input exists**: `TwoWay.exists_isSnakeMarking`
  (`SnakeData.lean`), through the assembly of an annotated string out of purely
  numerical data (`TwoWay.isSnakeMarking_snakeAnn`, `SnakeAssemble.lean`).  This
  is the mathematical content of stage 1, and it is sorry-free.

What is left is only that the correct markings can be **recognised**.  It is
isolated as the single named statement

```lean
theorem exists_regular_snakeLang [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) :
    ∃ L : Language (A × TwoWay.SnakeDatum A Q K), L.IsRegular ∧
      (∀ u ∈ L, TwoWay.SnakeRel M K (homOf (TwoWay.snakeIn K) u)
        (homOf (TwoWay.snakeOutLet K) u)) ∧
      (∀ w : List A, ∃ u ∈ L, homOf (TwoWay.snakeIn K) u = w)
```

in `SnakeStage1.lean`, and it is the only `sorry` of the project that concerns
Section C.2.  It renders the book's sentence "*this stage can be implemented by
a rational function, since a nondeterministic automaton with output can guess
the record-breakers, and then check that they satisfy the conditions in the
definition*" literally: what has to be produced is the language of the
**checking** automaton.  The annotation is kept letter to letter — a letter of
the input together with a `TwoWay.SnakeDatum`, that is, the bit marking a block
boundary before (or, at the last letter, after) it and the data of the piece
slots — so that a position of an annotation is a position of the input; the
separators are inserted afterwards by the homomorphism `TwoWay.snakeOutLet`.

Everything that turns such a language into what the induction step consumes is
proved:

* `Transducers.isRationalRel_of_regular_nivat` (`PartB/GuessCheck.lean`): a
  regular language of annotations, read through one homomorphism and written
  through another, is a rational relation (one half of Nivat's theorem).  This
  is the "guess and check" step.
* `Transducers.exists_rationalFun_of_total_rel` (`PartB/UniformFun.lean`,
  Lemma B.2.5): a total rational relation contains the graph of a rational
  function.  This is why no functionality of the guessing has to be proved.
* `TwoWay.exists_rational_snakeRel`, `TwoWay.exists_snakeMarking` and
  `TwoWay.widthOut_eq_pairMap` (`SnakeStage1.lean`) chain the three together and
  hand the induction step of `SnakeReg.lean` the equation
  `widthOut M K w = pairMap (blockFun M (K-1) (2K+1)) (ann w)` for every nonempty
  `w`; the empty input is treated separately, by a case distinction over the
  regular language `{[]}`.

The tools for the missing regularity are in the project.  The conditions to be
checked on an annotation are conditions on the run of `M` at, and between, the
marked positions, and each of them is a regular property of the input marked at
one or at two positions:

* that the run visits a given cut in a given state — `TwoWay.visitLang_isRegular`
  (`TwoWayVisit.lean`);
* the order in time of the visits to *one* cut — `TwoWay.orderLang_isRegular`
  (`TwoWayOrder.lean`), available as a rational annotation through
  `TwoWay.exists_rational_visitOrder_annot` (`TwoWayAnnotOrd.lean`);
* the order in time of two configurations at *two different* marked positions —
  `RunMark.isRegular_beforeLang` with `RunMark.mem_beforeLang`
  (`RunMark.lean`).  This is precisely the comparison that the definition of the
  record-breaking columns makes: `xᵢ₊₁` is the least column whose first visit
  comes after the last visit to `xᵢ`.

Since the annotation is letter to letter, these become mso formulas with one and
with two free first-order variables by Theorem C.4.1 in the form of
`MarkLogic.exists_form_of_regular` and of `MarkLogic2`, and the conditions on an
annotation are first-order combinations of them: each condition relates a marked
position to the *next* marked position, and the marks are letters of the
annotated alphabet, so no quantification over sets and no unbounded counting is
needed.  The language of correct annotations is then mso-definable, hence
regular by `Transducers.isRegular_of_msoDefinable` (`MSOBuchi.lean`).  Two
things have to be added for that route to go through: the data `a`, `b`, `p` of
the pieces, which `TwoWay.exists_pieceData` currently produces by an existential
statement, have to be given explicitly in terms of the run (the states involved
are the states of the run at the boundary times of the excursions), and the
regular languages of marked *inputs* have to be pulled back along the projection
from the annotated alphabet to the input alphabet.

#### The proof of Theorem C.3.2

Both implications of Theorem C.3.2 are formalised, and every file that they use
is sorry-free.

The implication `regular ⊆ sst` is `Transducers.isSST_of_isRegularFun`
(`SSTRegular.lean`).  It follows the book: sst's are closed under
post-composition with each prime regular function, so, since a regular function
is a composition of primes, with every regular function; applying this to the
identity sst gives the statement.  The case of a rational function is reduced,
as in the book, to Krohn–Rhodes (Theorem A.2.2), because the naive product
construction is not copyless: keeping a register `X_q` for the image of the
content of `X` read from the state `q` breaks copylessness at a concatenation
`X ↦ Y Z`, since the state reached after the content of `Y` need not depend
injectively on `q`.  For a reversible machine it does, and for a flip-flop
machine the content of a register is split at its last reset
(`SSTMealyRev.lean`, `SSTMealyFF.lean`).  For map reverse and map duplicate the
content of a register is kept as a tuple of strings, indexed by the position of
the separators inside it (`SSTMapRev.lean`, `SSTMapDup.lean`).

The implication `sst ⊆ regular` goes, as in the book, through Theorem C.2.9: an
sst is simulated by a two-way transducer (`Transducers.isTwoWay_of_isSST`,
`SSTTwoWay.lean`), and a two-way transducer computes a regular function
(`Transducers.twoWay_isRegular`).  The simulation itself is proved sorry-free.
It has two parts.

* `SSTNorm.lean` normalises the sst.  A two-way transducer cannot see the state
  of the sst before the position of its head, so every input letter is
  annotated with that state by a Mealy machine; the annotation is rational and
  two-way transducers are closed under pre-composition with rational functions
  (Corollary C.2.7).  Moreover a register may occur several times in a final
  output string — the copyless restriction constrains only the register
  updates — so `K + 1` copies of every register are kept, where `K` bounds the
  number of register occurrences in a final output string; all copies hold the
  same value, and the occurrences in a final output string are given pairwise
  distinct copies (`Transducers.tagWith`).  The result is a `Transducers.NSST`
  computing the same function on the annotated input
  (`Transducers.exists_nsst_of_sst`).
* `SSTWalk.lean` traverses the register flow tree of a normalised sst.  The
  machine sweeps to the right end of the input and starts expanding the final
  output string; printing the letters it meets, it moves *left* when it meets a
  register, to expand that register's value from the update at the previous
  position, and *right* when the expansion of an update is finished.  The
  copyless restriction is exactly what makes the traversal possible: when the
  machine returns to a position in the state `ret y`, the place at which the
  expansion has to be resumed is determined by `y` and by the letter at that
  position, because `y` occurs at most once in the whole update applied there
  (`NSSTWalk.findReg_eq`), and in the final output string because the sst has
  been normalised.  Correctness is the pair of lemmas `NSSTWalk.scan` (a
  nested induction, on the position and on the length of the suffix being
  expanded) and `NSSTWalk.top`.

What keeps `Transducers.sst_iff_regular` from being proved outright is therefore
only the open induction step of the snake lemma, which is the single remaining
gap of Theorem C.2.9 (see *What is missing in Theorem C.2.9* above).  Once
`Transducers.boundedWidth_isRegular_step` is closed, Theorem C.3.2 is closed
with it, with no further work.

#### The proof of Theorem C.4.8

Both implications of Theorem C.4.8 (`Transducers.msoTransduction_iff_regular`)
are formalised, and no file used by either of them contains a `sorry`.

*From two-way transducers to mso transductions* (`TwoWayMSO.lean`).  As in the
book, the mso transduction simply writes down the semantics of the two-way
transducer: the elements of the output universe are the pairs (configuration of
the run, index of a letter in the string produced by that step), that is
`|Q| · (K+1)` copies of the input positions plus as many extra elements for the
configurations at the right end, where `K` bounds the length of the string
produced by one transition.  All the properties involved -- "the run visits the
state `q` at the marked position", "it produces the letter `b` there", "it
visits one marked target before the other" -- are checked by a deterministic
two-way automaton that simulates the run and stops at the first configuration
satisfying a trigger condition (`RunProbe.lean`), so the corresponding languages
of doubly marked strings are regular (Shepherdson, `TwoDFA.accepts_isRegular`,
and `RunMark.lean`), and Theorem C.4.1 turns them into formulas with one or two
free variables (`MarkLogic.lean`, `MarkLogic2.lean`).  The combinatorics of the
output list is in `FlatIndex.lean` and `RunElts.lean`.

*From mso transductions to regular functions* (`MSOReg.lean`).  The output
universe is first normalised (Lemma C.4.9, `MSONorm.lean`): the extra elements of
the linear type `τ = k · n + c` are attached to the first position of the input,
which leaves a single finite set of tags, a universe formula and letter formulas
with one free variable, and an order formula with two free variables.  A
two-way transducer then *walks* the output order (`WalkAut.lean`): it scans for
the first element, outputs its letter, and asks whether it is the last element,
whether its successor sits in the same position, or to the right, or to the
left; in the last two cases it walks in that direction and stops at the first
position where the automaton for "is the successor of" accepts.  The questions
are the mso formulas of `MSOWalkForms.lean`, whose meaning is expressed through
the increasing enumeration of the selected elements (`SortedEnum.lean`).  By
Lemma C.4.10 the unary questions are precomputed into the letters of a rational
letter-to-letter function `pre`, and the binary ones become regular languages of
infixes of `pre w`, read by a finite family of deterministic automata whose
product -- together with the last letter read, which is what answers the unary
question at the end of a rightward scan -- is the automaton of the walk
(`MSOWalkData.lean`).  Finally `f` is the composition of `pre` with the function
computed by the walking transducer; since that transducer need not halt on the
strings that are not of the form `pre w`, what is composed with `pre` is its
width-bounded output `TwoWay.widthOut`, a total function that agrees with the run
wherever the run halts and is regular by Theorem C.2.9.

This last step is the only reason why `Transducers.msoTransduction_iff_regular`
still depends on `sorryAx`: exactly as for Theorem C.3.2, the inclusion
`mso ⊆ regular` uses the hard half of Theorem C.2.9, whose single remaining gap
is the induction step `Transducers.boundedWidth_isRegular_step` of the snake
lemma (see *What is missing in Theorem C.2.9* above).  Once that step is closed,
Theorem C.4.8 is closed with it, with no further work.  The converse inclusion
`regular ⊆ mso`, `Transducers.isMSOTransduction_of_isTwoWay`, is proved outright
and depends only on `propext`, `Classical.choice`, `Quot.sound`.

#### The proof of Theorem C.4.16

Theorem C.4.16 is the first-order counterpart of Theorem C.4.4, and it is proved
outright, following the book's proof of Theorem C.4.4 with aperiodicity added
throughout and with Theorem C.4.11 and Lemma C.4.13 in place of Theorem C.4.1.

From a first-order relabelling to an aperiodic bimachine
(`Transducers.isAperiodicBimachine_of_isFORelabelling`, `FORelabBimach.lean`):
let `k` bound the quantifier rank of the finitely many formulas of the
relabelling.  The prefix automaton of the bimachine computes the `k`-type of the
prefix read so far and the suffix automaton the `k`-type of the suffix; both
transition functions are aperiodic, because `k`-types are (Lemma C.4.15,
`Transducers.transAperiodic_tpStep`).  By the compositionality of first-order
logic at a position (`Transducers.sat_const_iff_of_tp_split`, `FOPos.lean`, an
application of Claim C.4.14), whether a formula of the relabelling holds at a
position depends only on the `k`-type of the prefix, the letter and the `k`-type
of the suffix; so the index chosen at a position, hence the output block, is a
function of the bimachine's two states, which is exactly the output function of
a bimachine.  The one place where the two notions differ is bookkeeping: a
bimachine outputs one block per *gap*, one more than the number of positions,
while a relabelling outputs one block per position; the block of the last gap is
appended to the block of the last position, and the empty input is handled by
`emptyOut`.

From an aperiodic bimachine to a first-order relabelling
(`Transducers.isFORelabelling_of_isAperiodicBimachine`, `FOBimachRelab.lean`):
the indices of the relabelling are the quadruples `(q, a, s, last?)` consisting
of a state of the prefix automaton, a letter, a state of the suffix automaton and
a Boolean.  The formula of such an index says that the prefix strictly before the
position drives the prefix automaton to `q`, that the letter is `a`, that the
suffix strictly after the position drives the suffix automaton to `s`, and that
the position is (or is not) the last one.  The first conjunct is a first-order
sentence by Theorem C.4.11 (the language `{u | δ*(q₀,u) = q}` of an aperiodic
transition function is first-order definable), relativised to the positions below
the free variable with `MSO.relLt`; the third one is the same statement for the
*reverse* of such a language, which is first-order definable because first-order
definability is preserved by reversal (`Transducers.FODefinable.reverse`,
`FORev.lean`, proved through the `k`-type characterisation and the reversal
`tpRev` of a `k`-type), relativised with `MSO.relGt`.  Exactly one index holds at
each position, and its output block is the block of the corresponding gap, with
the block of the last gap again appended at the last position.

`#print axioms Transducers.foRelabelling_iff_aperiodicBimachine` reports only
`propext`, `Classical.choice`, `Quot.sound`, as it does on the two implications
`Transducers.isAperiodicBimachine_of_isFORelabelling` and
`Transducers.isFORelabelling_of_isAperiodicBimachine`.

#### Theorem C.4.17: what was removed and what remains

Theorem C.4.17 (the first-order transductions are exactly the compositions of
map reverse, map duplicate and first-order rational functions) has been
**removed from the formalised theorems at the user's request**.  Its statement,
and the statement of its open half, are kept only as comments in
`PartC/MSOOpen.lean`; neither is a Lean declaration any more.  The family of
primes `Transducers.FORegularFam` (`PartC/FOPrimeFam.lean`) and everything
proved about it are unaffected.

The inclusion from right to left -- every composition of primes is a first-order
transduction -- is **proved**, as
`Transducers.isFOTransduction_of_compClosure` in
`PartC/FOTransPrimeComp.lean`, by induction on `CompClosure`.  It is not free,
because in the mso case the corresponding inclusion is obtained *through*
Theorem C.4.8 and the definition of regular functions as compositions of primes,
and that route is unavailable in the first-order setting.  It rests on four
ingredients, each proved here directly:

* closure of first-order transductions under composition
  (`Transducers.isFOTransduction_comp`, `PartC/FOTransTr.lean` and
  `PartC/FOTransComp.lean`), by translating the formulas of the second
  transduction backwards along the first one -- the elements of the composite
  transduction are pairs of an element of the second one and an element of the
  first one, and every formula of the second transduction is evaluated on the
  intermediate string by substituting the formulas of the first;
* every first-order relabelling is a first-order transduction
  (`Transducers.isFOTransduction_of_isFORelabelling`, `PartC/FORelabTrans.lean`);
* map reverse is a first-order transduction
  (`Transducers.isFOTransduction_mapReverse`, `PartC/FOTransRev.lean`): the
  elements are the positions of the input, and the order `Transducers.revOrd`
  keeps the order of the blocks and reverses the order inside each block;
* map duplicate is a first-order transduction
  (`Transducers.isFOTransduction_mapDuplicate`, `PartC/FOTransDup.lean`): the
  elements are pairs `(copy, position)` with `copy : Bool`, and the order
  `Transducers.dupOrd` puts the first copy of a block before its second copy.

The block combinatorics that the last two need -- being a separator, being in the
same block, being between two positions -- is in `PartC/BlockPos.lean`, and the
first-order formulas expressing it in `PartC/BlockForm.lean`; the generic
machinery for producing `ITrans.Outputs` witnesses is in
`PartC/ITransBuild.lean`.

The inclusion from left to right -- every first-order transduction is a
composition of primes -- is no longer part of the formalisation; it was the only
`sorry` of Section C.4, and it has been removed together with Theorem C.4.17
itself.  The book does not prove it either: it only states
the result and leaves the proof "for a future edition of these notes", with a
sketch of what would be needed, namely first-order variants of (1) the lemma
saying that a string representation of the configuration graph of a two-way
transducer can be computed, and (2) the main step in the decomposition of two-way
transducers into primes, which says that the output string can be read off the
configuration graph by a composition of primes -- "the second one being more
technical".  In this project those two ingredients are the contents of the dozen
files behind Theorem C.4.8 and Theorem B.2.6, and their aperiodic counterparts
are not available; producing them is a development of the same order of
magnitude as the mso case.  What *is* available towards them is the relabelling
half of the picture, Theorem C.4.16 above, which identifies the first-order
rational functions appearing among the primes.

`#print axioms` on `Transducers.isFOTransduction_of_compClosure`,
`Transducers.isFOTransduction_comp`,
`Transducers.isFOTransduction_of_isFORelabelling`,
`Transducers.isFOTransduction_mapReverse` and
`Transducers.isFOTransduction_mapDuplicate` reports only `propext`,
`Classical.choice`, `Quot.sound`.

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

All statements compile.  Part A is proved in full.  **Part B is now proved in
full**: eighteen of its numbered results are proved outright (B.1.4, B.1.5,
B.1.7, B.2.3, B.2.4, B.2.5, B.2.6, B.2.7, B.3.5, B.3.6, B.4.1, B.4.3, B.4.4,
B.4.5, B.4.6, B.4.8, B.4.13), B.1.6 is proved from an explicit hypothesis
stating that the Post correspondence problem is undecidable, and the four
remaining decidability statements (B.3.3, B.3.4, B.3.7, B.4.2) are proved from
the single effectivity hypothesis `EffectiveWeightedEvalEq` of
`PartB/Effective.lean` — see the subsection *The four conditional results of
Part B* above for what that hypothesis says, why it is true, and why it cannot
currently be discharged inside Mathlib (its `Primrec`/`Computable` API provides
no arithmetic on `ℤ` or `ℚ`).  The effective Schützenberger bound, which these
four results also need and which used to be a second hypothesis, is proved in
`PartB/WeightedBound.lean`.  No file of
Part B contains a `sorry`, and every numbered result of Part B depends only on
`propext`, `Classical.choice`, `Quot.sound`.
In Part C,
Theorem C.1.1, Lemmas C.1.2 and C.1.3,
Theorem C.2.2, **Theorem C.2.5**, Lemma C.2.6, **Corollary C.2.7**,
**Corollary C.2.8**, **Lemma C.2.10**, **Claim C.2.11**, **Theorem C.4.1**,
**Lemma C.4.2**, **Theorem C.4.4**, **Claim C.4.6**, **Lemma C.4.10**,
**Theorem C.4.11**, **Lemma C.4.13**, **Theorem C.4.16** and
Lemma C.4.15 are
proved.  Theorem C.4.1 (Büchi-Elgot-Trakhtenbrot), Lemma C.4.2, Theorem C.4.4
(rational functions are exactly the mso relabellings), Claim C.4.6,
Lemma C.4.10 (the precomputation of a finite family of formulas by a
letter-to-letter rational function), Theorem C.4.11 (a language is first-order
definable if and only if it is recognised by an aperiodic dfa), Lemma C.4.13
(two strings have the same `k`-type if and only if they satisfy the same
first-order sentences of quantifier rank at most `k`) and Theorem C.4.16 (the
first-order relabellings are exactly the functions computed by aperiodic
bimachines)
are proved outright: no file they use contains a `sorry`, and each of them
depends only on `propext`, `Classical.choice`, `Quot.sound` (checked again on a
clean build of the whole project, `lake build` with no errors, and with
`#print axioms`; Lemma C.4.15 needs only `propext` and `Quot.sound`).  Both
directions of Theorem C.4.4, and Lemma C.4.10, go through bimachines
(Theorem B.2.3) and through the doubly marked alphabet `Mark2 A = A × 2 × 2`,
for which Lemma C.4.2 gives the regular language `markedSat2 φ` of the marked
strings satisfying a formula; Claim C.4.5 of the book is the internal step of
Theorem C.4.4 and is formalised, as `Transducers.RatRelab.exists_form`, for the
index of a bimachine rather than for the transitions of an unambiguous
transducer.  So that the state of the section is visible file by file, the
numbered results of Section C.4 that are
still open have been moved, unchanged, from `PartC/MSO.lean` to
`PartC/MSOOpen.lean`, which `PartC/MSO.lean` imports: `PartC/MSO.lean` now
contains exactly the ten proved results of Section C.4 (C.4.1, C.4.2, C.4.4,
C.4.6, C.4.8, C.4.10, C.4.11, C.4.13, C.4.15, C.4.16) and no `sorry`, while
every name of Section C.4 is still available from `RequestProject.PartC.MSO` as
before; `PartC/MSOOpen.lean` now declares nothing at all.  Of
**Theorem C.4.17** (the first-order transductions are exactly the compositions
of map reverse, map duplicate and first-order rational functions), which has
been removed from the formalised theorems at the user's request, the inclusion
from compositions of primes to first-order transductions is proved
(`Transducers.isFOTransduction_of_compClosure`, `FOTransPrimeComp.lean`,
depending only on `propext`, `Classical.choice`, `Quot.sound`), on top of the
closure of first-order transductions under composition
(`FOTransTr.lean`, `FOTransComp.lean`) and of the three primes
(`FORelabTrans.lean`, `FOTransRev.lean`, `FOTransDup.lean`, with the block
combinatorics of `BlockPos.lean`, `BlockForm.lean` and the tools of
`ITransBuild.lean`).  The converse inclusion, which was the only `sorry` of
Section C.4, has been removed along with the theorem; the book gives no proof of
it either -- see *Theorem C.4.17: what was removed and what remains* above.
Lemma C.4.13 is proved by the Ehrenfeucht-Fraïssé argument of the book: the
compositionality of first-order logic (Claim C.4.14, `FOComp.lean`) gives one
direction, and Hintikka sentences of quantifier rank `k`, built by induction
from the finitely many `k`-types (`FOHintikka.lean`, using Lemma C.4.15), give
the other.  For Theorem C.4.11, the easy direction runs the finite aperiodic
automaton of `k`-types (`FOTypeDFA.lean`), and the hard one follows the book
through the aperiodic Krohn-Rhodes Theorem A.2.8: the Mealy machine of the dfa
has the transition function of the dfa, so aperiodicity is literally the
hypothesis of `Transducers.krohn_rhodes_flipFlop`, and the resulting composition
of flip-flops is first-order definable because flip-flops are
(`FOFlipFlop.lean`, `FOMealy.lean`) and first-order definable Mealy machines are
closed under composition, by substitution of formulas (`FOSubstRel.lean`).
Of **Theorem C.4.8** (mso transductions compute exactly the regular functions)
both implications are now formalised, and no file they use contains a `sorry`:
`regular ⊆ mso` is `Transducers.isMSOTransduction_of_isTwoWay`, which is proved
outright (axioms `propext`, `Classical.choice`, `Quot.sound`), and `mso ⊆
regular` is `Transducers.MSOReg.isRegularFun_of_isMSOTransduction`, which
normalises the type τ (Lemma C.4.9, `MSONorm.lean`), precomputes the questions of
the walk by Lemma C.4.10 and composes the resulting rational function with the
walking two-way transducer, appealing to Theorem C.2.9 for the regularity of the
latter; `Transducers.msoTransduction_iff_regular` therefore still depends on
`sorryAx`, through the single open statement of Section C.2 — see *The proof of
Theorem C.4.8* above.  Of **Theorem C.3.2** (sst = regular) both implications are now
formalised and every file they use is sorry-free: `regular ⊆ sst` is
`Transducers.isSST_of_isRegularFun`, which is proved outright, and `sst ⊆
regular` is proved from Theorem C.2.9, the simulation of an sst by a two-way
transducer (`Transducers.isTwoWay_of_isSST`) being itself proved outright;
`Transducers.sst_iff_regular` therefore still depends on `sorryAx`, through the
single open statement of Section C.2 — see *The proof of Theorem C.3.2* above.
In Part D, Theorem D.0.19 is proved.  The remaining results are
statements only (`sorry`).  Exercises and examples of the book are not included.

Of Theorem C.2.9 (two-way transducers compute exactly the regular functions),
the right-to-left implication is proved — it is Corollary C.2.8 — and the
left-to-right implication, isolated as `Transducers.twoWay_isRegular`, is still
open; `Transducers.twoWay_iff_regular` is proved from it and from
Corollary C.2.8.  That implication is reduced, sorry-free, to the book's snake
lemma `Transducers.boundedWidth_isRegular` (`SnakeReg.lean`).  The snake lemma
is proved by induction on the width `k`; its two base cases `k = 0` and `k = 1`
(`Transducers.TwoWay.widthOut_zero_isRegular` and
`Transducers.TwoWay.widthOut_one_isRegular`) are proved in full in
`SnakeBase.lean`, and the only remaining `sorry` of Section C.2 is the induction
step `Transducers.boundedWidth_isRegular_step` (`SnakeReg.lean`).  The
combinatorics of the width induction that the book proves the step by —
record-breaking columns, loop and progress parts, and the splitting of a run of
width `k` into pieces of width `k - 1` together with the corresponding
factorisation of its output — is proved in full in `SnakeWalk.lean`,
`SnakeRec.lean` and `SnakeLoop.lean`, and the confinement of those pieces to
two consecutive blocks of the input in `SnakeConfine.lean`; the book's
"reverse the snake" is `SnakeMirror.lean`; the identification of a piece with
the whole run of a window transducer, to which the induction hypothesis
applies, is in `SnakeLocal.lean`, `SnakePiece.lean` and `SnakePieceRev.lean`;
the gluing of the pieces, which is stages 1--3 of the book's proof, is the
neighbouring-block map combinator `Transducers.RegPair.isRegularFun_pairMap`
(`RegPair.lean`, on top of the bilateral rewritings of `RatBi.lean`); and the
order in time of the visits of a run to a cut, on which the definition of the
record-breaking columns rests, is a regular property available as a rational
annotation (`TwoWayOrder.lean`, `TwoWayAnnotOrd.lean`).  The identification of
the individual pieces inside a block is proved as well
(`SnakeExc.lean`, `SnakeParts.lean`, `SnakePieceIdent.lean`,
`SnakeFinalConf.lean`), so is the regularity of the block function and the fact
that the map combinator applied to it on a correct marking computes the output
of the run (`SnakeBlock.lean`, `SnakeRegTools.lean`), and so is the **existence
of a correct marking of every input** (`SnakeAssemble.lean`, `SnakeData.lean`,
`Transducers.TwoWay.exists_isSnakeMarking`, which depends only on `propext`,
`Classical.choice`, `Quot.sound`).  What is left is one statement,
`Transducers.TwoWay.exists_regular_snakeLang` (`SnakeStage1.lean`): that the
correct markings can be *recognised*, that is, that they form a regular language
of letter-to-letter annotated inputs.  Everything that turns such a language into
the regular marking function that the induction step consumes is proved --
"guess and check" (`PartB/GuessCheck.lean`) and uniformisation
(`PartB/UniformFun.lean`).  See *What is missing in Theorem C.2.9* above.  Claim C.2.11 is proved in a corrected form:
the statement as printed is false on the empty input, see *An error in
Claim C.2.11* above.

Corollary C.2.8 is printed in the book as the inclusion `two-way ⊆ regular`,
which is a typo: its proof establishes `regular ⊆ two-way`, and the printed
inclusion is the hard half of Theorem C.2.9.  The corollary is therefore
formalised as `Transducers.regularFun_isTwoWay` (`regular ⊆ two-way`) and proved
in full, while the printed inclusion is the still open
`Transducers.twoWay_isRegular`, the left-to-right implication of
`Transducers.twoWay_iff_regular`.  See *A typo in Corollary C.2.8* above.

`#print axioms` on `Transducers.twoWay_comp`, `Transducers.regularFun_isTwoWay`,
`Transducers.isTwoWay_of_isRegularFun`,
`Transducers.regular_closure_properties`, `Transducers.sum_of_regular`,
`Transducers.TwoWay.runOutput_eq_loopProgOut`,
`Transducers.Walk.walk_splitsInto_pred`,
`Transducers.TwoWay.run_splitsInto_pred`,
`Transducers.TwoWay.runOutput_splits`,
`Transducers.TwoWay.widthOut_one_eq`,
`Transducers.TwoWay.widthOut_zero_isRegular`,
`Transducers.TwoWay.widthOut_one_isRegular`,
`Transducers.Walk.loop_confined`,
`Transducers.Walk.progress_confined`,
`Transducers.TwoWay.stepCfg_mirror`,
`Transducers.TwoWay.reaches_mirror_iff`,
`Transducers.TwoWay.widthOut_stopRight`,
`Transducers.TwoWay.orderLang_isRegular`,
`Transducers.TwoWay.exists_rational_visitOrder_annot`,
`Transducers.isRationalFun_biEval`,
`Transducers.isRationalFun_biFilter`,
`Transducers.isRationalFun_biMarkSep`,
`Transducers.RegPair.isRegularFun_pairMap`,
`Transducers.isSST_of_isRegularFun`,
`Transducers.exists_nsst_of_sst`,
`Transducers.isTwoWay_of_nsst`,
`Transducers.isTwoWay_of_isSST`,
`Transducers.isAperiodicBimachine_of_isFORelabelling`,
`Transducers.isFORelabelling_of_isAperiodicBimachine`,
`Transducers.foRelabelling_iff_aperiodicBimachine`,
`Transducers.isFOTransduction_comp`,
`Transducers.isFOTransduction_of_isFORelabelling`,
`Transducers.isFOTransduction_mapReverse`,
`Transducers.isFOTransduction_mapDuplicate` and
`Transducers.isFOTransduction_of_compClosure`
reports only `propext`, `Classical.choice`, `Quot.sound`.
(`Transducers.twoWay_iff_regular`, `Transducers.twoWay_isRegular`,
`Transducers.sst_iff_regular` and `Transducers.msoTransduction_iff_regular`
still depend on `sorryAx`, through
`Transducers.boundedWidth_isRegular_step`.)
