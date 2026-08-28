# Theorems of *Transducers* (M. Bojańczyk) — formal statements

This project contains Lean 4 statements of the theorems, lemmas, corollaries and
claims of the book `main.pdf`, together with the definitions needed to state
them.  Everything lives in the namespace `Transducers`.

A result of the book is identified by its LaTeX label, in backticks, as in
Theorem `thm:decidable-equivalence-regular`, and not by its number, which
changes whenever the LaTeX sources are edited.  Environments of the book that
carry no label are given a placeholder tag with the prefix `nolabel:`, and
sections, which carry no labels either, are referred to by their titles.  See
`LABELS.md` for the convention and for the dictionary of labels.

The *exercises* of the book are not numbered results of the main text, so they
are not listed here; they are listed in `EXERCISES.md`, in the same style.

The correspondence between the labels and the Lean declarations is itself
checked by Lean, in `RequestProject/Labels.lean`: every formalised result gets
an alias whose Lean name is its label, and an assertion that records that the
result is proved outright — `assert_no_sorry` fails if the declaration depends on
`sorryAx` or on any axiom other than `propext`, `Classical.choice`, `Quot.sound`.
So the names and the statuses in the tables below cannot go stale without
breaking the build.

Of the **100 theorem-like environments** of the book, 20 definitions and 72
results are formalised, and 8 are not; of the 72, **66 are proved outright** and
6 are proved from an explicit hypothesis.  **Parts A, B and D are proved in
full**, and so is Part C apart from Theorem `thm:decidable-equivalence-regular`,
which is one of the six.  Nothing that is formalised is left unproved: there is
no `sorry` and no `axiom` anywhere in the project.  The `## Status` section at
the end gives the counts part by part, the six hypotheses, the eight environments
that are not formalised, and the warnings that `lake build` still emits.

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
  Exercises.lean Exercises/    -- the exercises of the book (indexed in `EXERCISES.md`)
  Labels.lean                  -- the results of the book indexed by their LaTeX labels
  Main.lean                    -- global options used by the project
```

| File | Contents |
| --- | --- |
| `Common/Basic.lean` | continuity, prefix/length preservation, aperiodicity, map lifting, left distance, closure under composition |
| `Common/Aux.lean` | auxiliary lemmas on lists and on iterating a function on a finite set |
| `Common/RegularAux.lean` | regularity of the auxiliary languages used in Part B |
| `Exercises/Intro.lean`, `Exercises/IntroAux.lean` | the exercises of the introduction and the auxiliary facts their solutions take for granted — see `EXERCISES.md` |
| `PartA/MealyBasic.lean` | Mealy machines: definitions, runs, state transformations, products, the associated dfa |
| `PartA/PrimeClosure.lean` | closure properties of compositions of prime Mealy machines (pairing the output with the input) |
| `PartA/MapLift.lean` | the map lifting: its description position by position, and Lemma `lem:map-lifting-decomposition-mealy` |
| `PartA/StateTrans.lean` | the state transformation transducer of a pre-automaton and the proof of Lemma `lem:Mealy-map-lifting` (the induction of the Krohn-Rhodes Theorem) |
| `PartA/FlipFlopClosure.lean` | closure properties of compositions of flip-flop Mealy machines (the flip-flop analogues of `PrimeClosure.lean` and Lemma `lem:map-lifting-decomposition-mealy`) |
| `PartA/StateTransAperiodic.lean` | the aperiodic case of the Krohn-Rhodes construction: condition (*) is inherited by the smaller pre-automata, and all the machines are flip-flops |
| `PartA/Statements.lean` | Part A: Mealy machines |
| `Exercises/PartA.lean` | the exercises of Part A (`mealy.tex` and `krohn-rhodes.tex`), which are not numbered results of the book and are indexed in `EXERCISES.md`, not here |
| `PartB/LabAut.lean` | automata with labelled transitions, nfas with output, rational relations and functions |
| `PartB/Atomize.lean`, `PartB/OutLang.lean`, `PartB/EpsElim.lean`, `PartB/RatComp.lean`, `PartB/RatCont.lean`, `PartB/HomComplement.lean`, `PartB/LenNormalForm.lean`, `PartB/MealyChar.lean`, `PartB/Typing.lean`, `PartB/SeqChar.lean`, `PartB/Unambig.lean`, `PartB/Uniform.lean`, `PartB/Bimachine.lean`, `PartB/RatBimach.lean`, `PartB/PrimeRat.lean`, `PartB/BimachPrime.lean` | the constructions used in the proofs of Part B (see the list at the end of the Part B section below) |
| `PartB/UniformFun.lean` | uniformisation in the form of a function (`Transducers.exists_rationalFun_of_total_rel`): a total rational relation contains the graph of a rational function |
| `PartB/GuessCheck.lean` | "guess and check", one half of Nivat's theorem (`Transducers.isRationalRel_of_regular_nivat`): a regular language of annotated strings, read through one homomorphism and written through another, is a rational relation |
| `PartB/Codes.lean` | finite descriptions (codes) of nfas with output, and the formalisation of (un)decidability statements |
| `PartB/PCPRed.lean` | the Post correspondence problem and the reduction proving Theorem `thm:undecidable-equivalence-rational-relations` |
| `PartB/PathComb.lean` | combinatorics of paths: splitting at a visited state, pigeonhole extraction of a short loop, replacement by a simple path |
| `PartB/LenDec.lean` | the decision procedure for Lemma `lem:decide-if-length-preserving` and its correctness and computability |
| `PartB/Effective.lean` | the effectivity hypothesis `EffectiveWeightedEvalEq` from which Theorems `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata` and `thm:decide-if-mealy` are proved, and the statement `EffectiveWeightedBound` of the effective Schützenberger bound (which is *proved*, in `PartB/WeightedBound.lean`) |
| `PartB/WeightedBound.lean` | the effective Schützenberger bound: the useful states of the normalised automaton are covered by an explicit list, so the dimension of the linear representation, and hence the length bound `wcodeBound`, is a primitive recursive function of the code (`effectiveWeightedBound`) |
| `PartB/WCodes.lean` | codes of weighted automata over `ℚ` (`WCode`, `wcodeAut`, `wcodeEval`, `WCodeValid`) |
| `PartB/CodeAtom.lean`, `PartB/CodeMerge.lean`, `PartB/CodeAlpha.lean`, `PartB/CodeEps.lean`, `PartB/RunList.lean` | the letter-atomic normal form of a code, the alphabets of a code, its value on the empty input, and the enumeration of the runs of a letter-atomic code |
| `PartB/Iota.lean`, `PartB/PairWeighted.lean`, `PartB/PairWeightedEval.lean`, `PartB/PairPrimrec.lean` | the numerical encoding of strings and the product weighted automaton reducing Theorem `thm:equivalence-rational-functions` to Theorem `thm:equivalence-weighted-automata` |
| `PartB/WeightedDec.lean`, `PartB/RatEqDec.lean`, `PartB/MealyDec.lean` | the decision procedures of Theorems `thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata`, of Theorem `thm:equivalence-rational-functions` and of Theorem `thm:decide-if-mealy` |
| `PartB/PrefixCodes.lean`, `PartB/CodeRat.lean` | the two codes reducing prefix preservation to an equality of rational functions, and the rational function described by a code over its own finite alphabets |
| `PartB/RationalStatements.lean` | Sections *Rational relations* to *Rational functions*: rational relations, rational functions, bimachines |
| `PartB/WeightedNF.lean`, `PartB/WeightedLinRep.lean`, `PartB/WeightedPrecomp.lean`, `PartB/WeightedRegular.lean`, `PartB/WeightedZero.lean` | normal forms and linear representations of weighted automata, the proofs of Lemma `lem:closure-weighted-automata-precomposition` and Theorem `thm:characterisation-rational-functions-weighted-automata`, and Schützenberger's zeroness criterion |
| `PartB/WeightedStatements.lean` | Sections *Rational relations and weighted automata* to *Machine independent characterisations*: weighted automata, machine independent characterisations |
| `PartC/ContAux.lean` | continuity: closure under composition, letter-to-letter maps, reversal, duplication, and the map lifting (Lemma `lem:map-lifting-continuous`) |
| `PartC/TwoDFA.lean` | deterministic two-way automata and Shepherdson's Theorem (their languages are regular) |
| `PartC/TwoWayCont.lean` | two-way transducers (Definition `def:two-way-transducer`) and their continuity (Theorem `thm:continuity-2dfas`) |
| `PartC/TwoWayPrecomp.lean` | pre-composition of a two-way transducer with a Mealy machine (Lemma `lem:2dfa-precomposition-with-mealy`), via the Krohn-Rhodes Theorem: the reversible case, the flip-flop case, and pre-composition with reversal |
| `PartC/TwoWayHom.lean`, `PartC/TwoWayBlock.lean`, `PartC/TwoWayErase.lean`, `PartC/TwoWayRat.lean` | pre-composition of a two-way transducer with a homomorphism and with an arbitrary rational function (Corollary `cor:2dfa-closure-under-composition`) |
| `PartC/TwoWayRun.lean`, `PartC/TwoWayVisit.lean`, `PartC/TwoWayAnnot.lean`, `PartC/TwoWayAnnotBim.lean`, `PartC/TwoWayCompAux.lean`, `PartC/TwoWayCompPred.lean`, `PartC/TwoWayComp.lean`, `PartC/TwoWayCompFinal.lean` | the composition of two two-way transducers (Theorem `thm:composition-of-two-way-transducers`) |
| `PartC/ConfGraph.lean`, `PartC/ConfGraphRun.lean`, `PartC/ConfGraphAnnot.lean`, `PartC/ConfGraphReg.lean` | the alphabet `C` and the string representation of the reachable configuration graph of a two-way transducer, its agreement with the run semantics, and the two lemmas of the book about it (Lemmas `lem:compute-configuration-graph` and `lem:check-if-output-string-of-configuration-graph-belongs-to-L`) |
| `PartC/TwoWaySweep.lean`, `PartC/TwoWayRegular.lean` | explicit two-way transducers for the identity, for post-composition with a letter-to-letter map, and for map reverse and map duplicate; every regular function is computed by a two-way transducer (Corollary `cor:2dfa-computes-all-regular-functions`) |
| `PartC/RegularDef.lean` | the prime regular functions and the regular functions (Definition `def:regular-functions`), moved here unchanged from `PartC/Statements.lean`, together with their elementary closure properties |
| `PartC/RegCodeSan.lean` | codes of two-way transducers (`TwoWayCode`, `twoWayCodeAut`, `twoWayCodeRel`, `TwoWayCodeTotal`, moved here unchanged from `PartC/Statements.lean`), and the fact that a coded transducer is blind to the letters that do not occur in its table: renaming them does not change the computed relation (`Transducers.RegDec.twoWayCodeRel_map`), which is what makes the equivalence test of Theorem `thm:decidable-equivalence-regular` a finite check |
| `PartC/RegCodeBound.lean` | the existence of the equivalence bound of Theorem `thm:decidable-equivalence-regular` for two codes (`Transducers.exists_twoWayCode_bound`): the transducer of a code read over the finite alphabets and the finite state set that occur in it, the step-by-step correspondence between its runs and those of the coded transducer, the determinism of two-way transducers (`TwoWay.computes_unique`), and the application of `Transducers.regularFun_eq_of_short` |
| `PartC/EffectiveReg.lean` | the two effectivity hypotheses `EffectiveTwoWayEvalEq` and `EffectiveTwoWayBound` from which Theorem `thm:decidable-equivalence-regular` is proved, with their justification |
| `PartC/RegEqDec.lean` | the decision procedure of Theorem `thm:decidable-equivalence-regular`: compare the two codes on the strings of length at most the bound over the letters of the two codes together with one fresh letter |
| `PartC/RatBuild.lean`, `PartC/RatTools.lean`, `PartC/RatSeq.lean` | a bimachine-based builder for rational functions, and the rational functions used by Lemma `lem:regular-closure-properties` and Claim `claim:conditional` (constants, `cons`, letter-to-letter maps, homomorphisms, conditionals on a regular language, and sequential letter-by-letter transducers) |
| `PartC/MapLiftAux.lean`, `PartC/MapLiftRat.lean`, `PartC/MapLiftPrime.lean`, `PartC/RegMapLift.lean` | closure of the regular functions under map lifting (first item of Lemma `lem:regular-closure-properties`): the map lifting of a rational function is rational, the map liftings of map reverse and map duplicate are regular, and the general case follows by induction on the composition tree |
| `PartC/SumShape.lean`, `PartC/SumPrime.lean`, `PartC/SumReg.lean`, `PartC/RegSum.lean` | Claim `claim:conditional`: the *marked sum* of two regular functions, its compatibility with composition, its prime base cases, and the passage from the marked sum to the sum of the claim (with the counterexample `Transducers.not_sum_of_regular_nil` to the claim as printed) |
| `PartC/RegClosure.lean` | closure of the regular functions under concatenation and under conditionals over a regular language (second and third items of Lemma `lem:regular-closure-properties`) |
| `PartC/SnakeWidth.lean` | the *width* of the run of a two-way transducer (the maximal number of visits to a single column) and the bound `width ≤ |Q|` for a halting run |
| `PartC/SnakeBase.lean` | the base cases `k ≤ 1` of the induction on the width in the snake lemma: a halting run of width one never moves left, so it is a left-to-right pass, its output is computed by a bimachine, and the inputs on which it is such a pass form a regular language (`TwoWay.widthOut_zero_isRegular`, `TwoWay.widthOut_one_isRegular`) |
| `PartC/SnakeReg.lean` | the book's snake lemma, as the induction on the width `Transducers.snakeReg` over the predicate `Transducers.SnakeReg` ("the width-`k` output function of *every* two-way transducer over *every* finite alphabet is regular") — the base cases `k ≤ 1` come from `SnakeBase.lean` and the induction step `Transducers.boundedWidth_isRegular_step` (from `SnakeReg (k+1)` to `SnakeReg (k+2)`) is proved from the checking automaton of stage 1 — together with `Transducers.boundedWidth_isRegular` and the reduction of the hard half of Theorem `thm:2dfa-decomposition-into-primes` to it (`Transducers.isRegularFun_of_isTwoWay`) |
| `PartC/SnakeWalk.lean` | combinatorics of the trajectory of a run, seen as a walk: intermediate values, first and last visit to a column, visit counts, record-breaking columns, and the width bounds for the progress parts and for the two halves of a one-sided loop |
| `PartC/SnakeRec.lean` | the sequence of record-breaking columns of a walk, its stabilisation, the increasing chain of times it defines, and the resulting decomposition of the output of a run into the outputs of the loop parts and of the progress parts |
| `PartC/SnakeConfine.lean` | the confinement of the pieces of the record-breaker decomposition: after the last visit to a record-breaking column the walk stays strictly to its right (`Walk.recSeq_lt_of_recLast_lt`), up to the first visit to one it stays weakly to its left (`Walk.le_recSeq_of_le_recFirst`), so the loop and the progress parts of the `i`-th record-breaker are contained in the columns `x (i-1) < · ≤ x (i+1)` (`Walk.loop_confined`, `Walk.progress_confined`), i.e. in the book's block `wᵢ₋₁ # wᵢ` |
| `PartC/SnakeMirror.lean` | mirroring a two-way transducer (`TwoWay.mirror`: swap the two letters adjacent to the head and the two directions), an involution that turns every run into the mirrored run on the reversed input, with the same output (`TwoWay.stepCfg_mirror`, `TwoWay.reaches_mirror_iff`); this is the book's "reverse the snake" |
| `PartC/SnakeLoop.lean` | splitting a looping part of a walk into pieces of smaller width (intermediate visits to the base column, then the furthest column of each one-sided loop, the left-hand case being reduced to the right-hand one by reflecting the walk), and the induction step of the snake lemma at the level of runs: `Transducers.TwoWay.runOutput_splits` |
| `PartC/SnakeLocal.lean`, `PartC/SnakePiece.lean`, `PartC/SnakePieceRev.lean` | a piece of a run seen as a complete run on a window of the input: the window transducer `TwoWay.withContext`, the transducer `TwoWay.stopRight` that halts on reaching the right end of the window, and the identification of a left-to-right (resp. right-to-left, by mirroring) piece with the whole run of such a transducer, so that the induction hypothesis of the snake lemma applies to it (`TwoWay.widthOut_stopRight`) |
| `PartC/SnakeExc.lean` | the *excursions* of a record-breaking column: the intermediate visits `excT` to the column during its loop part, the time `excS` at which each excursion is at its furthest column `excC`, and the resulting cutting of the loop part into the `2k` halves of excursions |
| `PartC/SnakeParts.lean` | the output of a halting run of width at most `k` as the concatenation of the `2k+1` pieces of each record-breaker (`TwoWay.blockOut`, `TwoWay.runOut_eq_partsOut`) |
| `PartC/SnakePieceIdent.lean` | the identification of a piece with the whole run of a window transducer on the interval between the record-breaking column and the furthest column of the excursion (`TwoWay.exists_widthOut_excHalves` for the two halves of an excursion, `TwoWay.exists_widthOut_prog` for a progress part) |
| `PartC/SnakeFinalConf.lean` | the same for the progress part after the last record-breaker, which reaches the end of the input (`TwoWay.exists_widthOut_finalProg_confined`) |
| `PartC/SnakeRegTools.lean` | the regular-function tools used to build the block function: cutting a factor out of an annotated pair of blocks and reading parameters off its first letter, both by bimachines |
| `PartC/SnakeBlock.lean` | the *block function* of stages 2--4: the annotated alphabet `TwoWay.SnakeLet` with its `2·(2k+1)` piece slots (`TwoWay.slot`), the output `TwoWay.pieceOut` of a piece with given parameters, the output `TwoWay.pieceOutput` of the `r`-th piece of a block, the regularity of the block function (`TwoWay.isRegularFun_blockFun`), the notion of a correct marking (`TwoWay.IsSnakeMarking`) and the fact that the neighbouring-block map combinator applied to the block function on a correct marking computes the output of the run (`TwoWay.pairMap_blockFun_eq_runOut`) |
| `PartC/SnakeAssemble.lean` | the assembly of a correct marking out of purely numerical data — the cutting points of the blocks and, for every pair of blocks and every slot, the window and the parameters of that piece (`TwoWay.snakeAnn`, `TwoWay.isSnakeMarking_snakeAnn`) |
| `PartC/SnakeData.lean` | the numerical data of the pieces of a run and the existence of a correct marking of every nonempty input whose run halts with width at most `k` (`TwoWay.snakeY`, `TwoWay.exists_pieceData`, `TwoWay.exists_isSnakeMarking`) |
| `PartC/SnakeStage1.lean` | the book's stage 1: the guess-and-check formulation of the marking (`TwoWay.SnakeRel`, `TwoWay.exists_regular_snakeLang`, `TwoWay.exists_rational_snakeRel`, `TwoWay.exists_snakeMarking`) and the equation `widthOut M K w = pairMap (blockFun …) (ann w)` that the induction step consumes (`TwoWay.widthOut_eq_pairMap`) |
| `PartC/SnakeWinRun.lean` | the converse of the locality results of `SnakeLocal.lean`, `SnakePiece.lean` and `SnakePieceRev.lean`: from a run of the *window* transducer on a window back to the corresponding piece of the run of `M` and to the output it produces, for each of the four kinds of piece (`TwoWay.exists_outRange_kind_one` … `kind_four`).  This is the direction that the checking automaton of stage 1 needs |
| `PartC/SnakeChain.lean` | telescoping a chain of pieces: the concatenation of the outputs of the pieces of a chain is the output of the run (`TwoWay.runOut_of_chain`), and the reindexing of a doubly indexed family of pieces as a single chain (`Transducers.flatMap_range_mul`) |
| `PartC/SnakeChkRel.lean` | what the marking of stage 1 actually has to satisfy (`TwoWay.SnakeRel`), which is weaker than being a correct marking of the record-breaker decomposition and is what lets the checking automaton verify a chain of pieces instead |
| `PartC/SnakeRunLang.lean` | regular languages describing the run of a two-way transducer on its whole input: the inputs on which it halts, those on which it reaches the right end in a given state, and those on which it has width at most `k`; all by simulation with a deterministic two-way automaton (`RunProbe.lean`), the width by marking the column and removing the mark with `SnakeForall.lean` |
| `PartC/SnakeForall.lean` | universal closure of a regular relation on two marked positions: the conjunction, over all pairs of consecutive marked positions, of a regular condition on the doubly marked string is regular, by the mso sentence `∀x₀∀x₁ φ(x₀,x₁)` and Theorem `thm:mso-logic-languages` |
| `PartC/SnakeLocLang.lean` | two elementary families of regular languages used by the checking automaton: every pair of consecutive letters satisfies a fixed condition (`SnakeLoc.PairsOK`), and every letter strictly between the two marks of a doubly marked string does (`SnakeLoc.MidOK`) |
| `PartC/SnakeChkWin.lean`, `PartC/SnakeChkData.lean`, `PartC/SnakeChkEnc.lean`, `PartC/SnakeChkRead.lean`, `PartC/SnakeChkBuild.lean`, `PartC/SnakeChkMain.lean` (with `SnakeChkAcc.lean`, `SnakeChkAnn.lean`, `SnakeChkBlkIdx.lean`, `SnakeChkBlocks.lean`, `SnakeChkComp.lean`, `SnakeChkCtx.lean`, `SnakeChkCut.lean`, `SnakeChkFlag.lean`, `SnakeChkGeom.lean`, `SnakeChkReadData.lean`, `SnakeChkSplit.lean`, `SnakeChkStruct.lean`, `SnakeChkTools.lean`, `SnakeChkVerify.lean`) | the **checking automaton of stage 1**: the window condition of one piece and its regularity (`TwoWay.Chk.WinCond`, `TwoWay.Chk.isRegular_winCond`), the *chain of pieces* that the automaton verifies (`TwoWay.Chk.ChainData`) together with the theorem that the outputs of the pieces of a chain concatenate to the output of the run (`TwoWay.Chk.runOut_of_chainData`), the annotated alphabet, and the proof that the accepted annotations form a regular language containing an annotation of every input (`TwoWay.exists_regular_snakeLang`) |
| `PartC/SnakeChkPieceWin.lean` | the window condition of each of the four kinds of piece, derived from the run (`TwoWay.Chk.winCond_kind_one` … `winCond_kind_four`), with the two states of a piece named as the states of the run at its two ends (`TwoWay.qAt`) |
| `PartC/SnakeChkCross.lean` | one piece of the chain as a package: the window, the context letters, the two states, the kind, the two cuts and the window condition, for a piece that crosses its window (`TwoWay.Chk.CrossOK`, `TwoWay.Chk.exists_crossOK`) and for one that halts inside it (`TwoWay.Chk.HaltOK`, `TwoWay.Chk.exists_haltOK_right`, `TwoWay.Chk.exists_haltOK_left`) |
| `PartC/SnakeChkSlot.lean` | the pieces of the record-breaker decomposition as pieces of the chain — the two halves of an excursion (`TwoWay.Chk.exists_crossOK_exc`), a progress part (`TwoWay.Chk.exists_crossOK_prog`) and the final piece (`TwoWay.Chk.exists_haltOK_final`) — together with the two times that delimit a piece slot (`TwoWay.Chk.pcStart`, `TwoWay.Chk.pcEnd`) and the proof that consecutive slots meet |
| `PartC/SnakeChkSlotOK.lean` | every slot of the record-breaker decomposition carries a piece of the chain, on a window confined to its pair of blocks (`TwoWay.Chk.SlotOK`, `TwoWay.Chk.exists_slotOK`) |
| `PartC/SnakeChkRB.lean` | **the record-breaker decomposition of a good input is a chain of pieces** (`TwoWay.Chk.nonempty_chainData_of_good`): the last step of stage 1, and with it of Theorem `thm:2dfa-decomposition-into-primes` |
| `PartC/SnakeAlph.lean` | **the book's alphabet of snake letters** `Transducers.SnakeLetter Q B` (a letter is a bipartite graph on two copies of `Q`, with at most one outgoing edge per vertex, labelled by output letters) and the snake graph a string over it represents: vertices, edges, paths (`SnakeGraph.IsSnakePath`), the output `SnakeGraph.pathOut` of a path, the width of the graph (`SnakeGraph.SnakeWidthLe`) and the function `SnakeGraph.snakeOut k` of Lemma `lem:output-of-snake-graph-is-regular` |
| `PartC/SnakeAlphLoc.lean` | the edges of a snake graph read off the two letters adjacent to a column, which is what makes the conditions on the graph local |
| `PartC/SnakeAlphChar.lean` | **the characterisation `SnakeGraph.representsSnake_iff`**: a string represents a snake graph exactly when in- and out-degrees are at most one, there is at most one source and there is no directed cycle |
| `PartC/SnakeAlphLocLang.lean` | the degree conditions and the width condition are regular, being conditions on pairs of consecutive letters, and so is the uniqueness of the source |
| `PartC/SnakeAlphCyc.lean` | acyclicity is a regular condition: a left-to-right automaton keeps track of the reachability relation between the vertices of the current column |
| `PartC/SnakeAlphRun.lean` | the two-way transducer `SnakeGraph.snakeTrans` that walks along a snake graph, and the proof that it computes the output of the graph (`SnakeGraph.computes_snakeTrans`), so that the width-bounded output function of `Transducers.boundedWidth_isRegular` already computes it |
| `PartC/SnakeAlphReg.lean` | **Lemma `lem:output-of-snake-graph-is-regular` in the form the book states it** (`SnakeGraph.snakeOut_isRegular`), obtained from the two previous items by the conditional of Lemma `lem:regular-closure-properties` |
| `PartC/TwoWayOrder.lean` | the *order in time* of the visits of a run to a cut is a regular property: a cut marked with a pair of states `(q₁, q₂)` is accepted by the two-way automaton `TwoWay.orderAut` exactly when the run visits it in `q₁` before it ever visits it in `q₂` (`TwoWay.VisitsBefore`, `TwoWay.orderLang_isRegular`), together with the resulting API for the first and the last visit to a cut |
| `PartC/TwoWayAnnotOrd.lean` | the same information as a *rational annotation* of the input (`TwoWay.exists_rational_visitOrder_annot`): from the annotation of the two letters adjacent to a cut one reads off, for every pair of states, which of the two visits comes first, and hence which visit to the cut is the first and which is the last |
| `PartC/RatBi.lean` | *bilateral rewritings*: a rewriting in which the block produced at a letter depends on the letter, on the state of a deterministic automaton run left-to-right on the prefix and on the state of a deterministic automaton run right-to-left on the suffix, is computed by a bimachine and hence rational (`Transducers.isRationalFun_biEval`); the two standard instances are cutting out the factor selected by regular lookaround (`isRationalFun_biFilter`) and cutting the input into the blocks it delimits (`isRationalFun_biMarkSep`) |
| `PartC/RegPair.lean` | the *neighbouring-block map combinator* is a regular operation (`Transducers.RegPair.isRegularFun_pairMap`): if `f` is regular then so is `w₀ # ⋯ # wₙ ↦ f (w₀ # w₁) · f (w₁ # w₂) ⋯ f (wₙ₋₁ # wₙ)`.  This is stages 1--3 of the book's induction step, carried out exactly as in the book: a rational function appends a copy of the separator at the end of every block, map duplicate procures the two copies of every block, and a bilateral rewriting deletes the extra copies of `w₀` and `wₙ` and re-brackets the rest |
| `PartC/SSTDef.lean` | Definition `def:sst`: the copyless restriction (`Transducers.Copyless`), streaming string transducers (`Transducers.SST`) and their semantics (`SST.subst`, `SST.runConfig`, `SST.eval`, `Transducers.IsSST`), moved here unchanged from `Statements.lean` so that the constructions of Theorem `theorem:sst-two-way-equivalence` can precede it |
| `PartC/SSTBasic.lean` | the elementary API of an sst: substitution of register contents, the workable form `Transducers.copyless_iff` of the copyless restriction, the list `Transducers.regsOf` of register occurrences, and the *simulation lemma* `SST.eval_of_sim` by which every construction below is verified |
| `PartC/SSTComp.lean` | the easy cases of the closure of sst's under post-composition with a prime regular function: the identity sst, homomorphisms, the separator function and the case distinction on a regular language |
| `PartC/SSTMealyRev.lean`, `PartC/SSTMealyFF.lean`, `PartC/SSTMealy.lean` | post-composition of an sst with a Mealy machine, hence with an arbitrary rational function: since the naive construction is not copyless, the machine is decomposed by Krohn–Rhodes (Theorem `thm:krohn-rhodes`) into reversible and flip-flop machines, treated in the first two files, and `SSTMealy.lean` assembles them |
| `PartC/SSTMapRev.lean`, `PartC/SSTMapDup.lean` | post-composition of an sst with map reverse and with map duplicate, the two remaining prime regular functions: the register contents are kept as tuples indexed by the position of the separators inside them, and copylessness is proved by counting register occurrences |
| `PartC/SSTRegular.lean` | the "regular to sst" half of Theorem `theorem:sst-two-way-equivalence` (`Transducers.isSST_of_isRegularFun`): sst's are closed under post-composition with every prime, hence with every regular function, and applying this to the identity sst gives the statement |
| `PartC/SSTNorm.lean` | *normalised* sst's (`Transducers.NSST`: the register update depends only on the letter read, the state only on the last letter, and no register occurs twice in a final output string) and the reduction of an arbitrary sst to one (`Transducers.exists_nsst_of_sst`): the input letters are annotated by a Mealy machine with the state of the sst before them, and `K + 1` copies of every register are kept so that the occurrences in a final output string can be given pairwise distinct copies |
| `PartC/SSTWalk.lean` | the two-way transducer that traverses the register flow tree of a normalised sst (`Transducers.isTwoWay_of_nsst`): it expands the final output string depth-first, moving left to expand the value of a register and right when an expansion is finished, and the copyless restriction is what makes the place at which the expansion has to be resumed a function of the register and of the letter at the position returned to (`NSSTWalk.findReg_eq`, `NSSTWalk.scan`, `NSSTWalk.top`) |
| `PartC/SSTTwoWay.lean` | the "sst to regular" half of Theorem `theorem:sst-two-way-equivalence`, through Theorem `thm:2dfa-decomposition-into-primes` (`Transducers.isTwoWay_of_isSST`): the annotation of `SSTNorm.lean` is rational and two-way transducers are closed under pre-composition with rational functions (Corollary `cor:2dfa-closure-under-composition`) |
| `PartC/KTypes.lean` | `k`-types of strings (Definition `def:k-types`) and their properties (Lemma `lem:k-types-properties`) |
| `PartC/Statements.lean` | Sections *The prime regular functions* to *Streaming string transducers*: regular functions, two-way transducers, streaming string transducers |
| `PartC/MSODef.lean` | the definitions of Section *Logic*: monadic second-order logic over strings, mso relabellings, mso transductions and the first-order fragment (moved unchanged out of `MSO.lean`, which imports this file) |
| `PartC/MultiDFA.lean` | one deterministic automaton for a finite family of regular languages (`MultiDFA.exists_prod`), and the regular language "the last letter belongs to `F`"; used by the walking transducer of Theorem `thm:logic-regular-functions` |
| `PartC/MSOWeak.lean` | why Definition `def:mso-transduction` needs its two requirements: without them (`Transducers.IsWeakMSOTransduction`) every length preserving function would be an mso transduction, so Theorem `thm:logic-regular-functions` would fail |
| `PartC/MSOSyntax.lean` | elementary syntax and semantics of mso formulas: satisfaction depends only on the free variables (`MSO.sat_congr`), bounds on the variables of a formula, finite conjunctions and disjunctions, universal quantification and implication as abbreviations, and the existential closure of a list of variables |
| `PartC/RegAut.lean` | a toolkit of regular languages used by the translation of formulas into automata: languages defined by a `foldl` and by an nfa, Boolean operations, finite intersections, images and inverse images of letter-to-letter maps, the scanning languages, and the language of strings with exactly one marked position |
| `PartC/MSOAnnot.lean` | Lemma `lem:mso-free-variables`: the language `AnnLang` of valid annotated strings satisfying a formula, its regularity by induction on the syntax of the formula, and its identification with the language in the statement of the lemma |
| `PartC/MSOBuchi.lean` | Theorem `thm:mso-logic-languages`: the language of a sentence is regular (from Lemma `lem:mso-free-variables`), and the formula that guesses the run of a dfa as one second-order variable per state |
| `PartC/MSORelab.lean` | Claim `claim:mso-annotation-regular`: the strings over `Γ × 2` with one marked position at which a formula holds form a regular language, and the language of the claim is the intersection, over the finitely many indices, of the complements of the projections of those languages |
| `PartC/MarkStr.lean` | doubly marked strings: the alphabet `Mark2 A = A × 2 × 2`, the marking `markAt2 w x y` of two positions of a string and its decomposition into prefix, marked infix and suffix, and the regular language `markedSat2 φ` of doubly marked strings satisfying a formula (from Lemma `lem:mso-free-variables`) |
| `PartC/MarkLogic.lean` | the converse translation: from an automaton over `Mark2 A` back to an mso formula with one free variable (`exists_form_of_regular`), by a syntactic translation of the formula given by Theorem `thm:mso-logic-languages` for the language of marked strings |
| `PartC/MarkBimach.lean` | the bimachine that precomputes, in every position of the input, the state of each automaton of a finite family on the unmarked prefix and its state transformation on the unmarked suffix; the function `markFun` it computes, its rationality (from Theorem `thm:bimachines`) and, in the letter-to-letter case, its length preservation |
| `PartC/MarkDelay.lean` | the delayed automaton reading letters that carry states and state transformations: it keeps the last letter read pending, since whether a position is the last one is known only when the string ends |
| `PartC/MSORatRelab.lean` | Theorem `thm:logic-rational-functions`: from a bimachine to an mso relabelling (this is Claim `claim:transition-formula` of the book, formalised for the index of a bimachine rather than for an unambiguous transducer), and from an mso relabelling back to a bimachine |
| `PartC/MSOPrecomp.lean` | Lemma `lem:logic-precomputation`: the letter-to-letter rational function that decorates every position by the states of the automata of the family, the set of letters for a formula with one free variable, and the delayed language for a formula with two free variables |
| `PartC/MSOSubst.lean` | renaming of all the variables of a formula and the two combinators `MSO.atv`, `MSO.atv2` that plug a formula with one or two free variables under a quantifier |
| `PartC/MSONorm.lean` | Lemma `lem:logic-reduction-to-type-n`: the normalisation of the type `τ` of an mso transduction — a single set of tags, one universe and letter formula with one free variable per tag and one order formula with two free variables per pair of tags (`Transducers.NormT`), with the extra elements of `τ` attached to the first position of the input |
| `PartC/SortedEnum.lean` | the order-theoretic dictionary between a linear order on a finite set and its increasing enumeration (minimum, maximum, successor) |
| `PartC/MSOWalkForms.lean` | the mso formulas that the walking transducer of Theorem `thm:logic-regular-functions` asks about — "is this element the first / the last one", "is its successor at the same position, or to the right", "is this element the successor of that one" — and their meaning in terms of the sorted enumeration of the selected elements |
| `PartC/WalkAut.lean` | the walking two-way transducer of Theorem `thm:logic-regular-functions`, in abstract form (letter-indexed answers to the unary questions and one deterministic automaton with a family of acceptance conditions for the binary ones), and its correctness `Transducers.WalkAut.computes_of_spec` |
| `PartC/MSOWalkData.lean` | the walking transducer of an mso transduction: the product of the family of automata (with the last letter read), the `WalkAut.Data` built from the precomputation of Lemma `lem:logic-precomputation`, and the verification of the nine hypotheses of `WalkAut.computes_of_spec` |
| `PartC/MSOReg.lean` | Theorem `thm:logic-regular-functions`, from mso transductions to regular functions: normalise (Lemma `lem:logic-reduction-to-type-n`), precompute the questions (Lemma `lem:logic-precomputation`), walk (`MSOWalkData.lean`), and compose the rational precomputation with the width-bounded output of the walking transducer, which is regular by Theorem `thm:2dfa-decomposition-into-primes` |
| `PartC/RunProbe.lean` | probing the run of a two-way transducer by a deterministic two-way automaton that simulates it and stops at the first configuration satisfying a trigger condition (used for the converse half of Theorem `thm:logic-regular-functions`) |
| `PartC/RunMark.lean` | the regular languages of doubly marked strings describing the run of a two-way transducer: which targets it reaches, which letter it produces there, and which of two targets it reaches first |
| `PartC/MarkLogic2.lean` | the converse translation from an automaton over `Mark2 A` back to an mso formula with **two** free variables |
| `PartC/FlatIndex.lean`, `PartC/RunElts.lean` | the combinatorics of the output positions of a two-way transducer as pairs (step of the run, position inside the string produced at that step), and the list of elements required by `MSOTransduction.Outputs` |
| `PartC/TwoWayMSO.lean` | Theorem `thm:logic-regular-functions`, from two-way transducers to mso transductions: the mso transduction whose elements are the pairs (configuration, index of a produced letter), with all its formulas obtained from `RunMark.lean` through Theorem `thm:mso-logic-languages` |
| `PartC/FORel.lean` | relativisation of a first-order formula to the positions strictly below, at most, or strictly above a variable (`MSO.relLt`, `relLe`, `relGt`), the strict order `MSO.ltVar` and the fact that a first-order sentence does not see its valuations (`MSO.sat_sentence_congr`) |
| `PartC/FOSeg.lean` | factors of a string between two bounds (`MSO.segP`), their splitting, and the transfer of a splitting along an equality of `(k+1)`-types (`Transducers.exists_split_of_tp_succ_eq`) |
| `PartC/FOComp.lean` | Claim `claim:fo-composition-quantifier-rank` (an internal step, not a numbered result): the compositionality of first-order logic — if two strings have the same `k`-type then a marked position on one side can be matched on the other so that all formulas of quantifier rank `k` are preserved (`Transducers.KEquiv`, `sat_iff_of_kEquiv`, `sat_iff_of_tp_eq`) |
| `PartC/FORename.lean` | the effect of renaming and of shifting the variables of a formula on being first-order, on the quantifier rank and on the free variables, and finite conjunctions and disjunctions of first-order formulas |
| `PartC/FOHintikka.lean` | the second half of Lemma `lem:k-types-fo-equivalence`: a first-order sentence of quantifier rank at most `k` separating two strings of different `k`-type (`Transducers.exists_fo_sentence_of_tp_ne`, `tp_eq_of_fo_equiv`) |
| `PartC/FOTypeDFA.lean` | the easy direction of Theorem `thm:logic-aperiodic`: the (aperiodic, finite) automaton of `k`-types and the aperiodic dfa recognising a first-order definable language (`Transducers.tpDFA`, `aperiodic_dfa_of_foDefinable`) |
| `PartC/FOSubstRel.lean` | substitution of a sentence for a label test in a first-order formula, relativised to the positions at most a variable (`MSO.substRel`), used for the composition of first-order definable Mealy machines |
| `PartC/FOFlipFlop.lean` | flip-flop machines: the letter-indexed reset target (`Mealy.resetTo`) and the description of the state reached after a prefix as the target of the last resetting letter (`Mealy.trans_take_eq_iff`) |
| `PartC/FOMealy.lean` | the hard direction of Theorem `thm:logic-aperiodic`: first-order definable Mealy machines (`Transducers.FODefMealy`), their closure under composition, the first-order definability of flip-flops and hence of every composition of flip-flops (through the aperiodic Krohn-Rhodes Theorem `thm:aperiodic-mealy`), and the Mealy machine of a dfa (`Transducers.foDefinable_of_aperiodic_dfa`) |
| `PartC/FORev.lean` | first-order definability and reversal: every first-order definable language is defined by a first-order *sentence* (`FODefinable.exists_sentence`), the characterisation of first-order definability by invariance under `k`-types, the reversal `tpRev` of a `k`-type and `FODefinable.reverse`, and the first-order definability of the languages `{u \| δ*(q₀,u) = q}` and `{u \| δ*(q₀,reverse u) = q}` of an aperiodic transition function |
| `PartC/FOPos.lean` | compositionality at a position: whether a first-order formula of quantifier rank at most `k`, evaluated with the constant valuation at a position, holds depends only on the `k`-type of the prefix, the letter and the `k`-type of the suffix (`Transducers.sat_const_iff_of_tp_split`) |
| `PartC/FORelabBimach.lean` | Theorem `thm:fo-rational-functions`, from first-order relabellings to aperiodic bimachines: the prefix and suffix automata compute the `k`-type of the prefix and of the suffix, which are aperiodic transition functions, and by `FOPos.lean` the index chosen at a position — hence the output block — is a function of those two types and of the letter |
| `PartC/FOBimachRelab.lean` | Theorem `thm:fo-rational-functions`, from aperiodic bimachines to first-order relabellings: the formula attached to an index `(q, a, s, last?)` says that the prefix drives the prefix automaton to `q` (a first-order sentence by Theorem `thm:logic-aperiodic`, relativised to the positions below), the letter is `a`, the suffix drives the suffix automaton to `s` (relativised to the positions above, first-order by `FODefinable.reverse`), and the position is, or is not, the last one; the block of the last gap is appended to the block of the last position |
| `PartC/ITrans.lean` | mso transductions with arbitrary finite index sets (`Transducers.ITrans`) and the transport theorem `ITrans.isFOTransduction`, which removes the bijections `Fin k × Fin l ≃ Fin (k*l)` from the constructions of Part C |
| `PartC/TransEnum.lean` | the output of an `ITrans` read as an ordered enumeration of the selected elements (`ITrans.Enum.ord_iff_le`, `Enum.lab_iff`, `Enum.exists_index`), in the form the backwards translation of `FOTransTr.lean` uses |
| `PartC/FOPlug.lean` | the first-order plugging combinators `MSO.atvF`, `MSO.atv2F` and `MSO.atZeroF`: the second-order binding of `MSO.atv`/`MSO.atv2` can be dropped inside a first-order formula, because a first-order formula does not see the valuation of the set variables |
| `PartC/ITransBuild.lean` | tools for building first-order transductions: the construction of an `ITrans.Outputs` witness from a pairwise-ordered enumeration of the selected elements (`ITrans.outputs_of_pairwise`, `ITrans.outputs_of_forall₂`), the list lemmas `Transducers.forall₂_append` and `Transducers.forall₂_flatMap`, and the first-order transductions given by the identity and by a bijection of alphabets (`Transducers.isFOTransduction_id`, `Transducers.isFOTransduction_map_equiv`) |
| `PartC/BlockPos.lean` | the block combinatorics of the positions of a string over `Option A`: the separators (`Transducers.SepAt`), the equivalence "same block" (`Transducers.SameBlk`) with its symmetry, transitivity and betweenness properties, and the description of both for a string of the shape `u # w'` |
| `PartC/BlockForm.lean` | the first-order formulas `Transducers.sepF`, `Transducers.betweenF` and `Transducers.sameBlkF` expressing the predicates of `BlockPos.lean`, with their quantifier-rank-free-ness and their semantics |
| `PartC/FORelabTrans.lean` | every first-order relabelling is a first-order transduction (`Transducers.isFOTransduction_of_isFORelabelling`) |
| `PartC/FOTransRev.lean` | map reverse is a first-order transduction (`Transducers.isFOTransduction_mapReverse`): the elements are the positions, ordered by `Transducers.revOrd`, which keeps the order of the blocks and reverses the order inside a block |
| `PartC/FOTransTr.lean`, `PartC/FOTransComp.lean` | first-order transductions are closed under composition (`Transducers.isFOTransduction_comp`), by translating the formulas of the second transduction backwards along the first one; this is the first-order substitute for the route through Theorem `thm:logic-regular-functions` used in the mso case |
| `PartC/FOTransDup.lean` | map duplicate is a first-order transduction (`Transducers.isFOTransduction_mapDuplicate`): the elements are pairs `(copy, position)` ordered by `Transducers.dupOrd`, which puts the first copy of a block before its second copy |
| `PartC/FOPrimeFam.lean` | the family `Transducers.FORegularFam` of prime first-order regular functions (first-order rational functions, map reverse, map duplicate) |
| `PartC/FOTransPrimeComp.lean` | every composition of the primes of `FORegularFam` is a first-order transduction (`Transducers.isFOTransduction_of_compClosure`), by induction on `CompClosure` from the four files above |
| `PartC/MSO.lean` | Section *Logic*: the numbered results that are **proved** — Theorem `thm:mso-logic-languages`, Lemma `lem:mso-free-variables`, Theorem `thm:logic-rational-functions`, Claim `claim:mso-annotation-regular`, Theorem `thm:logic-regular-functions`, Lemma `lem:logic-precomputation`, Theorem `thm:logic-aperiodic`, Lemma `lem:k-types-fo-equivalence`, Lemma `lem:k-types-properties` and Theorem `thm:fo-rational-functions` (this file contains no `sorry`) |
| `PartC/MSOOpen.lean` | Section *Logic*: pointer comments only. It used to hold the results of Section *Logic* that were not yet proved; the last one, Theorem `nolabel:thm-fo-transduction-into-primes`, has been **removed from the formalised theorems at the user's request** and is kept there only as a comment, so the file now declares nothing and Section *Logic* has no `sorry` left |
| `PartD/MarkedSquare.lean` | marked squaring and its continuity |
| `PartD/ForDef.lean` | the syntax and the semantics of the for-transducers, and Definition `def:prenex-normal-form-for-transducers` |
| `PartD/ForSem.lean` | the semantic toolkit: folds over lists, nests of loops as folds over tuples, the variables and the letters of a program |
| `PartD/ForNest.lean`, `PartD/ForMerge.lean`, `PartD/ForPrenex.lean`, `PartD/ForLex.lean`, `PartD/ForTrace.lean`, `PartD/ForPrenexTop.lean` | the translation of a program into a single nest of loops and the proof of Lemma `lemma:prenex-normal-form` |
| `PartD/ForAtom.lean` | atomic tests, the atomisation of a program, constant programs, and the letters a program can see |
| `PartD/ForEvents.lean` | the tuples at which the body of a nest produces a letter, and their lexicographic order |
| `PartD/ForResim.lean` | the re-simulation of the inner nest of loops: answering, inside the composed program, a question about the letter produced at a given tuple |
| `PartD/ForFree.lean` | the free position variables of a program, and the transformation making a program closed (every free position variable bound by a loop that runs at the first position only) |
| `PartD/ForCompDef.lean`, `PartD/ForComp.lean` | the translation of the outer for-transducer over the tuples of the inner one, and its correctness (`Transducers.tr_spec`) |
| `PartD/ForCompTop.lean` | the assembly of Lemma `lem:for-closed-under-composition`: the length flags, the continuation-passing simulation on the inputs of length at most one, and the composed program |
| `PartD/PolyDef.lean` | Definition `def:polyregular-functions` and the elementary closure properties of the polyregular functions (moved here, unchanged, from `PartD/Statements.lean`, so that the constructions of the proof of Theorem `thm:for-transducers-are-polyregular` can be developed before the statements) |
| `PartD/ForMachine.lean` | a small machine language over a finite set of states, compiled into for-programs |
| `PartD/ForMapRev.lean` | map reverse and map duplicate are computed by for-transducers |
| `PartD/ForPrimes.lean` | each prime polyregular function -- rational functions, map reverse, map duplicate, marked squaring -- is computed by a for-transducer |
| `PartD/ForPolyreg.lean` | the left-to-right inclusion of Theorem `thm:for-transducers-are-polyregular`: every polyregular function is computed by a for-transducer (`Transducers.isForTransducer_of_isPolyregular`) |
| `PartD/PolyEnum.lean` | the enumeration `Transducers.PolyEnum.enum` of the tuples of positions visited by a nest of for-loops, one annotated copy of the input per tuple |
| `PartD/PolyStep.lean`, `PartD/PolyStepTop.lean` | the streaming string transducer that adds one innermost loop to the enumeration, and its correctness |
| `PartD/PolyEnumPoly.lean` | the enumeration is polyregular (`Transducers.PolyEnum.isPolyregular_enum`): marked squaring followed by the one-step transducer, iterated over the loops of the nest |
| `PartD/PolyScanAux.lean` | the ingredients of the scan of the enumeration: a loop-free program only sees the order of its position variables and the letters under them (`Transducers.ForProg.exec_congr_view`), and the finite information kept about one annotated copy |
| `PartD/PolyScan.lean` | the streaming string transducer that scans the enumeration, running the body of the nest once per copy and the epilogue at the end, and its correctness (`Transducers.PolyEnum.scan_enum`) |
| `PartD/PolyFor.lean` | the right-to-left inclusion of Theorem `thm:for-transducers-are-polyregular`: a for-transducer in prenex form is the enumeration followed by the scan, so every for-transducer computes a polyregular function (`Transducers.PolyEnum.isPolyregular_of_isForTransducer`) |
| `PartD/PebbleDef.lean` | the syntax and the semantics of the pebble transducers, moved out of `PartD/Statements.lean` unchanged (`Transducers.PebbleView`, `Transducers.viewOf`, `Transducers.PebbleAction`, `Transducers.Pebble`, `Transducers.Pebble.Computes`, `Transducers.IsPebbleTransducer`) |
| `PartD/PebbleAut.lean` | pebble *automata*: the variant of pebble transducers that returns an answer instead of a string, their one-step function `Transducers.PebbleAut.next`, the answer of a run, and the resolution `Transducers.resolve` of a sequence of stationary steps |
| `PartD/PebbleProd.lean` | the product of a pebble transducer with a deterministic automaton for the target language (`Transducers.prodAut`), which turns Theorem `thm:pebble-are-continuous` into a statement about pebble automata |
| `PartD/PebbleSub.lean` | the sub-machine of a pebble automaton: what happens above the bottom pebble is a run of a `k`-pebble automaton `Transducers.subAut` over the input with the bottom gap marked (`Transducers.markSplit`) |
| `PartD/PebbleAnn.lean` | the *gap data* of a pebble automaton (`Transducers.gapVal`) and the fact that annotating every gap of the input with it is continuous, by a bimachine (`Transducers.exists_annotation`) |
| `PartD/PebbleBisim.lean` | a big-step bisimulation principle for two deterministic systems (`Transducers.bisim_acc_iff`) |
| `PartD/PebbleOne.lean` | one-pebble automata recognise regular languages (`Transducers.OnePebble.onePebble_isRegular`), by collapsing their two levels into a deterministic two-way automaton and applying Shepherdson's Theorem |
| `PartD/PebbleLev1.lean` | pebble automata recognise regular languages (`Transducers.pebbleAut_answers_isRegular`), by induction on the number of pebbles: a `(k+1)`-pebble automaton is simulated by a one-pebble automaton over the annotated alphabet |
| `PartD/PebbleReg.lean` | Theorem `thm:pebble-are-continuous`: pebble transducers compute continuous functions (`Transducers.continuous_of_isPebbleTransducer`) |
| `PartD/PebbleForDef.lean`, `PartD/PebbleForRun.lean`, `PartD/PebbleForNest.lean`, `PartD/PebbleForTop.lean` | the easy direction of Theorem `thm:pebble-are-for`: a for-transducer in prenex form is simulated by a pebble transducer, one pebble per loop of the nest (`Transducers.PebFor.isPebbleTransducer_of_isForTransducer`) |
| `PartD/TwoWayTotal.lean` | a two-way transducer computes a regular function on the inputs on which it halts (`Transducers.TwoWay.exists_regularFun_of_twoWay`) |
| `PartD/SqPad.lean` | the padded input `Transducers.pad` (a blank on each side), its letters, its polyregularity, and the coordinates of the marked square of a string |
| `PartD/PebbleTwoWay.lean` | a one-pebble transducer is a two-way transducer, so it computes a regular function (`Transducers.PebOne.exists_regularFun_of_pebble_one`) -- the base case of the induction on the number of pebbles |
| `PartD/PebbleSquareIdx.lean` | the index structure of the marked square of the padded input: the marked gap and the start of a block, and the three tests (`Transducers.PebSq.topMark`, `topStart`, `topCoin`) that a pebble transducer can perform on them |
| `PartD/PebbleSquareDef.lean` | the `k`-pebble transducer `Transducers.PebSq.sim` that simulates a `(k+1)`-pebble transducer on the marked square of the padded input, the encoding of a stack, and the decoding of a view |
| `PartD/PebbleSquareRun.lean` | the run of the simulating machine: the walking phases, the composite walks, and one step of the simulated machine |
| `PartD/PebbleSquareSim.lean` | the simulation theorem: the simulating machine produces the same output on the marked square as the simulated one on the input (`Transducers.PebSq.sim_computes`) |
| `PartD/PebblePoly.lean` | the hard direction of Theorem `thm:pebble-are-for`: by induction on the number of pebbles, a pebble transducer computes a polyregular function (`Transducers.isPolyregular_of_isPebbleTransducer`) |
| `PartD/Statements.lean` | Part D: polyregular functions, for-transducers, pebble transducers |
| `Labels.lean` | the label-indexed view of the formalisation: for every result of the book that is formalised, an alias in the namespace `Transducers.Book` whose Lean name is the LaTeX label of the result, followed by `assert_no_sorry` or `assert_uses_sorry` according to its status in the tables below.  Kept in step with those tables by `tools/gen_labels.py --check`; see `LABELS.md` |

## Conventions

* Strings are `List A`, languages are `Language A = Set (List A)`, regularity is
  Mathlib's `Language.IsRegular`.
* Finiteness of an alphabet or a state space is an instance argument
  `[Finite A]` or an existential `∃ (Q : Type) (_ : Finite Q), …`.
* **Decidability statements.**  "Problem `P` is decidable" is formalised as `DecidableUnderPromise
  promise P`: there is a `Computable` `Bool`-valued function that answers `P` correctly on all
  finite descriptions (codes) satisfying the promise (for instance, that the code describes a
  function rather than a relation).  Since a code has only finitely many transitions it reads only
  finitely many letters of the ambient alphabet `ℕ`, so the promise `CodeFunctional` asks for a
  total function on the strings over the alphabet of the code; `Transducers.not_codeTotalFunctional`
  shows that asking for totality on all of `ℕ*` would be vacuous.  For the same reason the property
  decided in Theorem `thm:decide-if-mealy` is relativised to the strings over the alphabet of the
  code; the original statement is kept as a comment in `PartB/WeightedStatements.lean`, with an
  explanation.  Undecidability (Theorem `thm:undecidable-equivalence-rational-relations`) is `¬
  ComputablePred …`.  Theorem `thm:equivalence-decidable-mealy` is stated instead in the equivalent
  concrete form of a finite check on inputs of bounded length.
* **Compositions of prime functions** are expressed with `CompClosure P`, the
  closure of a family `P` of string-to-string functions under composition.

## Divergences from the book

Every place where the Lean statement of a numbered result differs from the
statement in the LaTeX sources, collected in one list.  Each one is also
recorded in the docstring of the declaration concerned and, where it belongs to
a single result, in the index below.  Every entry was re-read against the LaTeX
sources during the closing audit of the project, and this list is complete for
them; a divergence that has since disappeared from the book is noted as such
rather than deleted, because the note explaining it is still in the Lean files.
That last check moved one entry, Lemma `lemma:derivatives`, out of the list of
false statements and into the list of statements the book has corrected.

*Statements that were corrected because the printed version is false.*

* Definition `def:aperiodic-mealy` — `Transducers.Aperiodic` asks that the last letter of
  `f (u vⁿ w)` be eventually constant **as an element of `Option B`**.  Requiring an
  actual output letter makes the notion unsatisfiable, since for `u = v = w = ε`
  the output of a letter-to-letter function is empty.  The Lean definition also
  drops the book's side conditions that `f` be length preserving and that `uvw`
  be nonempty; neither is used.
* Claim `claim:conditional` — corrected on the empty input; the claim as printed is false
  there, and `Transducers.not_sum_of_regular_nil` is the counterexample.  See
  *An error in Claim `claim:conditional`* below.

*Statements that are formalised in an equivalent or restricted form.*

* Theorem `thm:equivalence-decidable-mealy` — stated as the finite check "the two machines are
  equivalent iff they agree on all inputs of length at most `|Q₁|·|Q₂|`", not as a
  `Decidable` instance.
* Theorem `thm:decide-if-mealy` — the decided property is relativised to the strings over the
  alphabet of the code (`CodeWord c`); see *Decidability statements* above.
* Lemma `lem:aperiodicity-minimal-machine` — stated as "some machine computing `f` satisfies
  condition (*)" rather than "the minimal machine of `f` satisfies (*)".  The two are
  equivalent, because (*) is inherited by the minimal machine, and the Lean form
  avoids constructing the minimal machine.  The book's finiteness assumptions on
  the alphabets are not needed and are omitted.
* Lemma `lem:k-types-fo-equivalence` — the book says two strings have the same `k`-type iff they
  satisfy the same first-order *formulas* of quantifier rank at most `k`; the Lean
  statement quantifies over first-order **sentences** (`φ.freeFO = ∅`), which is
  what "a string satisfies `φ`" means when there is no valuation to supply.
* Lemma `lem:output-of-snake-graph-is-regular` — stated as in the book, over the alphabet
  `Transducers.SnakeLetter Q B` of snake letters, but for every `k : ℕ`, not only for
  `k ∈ {1, …, |Q|}`; that is more general, and the restriction is immaterial, since a
  column has at most `|Q|` vertices.  The book's alphabet has, besides the slices, a
  special letter for the empty input; it is not needed for snake graphs, since the
  empty string already represents the graph with one column and no edge.  The general
  form the book's statement is proved from, `Transducers.boundedWidth_isRegular`, is
  kept: it says the same thing for the width-`k` output function `TwoWay.widthOut M k`
  of a two-way transducer.
* Claim `claim:transition-formula` — stated for the index of a bimachine rather than for an
  unambiguous transducer.
* Claims `claim:bounded-extensions`, `claim:computing-branching-part`, `claim:offsets-are-regular`
  and `claim:eliminating-negative-letters` — the Lean proof of Theorem
  `thm:subsequential-functions` reorganises these four steps; see the note after
  the Part B index for what each Lean declaration actually says.

*Parts of a statement that are not formalised.*

* Theorem `thm:aperiodic-mealy` — the sentence "Moreover, this property can be decided, given a
  Mealy machine that computes `f`" is **not formalised**.  What is formalised is the
  characterisation Lemma `lem:aperiodicity-minimal-machine` on which the book's decision
  procedure rests (enumerate the state transformations that arise and check that
  the powers of each one stabilise), but neither that enumeration nor the
  resulting decision procedure is written down.
* Definition `def:rational-recognisable-subsets` — not formalised at all; see its row in the
  Part B index.
* Conjecture `conj:regular-via-weighted-automata` and the five results of
  Section *Pebble transducers* listed in the Part D index — not formalised, each
  for the reason given in its row.

*Hypotheses that the Lean statement adds.*

* Theorem `thm:undecidable-equivalence-rational-relations` takes the undecidability of the Post
  correspondence problem, `¬ ComputablePred PCP.Solvable`, as an explicit argument.
* Theorems `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`,
  `thm:zeroness-weighted-automata` and `thm:decide-if-mealy` take
  `Transducers.EffectiveWeightedEvalEq` as an explicit argument, and Theorem
  `thm:decidable-equivalence-regular` takes `Transducers.EffectiveTwoWayEvalEq` and
  `Transducers.EffectiveTwoWayBound`.  See *The four conditional results of Part B* and
  *The conditional result of Part C* below for what each hypothesis says and why
  it is isolated.
* Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L` takes as an explicit
  argument the hypothesis that the two-way transducer computes a *total* function,
  `hM : ∀ w, M.Computes w (f w)`.  The book uses the lemma only for a transducer that
  computes a function, in the proof of Theorem `thm:continuity-2dfas`; without the
  hypothesis the transducer may fail to halt on some inputs and the statement is no
  longer about a function of the input.

*Divergences that the book has since removed.*

* Corollary `cor:2dfa-computes-all-regular-functions` — an earlier edition printed the inclusion
  the wrong way round.  The sources now read "Every regular function is computed
  by a two-way transducer", which is what is formalised.  See the section below.
* Theorem `thm:sequential-function-independent` — an earlier edition omitted the condition
  "outputs ε when the input is ε", which makes the theorem false.  The sources now
  list it as item (c), so the Lean statement is faithful; the earlier version is
  kept, commented out, in `PartB/WeightedStatements.lean`.
* Lemma `lemma:derivatives` — the derivative used to be printed as `f⁽ʷ⁾(v) = f (w v)`,
  without removing the output produced while reading `w`, and with that reading
  even the identity has infinitely many derivatives and the lemma is false.  The
  sources now read "`v ↦ f(wv)` with the first `|w|` letters of the output
  removed", which is the Lean definition `f⁽ʷ⁾(v) = drop |w| (f (w v))`, so the
  statement is now faithful.
* Theorem `nolabel:thm-fo-transduction-into-primes` — this is no longer a numbered environment of
  the book at all: `logic.tex` ends with an unnumbered paragraph that states the
  result and leaves its proof "for a future edition".  It was withdrawn from this
  formalisation at the author's request; the placeholder tag stays because the
  paragraph carries no `\label`.

## Index

### Introduction

| Book | Lean | Status | File |
| --- | --- | --- | --- |
| Definition `def:continuity` (continuity) | `Transducers.Continuous` | — | `Common/Basic.lean` |

### Part A: Mealy machines

| Book | Lean | Status | File |
| --- | --- | --- | --- |
| Definition `def:mealy-machine` (Mealy machine) | `Transducers.Mealy`, `Transducers.Mealy.eval`, `Transducers.IsMealy` | — | `PartA/MealyBasic.lean` |
| Theorem `thm:equivalence-decidable-mealy` (decidable equivalence) | `Transducers.mealy_equiv_iff_bounded` | proved | `PartA/Statements.lean` |
| Theorem `thm:composition-mealy` (composition) | `Transducers.mealy_comp` | proved | `PartA/Statements.lean` |
| Theorem `thm:continuity-mealy` (continuity) | `Transducers.mealy_continuous` | proved | `PartA/Statements.lean` |
| Definition `def:prime-mealy-machines` (prime Mealy machines) | `Transducers.Mealy.Reversible`, `Transducers.Mealy.FlipFlop`, `Transducers.PrimeMealyFam` | — | `PartA/MealyBasic.lean` |
| Theorem `thm:krohn-rhodes` (Krohn–Rhodes) | `Transducers.krohn_rhodes` | proved | `PartA/Statements.lean` |
| Definition `def:map-lifting` (map lifting) | `Transducers.mapLift` | — | `Common/Basic.lean` |
| Lemma `lem:map-lifting-decomposition-mealy` (map lifting of a decomposition) | `Transducers.mapLift_prime_decomposition` | proved (in `MapLift.lean`) | `PartA/Statements.lean` |
| Lemma `lem:Mealy-map-lifting` (state transformation transducer) | `Transducers.stateTransTransducer_prime_decomposition` | proved (in `StateTrans.lean`): induction basis `stateTransTransducer_prime_of_reversible`, induction step by the tripartite decomposition into `a`-blocks (`krStages_eq`, `krStages_compClosure`) | `PartA/StateTrans.lean` |
| Lemma `lem:reversible-composition` (reversible machines compose) | `Transducers.reversible_comp` | proved | `PartA/Statements.lean` |
| Definition `def:aperiodic-mealy` (aperiodic) | `Transducers.Aperiodic` | — | `Common/Basic.lean` |
| Theorem `thm:aperiodic-mealy` (aperiodic = flip-flops) | `Transducers.aperiodic_iff_flipflop_composition` | proved ("⇐" by `flipflop_composition_aperiodic`, "⇒" by `krohn_rhodes_flipFlop`, which runs the construction of `StateTrans.lean` inside the class of flip-flops, using that only realisable state transformations occur, see `StateTransAperiodic.lean`).  The theorem's last sentence, "moreover, this property can be decided", is *not* part of the Lean statement — see *Divergences from the book* above | `PartA/Statements.lean` |
| Claim `claim:aperiodic-pumping` (pumping form of aperiodicity) | `Transducers.aperiodic_iff_pumping` | proved | `PartA/Statements.lean` |
| Lemma `lemma:derivatives` (Myhill–Nerode) | `Transducers.myhill_nerode_mealy` | proved | `PartA/Statements.lean` |
| Lemma `lem:aperiodicity-minimal-machine` (condition (*)) | `Transducers.aperiodic_iff_transStabilises` | proved | `PartA/Statements.lean` |

One definition of Part A had to be corrected in order to make the corresponding
statements true, and one that used to need correcting no longer does; both are
documented in the docstrings.

* `Aperiodic` (Definition `def:aperiodic-mealy`) asks that the sequence of last letters of
  `f (u vⁿ w)` is eventually constant *as an element of `Option B`*.  Requiring
  an actual output letter would make the notion unsatisfiable, since for
  `u = v = w = ε` the output of a letter-to-letter function is empty.
* `deriv` (the derivative used in Lemma `lemma:derivatives`) removes the `|w|` output letters
  produced while reading `w`: `f⁽ʷ⁾(v) = drop |w| (f (w v))`.  This is what the
  sources now say; an earlier edition printed `f⁽ʷ⁾(v) = f (w v)`, and with that
  reading even the identity function has infinitely many derivatives and Lemma
  `lemma:derivatives` is false.

Two further divergences in Part A, both listed under *Divergences from the book*
above:

* the decidability clause of Theorem `thm:aperiodic-mealy` is not formalised;
* Lemma `lem:aperiodicity-minimal-machine` is stated as "some machine computing `f` satisfies
  condition (*)" instead of "the minimal machine of `f` satisfies (*)", which is
  equivalent and avoids constructing the minimal machine, and it drops the
  book's finiteness assumptions on the alphabets, which it does not need.

Auxiliary results proved along the way and reusable elsewhere:
`Transducers.Mealy.compose` (product of Mealy machines) and
`Transducers.Mealy.dfaComp` (the dfa reading the output of a Mealy machine),
`Transducers.derivMealy` (the minimal machine of a function),
`Transducers.compClosure_zipInput` and `Transducers.compClosure_liftSnd`
(a decomposition into primes can keep a copy of the input in its output),
`Transducers.outputMealy` (recovering the output of a machine from the state
transformations of the prefixes of the input).

### Part B: Rational functions

| Book | Lean | Status | File |
| --- | --- | --- | --- |
| Definition `def:nfa-with-output` (nfa with output) | `Transducers.NFAO` (via `Transducers.LabAut`) | — | `PartB/LabAut.lean` |
| Definition `def:rational-relation` (rational relation) | `Transducers.IsRationalRel` | — | `PartB/LabAut.lean` |
| Definition `def:rational-recognisable-subsets` (the rational and the recognisable subsets of a monoid) | — | not formalised.  The book uses it once, in the remark that explains the name *Kleene Theorem*; nothing else in the book, and nothing in this project, depends on it.  The recognisable subsets of `A* × B*` are formalised, for that monoid only, as `Transducers.Exercises.IsRecognisableRel` (Exercise `ex:recognisable-relations`, see `EXERCISES.md`) | — |
| Theorem `thm:composition-rational-relations` (composition) | `Transducers.rationalRel_comp` | proved (product automaton in `RatComp.lean`, on the atomic normal form of `Atomize.lean`) | `PartB/RationalStatements.lean` |
| Theorem `thm:continuity-rational-relations` (continuity) | `Transducers.rationalRel_continuous` | proved (ε-automaton running a dfa on the output, `RatCont.lean`) | `PartB/RationalStatements.lean` |
| Theorem `thm:undecidable-equivalence-rational-relations` (undecidable equivalence) | `Transducers.rationalRel_equivalence_undecidable` | proved from an explicit hypothesis that the Post correspondence problem is undecidable (reduction in `PCPRed.lean`) | `PartB/RationalStatements.lean` |
| Claim `claim:homomorphism-complement-rational` (complement of a homomorphism) | `Transducers.hom_complement_rational` | proved (explicit four-state automaton, `HomComplement.lean`) | `PartB/RationalStatements.lean` |
| Definition `def:rational-function` (rational function) | `Transducers.IsRationalFun` | — | `PartB/LabAut.lean` |
| Definition `def:bimachine` (bimachine) | `Transducers.Bimachine`, `Transducers.IsBimachine` | — | `PartB/Bimachine.lean` |
| Theorem `thm:bimachines` (rational = unambiguous = bimachine) | `Transducers.rational_iff_unambiguous_iff_bimachine` | proved (unambiguity by the least accepting run, `Unambig.lean` and `Uniform.lean`; bimachine → rational in `Bimachine.lean`, rational → bimachine in `RatBimach.lean`) | `PartB/RationalStatements.lean` |
| Lemma `lemma:eliminate-epsilon-transitions` (elimination of ε-transitions) | `Transducers.epsilon_elimination` | proved (`EpsElim.lean`, using the regularity of the outputs on a fixed input, `OutLang.lean`) | `PartB/RationalStatements.lean` |
| Lemma `lem:uniformisation` (uniformisation) | `Transducers.uniformisation` | proved (`Uniform.lean`, from the ε-free normal form of Lemma `lemma:eliminate-epsilon-transitions` and the unambiguisation of `Unambig.lean`) | `PartB/RationalStatements.lean` |
| Theorem `thm:rational-primes` (decomposition into primes) | `Transducers.rational_iff_prime_composition` | proved (`PrimeRat.lean` and `BimachPrime.lean`, from Theorem `thm:bimachines` and the Krohn–Rhodes Theorem) | `PartB/RationalStatements.lean` |
| Theorem `thm:rational-is-mealy-characterisation` (Mealy machines inside rational functions) | `Transducers.rational_isMealy_iff` | proved (from Theorem `thm:mealy-machine-independent` and Theorem `thm:continuity-rational-relations`) | `PartB/RationalStatements.lean` |
| Definition `def:semiring` (semiring) | Mathlib's `Semiring` | — | — |
| Definition `def:weighted-automaton` (weighted automaton) | `Transducers.LabAut.wEval`, `Transducers.IsWeighted` | — | `PartB/LabAut.lean` |
| Theorem `thm:equivalence-weighted-automata` (equivalence over ℚ) | `Transducers.weighted_equivalence_decidable` | proved from the effectivity hypothesis `EffectiveWeightedEvalEq` (`WeightedDec.lean`) | `PartB/WeightedStatements.lean` |
| Theorem `thm:equivalence-rational-functions` (equivalence of rational functions) | `Transducers.rationalFun_equivalence_decidable` | proved from `EffectiveWeightedEvalEq` (reduction to `thm:equivalence-weighted-automata` in `RatEqDec.lean`) | `PartB/WeightedStatements.lean` |
| Lemma `lem:closure-weighted-automata-precomposition` (pre-composition) | `Transducers.weighted_precomp_rational` | proved (`WeightedNF.lean`, `WeightedLinRep.lean` and `WeightedPrecomp.lean`) | `PartB/WeightedStatements.lean` |
| Theorem `thm:characterisation-rational-functions-weighted-automata` (characterisation of rationality) | `Transducers.rational_iff_weighted_precomp` | proved ("⇒" is Lemma `lem:closure-weighted-automata-precomposition`, "⇐" in `WeightedRegular.lean`) | `PartB/WeightedStatements.lean` |
| Theorem `thm:zeroness-weighted-automata` (zeroness) | `Transducers.weighted_zeroness_decidable` | proved from `EffectiveWeightedEvalEq` (special case of `thm:equivalence-weighted-automata`, `WeightedDec.lean`) | `PartB/WeightedStatements.lean` |
| Theorem `thm:mealy-machine-independent` (characterisation of Mealy machines) | `Transducers.isMealy_iff` | proved (`MealyChar.lean`) | `PartB/WeightedStatements.lean` |
| Theorem `thm:decide-if-mealy` (deciding the Mealy fragment) | `Transducers.rationalFun_isMealy_decidable` | proved from `EffectiveWeightedEvalEq` (`PrefixCodes.lean`, `CodeRat.lean`, `MealyDec.lean`); the statement is relativised to the strings over the alphabet of the code | `PartB/WeightedStatements.lean` |
| Lemma `lem:decide-if-length-preserving` (deciding length preservation) | `Transducers.rationalFun_lengthPreserving_decidable` | proved (bounded enumeration of transition sequences, `PathComb.lean` and `LenDec.lean`) | `PartB/WeightedStatements.lean` |
| Claim `claim:typing-length-preserving` (typings) | `Transducers.lengthPreserving_iff_typing` | proved (`Typing.lean`) | `PartB/WeightedStatements.lean` |
| Lemma `lem:characterisation-length-preserving` (length-preserving normal form) | `Transducers.lengthPreserving_rational_normal_form` | proved (`LenNormalForm.lean`) | `PartB/WeightedStatements.lean` |
| Theorem `thm:sequential-function-independent` (sequential functions) | `Transducers.isSequential_iff` | proved (`SeqChar.lean`).  The Lean statement is faithful: the book's condition (c) — *outputs ε when the input is ε* — is the Lean conjunct `f [] = []`.  An earlier edition of the book omitted (c), which made the theorem false; the docstring in `PartB/WeightedStatements.lean` still keeps that version, commented out, as a record | `PartB/WeightedStatements.lean` |
| Definition `def:left-distance` (left distance) | `Transducers.leftDist` | — | `Common/Basic.lean` |
| Theorem `thm:subsequential-functions` (subsequential functions) | `Transducers.isSubsequential_iff` | proved (`SubseqDef.lean`, `SubseqAlpha.lean`, `SubseqState.lean`, `SubseqBound.lean`, `SubseqChar.lean`) | `PartB/WeightedStatements.lean` |
| Claim `claim:bounded-extensions` (short extensions suffice) | `Transducers.Subseq.delay_bound`, `Transducers.Subseq.exists_short_extension` | proved (`SubseqAlpha.lean`); a **reorganised** step, not a literal rendering — see the note below | `PartB/SubseqAlpha.lean` |
| Claim `claim:computing-branching-part` (the branching part) | `Transducers.Subseq.key_drop` | proved (`SubseqState.lean`); phrased through Myhill–Nerode states rather than through regular languages — see the note below | `PartB/SubseqState.lean` |
| Claim `claim:offsets-are-regular` (the offsets) | `Transducers.Subseq.incr_congr` | proved (`SubseqState.lean`); phrased through Myhill–Nerode states rather than through regular languages — see the note below | `PartB/SubseqState.lean` |
| Claim `claim:eliminating-negative-letters` (negative letters) | `Transducers.Subseq.exists_deletion_bound` | proved (`SubseqBound.lean`); the free group is not used — see the note below | `PartB/SubseqBound.lean` |
| Theorem `thm:machine-independent-rational-functions` (rational functions) | `Transducers.isRationalFun_iff` | proved (`RatIndex.lean`, `SubseqRat.lean`, `RatAnnot.lean`) | `PartB/WeightedStatements.lean` |

**The four claims inside the proof of Theorem `thm:subsequential-functions`.**
The Lean proof reorganises them, so the declarations named above are not literal
renderings and the correspondence should be read with care.

* Claim `claim:bounded-extensions` says that a string that can be extended into the
  domain of `f` can be extended into it by a string of bounded length.  That is
  literally `Transducers.Subseq.exists_short_extension`.  The declaration that the
  table names first, `Transducers.Subseq.delay_bound`, is the *next* step: the bound
  `M0` on the length of the branching part, which the book obtains from this claim
  together with bounded variation.
* Claim `claim:computing-branching-part` says that the branching part takes finitely
  many values and that the inputs with a given value form a regular language.
  `Transducers.Subseq.key_drop` says instead that the branching part is determined by
  the Myhill–Nerode state of the input, which is the form in which the construction
  uses it.
* Claim `claim:offsets-are-regular` is treated the same way:
  `Transducers.Subseq.incr_congr` says that the offset at a letter is determined by
  the state.
* Claim `claim:eliminating-negative-letters` says that the reduced form of a
  sequential function with outputs in the free group over `B` is sequential.  The
  free group is not used at all in the Lean proof: the transducer emits the
  non-branching part with a bounded delay, and `Transducers.Subseq.exists_deletion_bound`
  — extending the input never shortens the non-branching part by more than a fixed
  constant — is what bounds that delay.

Supporting files for Part B: `Atomize.lean` (every nfa with output is equivalent to one whose
transitions read and write at most one letter), `RatComp.lean` (Theorem
`thm:composition-rational-relations`), `RatCont.lean` (Theorem `thm:continuity-rational-relations`),
`HomComplement.lean` (Claim `claim:homomorphism-complement-rational`), `MealyChar.lean` (Theorem
`thm:mealy-machine-independent`), `Typing.lean` (Claim `claim:typing-length-preserving`),
`LenNormalForm.lean` (Lemma `lem:characterisation-length-preserving`: the type
`τ q = |output| − |input|` of a state and the automaton whose states carry the output that is
produced but not yet emitted, or emitted but not yet produced), `SeqChar.lean` (Theorem
`thm:sequential-function-independent`: the canonical sequential transducer, whose states are the
Myhill–Nerode classes of the length-modulo and suffix languages), `RegularAux.lean` (regularity of
the auxiliary languages), `OutLang.lean` (for a fixed input, the set of outputs is a regular
language over the output alphabet) and `EpsElim.lean` (Lemma `lemma:eliminate-epsilon-transitions`).

The files added for Theorem `thm:subsequential-functions` are:

* `Lcp.lean` — the longest common prefix `lcp2` of two strings and its relation
  to the left distance of Definition `def:left-distance`.
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

The files added for Theorem `thm:machine-independent-rational-functions` are:

* `RatIndex.lean` — the equivalence relation `BoundedVarRel` (`w₁ ∼ w₂` if the
  left distances `‖f (w w₁), f (w w₂)‖` are bounded uniformly in `w`), the proof
  that it is an equivalence relation and a left congruence, and the easy
  implication: for a rational function, presented as a bimachine, two strings
  giving the same state of the suffix automaton are equivalent, so the relation
  has finite index.
* `SubseqRat.lean` — the graph of a subsequential function is a rational
  relation (a subsequential transducer is turned into an nfa with output with
  one extra final state).
* `RatAnnot.lean` — the converse implication.  Every letter of the input is annotated with the
  equivalence class of the suffix that follows it; the annotation is a rational relation, the
  correctly annotated strings form a regular language, and the partial function sending a correctly
  annotated string to the value of `f` on the underlying string is continuous and has bounded
  variation, hence subsequential by Theorem `thm:subsequential-functions`.  Composing the two
  rational relations gives the graph of `f`.

The files added for Lemma `lem:closure-weighted-automata-precomposition` and Theorem
`thm:characterisation-rational-functions-weighted-automata` are:

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
* `WeightedPrecomp.lean` — Lemma `lem:closure-weighted-automata-precomposition`: the product of a
  bimachine for the rational function `f` (Theorem `thm:bimachines`) with the linear representation
  of the weighted automaton for `h`.  Its states are triples consisting of the state of the prefix
  automaton at the current gap, the *guessed* state of the suffix automaton at that gap, and a state
  of the linear representation; the transition reading a letter carries the matrix entry of the
  output block produced at the previous gap.  The guesses are determined by the input, so the sum
  over the accepting runs is exactly `h (f w)`.
* `WeightedRegular.lean` — the implication "⇐" of Theorem
  `thm:characterisation-rational-functions-weighted-automata`: over the semiring of languages the
  map `v ↦ {v}` is computed by a weighted automaton, so the hypothesis gives a weighted automaton
  over that semiring computing `w ↦ {f w}`.  A concatenation of languages that is nonempty and
  contained in a singleton has singleton factors, so keeping the transitions labelled by a singleton
  language turns this automaton into an nfa with output computing `f`.

The files added for Theorems `thm:bimachines`, `lem:uniformisation` and `thm:rational-primes` are:

* `Unambig.lean` — unambiguisation: the runs of an ε-free nfa with output over a
  fixed input are ranked by the *key* `runKey`, a number whose base-`K` digits
  are the ranks of the transitions; the automaton `unambAut` follows a run while
  keeping track of the set of states reachable by a run with a smaller key, and
  accepts exactly the least accepting run.  Hence every ε-free nfa with output
  whose relation is total contains an unambiguous one with the same domain
  (`exists_unambiguous_of_epsFree`).
* `Uniform.lean` — Lemma `lem:uniformisation`: choosing one output string in each language of the
  extended ε-free automaton of Lemma `lemma:eliminate-epsilon-transitions` gives an ordinary nfa
  with output contained in the relation, which is unambiguised as above; the same argument gives an
  unambiguous ε-free automaton for every rational function
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
  Theorem `thm:rational-primes`: Mealy machines, homomorphisms and the separator function are
  read directly as nfas with output, a right-to-left Mealy machine is a
  bimachine, and rational functions compose.
* `BimachPrime.lean` — the hard implication of Theorem `thm:rational-primes`: a bimachine is the
  composition of `w ↦ w#`, a right-to-left Mealy machine annotating the
  positions with the states of the suffix automaton, a left-to-right Mealy
  machine annotating them with the states of the prefix automaton, and a
  homomorphism; the two Mealy machines are decomposed by the Krohn–Rhodes
  Theorem, reversal turning a decomposition into a decomposition of the
  right-to-left variant.

#### The four conditional results of Part B

These four decidability statements are proved from **one explicit effectivity hypothesis**, in
exactly the style already used for Theorem `thm:undecidable-equivalence-rational-relations` (which
takes the undecidability of the Post correspondence problem as an explicit hypothesis).  Every other
ingredient — Schützenberger's bound *and its effective form*, the reduction of equivalence of
rational functions to equivalence of weighted automata, the derivation of
`thm:equivalence-rational-functions` from `thm:equivalence-weighted-automata`, and the two code
constructions needed for prefix preservation in `thm:decide-if-mealy` — is proved in full, with no `sorry`
anywhere in their dependencies.  Each of the four was checked with `#print axioms` and depends only
on `propext`, `Classical.choice`, `Quot.sound`.

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
* `WeightedDec.lean` — Theorems `thm:equivalence-weighted-automata` and
  `thm:zeroness-weighted-automata`: compute the bound from the two codes and compare the values on
  all strings of length at most the bound over the letters of the two codes; zeroness is the special
  case in which the second automaton is the empty one.
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
* `RatEqDec.lean` — Theorem `thm:equivalence-rational-functions`: the two coded functions are
  equivalent exactly when the two codes read the same letters, agree on the empty string, and the
  two symmetric products `pairW K M N` and `pairW K N M` are equivalent weighted automata, which is
  decided by Theorem `thm:equivalence-weighted-automata`.
* `PrefixCodes.lean` — the codes `dropCode c` (computing `w ↦ dropLast (f w)`)
  and `shiftCode c` (computing `w ↦ f (dropLast w)`); for a length preserving
  coded function, prefix preservation is exactly the equality of the two.
* `CodeRat.lean` — the function `codeFun c` described by a code over its own
  finite alphabets `InA c` and `OutA c`; it is rational, it is computed by a
  Mealy machine exactly when the coded relation is length preserving and prefix
  preserving, and the property appearing in Theorem `thm:decide-if-mealy` is equivalent to
  `IsMealy (codeFun c)`.
* `MealyDec.lean` — Theorem `thm:decide-if-mealy`: decide length preservation with Lemma
  `lem:decide-if-length-preserving` and prefix preservation with Theorem
  `thm:equivalence-rational-functions` applied to `dropCode c` and `shiftCode c`.

### Part C: Regular functions

| Book | Lean | Status | File |
| --- | --- | --- | --- |
| Definition `def:regular-functions` (regular functions) | `Transducers.IsRegularFun`, `Transducers.RegularFam` | — | `PartC/RegularDef.lean` |
| Theorem `thm:regular-functions-are-continuous-and-closed-under-composition` (continuity, composition) | `Transducers.regular_continuous`, `Transducers.regular_comp` | proved (continuity by induction on the decomposition into primes, `ContAux.lean`) | `PartC/Statements.lean` |
| Lemma `lem:reversal-duplication-continuous` (reversal, duplication) | `Transducers.reverse_duplicate_continuous` | proved (`ContAux.lean`) | `PartC/Statements.lean` |
| Lemma `lem:map-lifting-continuous` (map lifting) | `Transducers.mapLift_continuous` | proved (Myhill–Nerode, `ContAux.lean`) | `PartC/Statements.lean` |
| Theorem `thm:decidable-equivalence-regular` (decidable equivalence) | `Transducers.regular_equivalence_decidable`; the book's proof: `Transducers.isWeighted_comp_regular`, `Transducers.isWeighted_comp_mapReverse`, `Transducers.isWeighted_comp_mapDuplicate`, `Transducers.exists_injective_weighted`, `Transducers.regularFun_eq_iff_weighted_eq`, `Transducers.regularFun_eq_iff_weighted_zero`, `Transducers.regularFun_eq_of_short`, `Transducers.exists_twoWayCode_bound` | the mathematical content of the book's proof is **proved** (`WeightedLin.lean`, `WeightedMapLift.lean`, `WeightedRegClosure.lean`): the reduction to zeroness of weighted automata over `ℚ` through the prime decomposition, with the constructions for map reverse (transposition of the matrices of a linear representation, where commutativity of the semiring is used) and map duplicate (Kronecker squares), the injective encoding of output strings by rationals, and the resulting bound reducing equivalence to a finite check. The decidability statement on *codes*, `Transducers.regular_equivalence_decidable`, is **proved from two explicit effectivity hypotheses** (`EffectiveTwoWayEvalEq` and `EffectiveTwoWayBound` of `PartC/EffectiveReg.lean`, `PartC/RegEqDec.lean`), exactly as Theorems `thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata` are: what those hypotheses isolate is the missing `Primrec`/`Computable` arithmetic on `ℤ` and `ℚ`. The *existence* of the equivalence bound, the mathematical content of the second hypothesis, is proved (`Transducers.exists_twoWayCode_bound`, `PartC/RegCodeBound.lean`) | `PartC/Statements.lean` |
| Conjecture `conj:regular-via-weighted-automata` (regular functions via weighted automata) | — | not formalised: it is an open conjecture of the book, not a result | — |
| Definition `def:two-way-transducer` (two-way transducer) | `Transducers.TwoWay`, `Transducers.IsTwoWay` | — | `PartC/TwoWayCont.lean` |
| Theorem `thm:continuity-2dfas` (continuity) | `Transducers.twoWay_continuous` | proved (`TwoWayCont.lean`, from Shepherdson's Theorem in `TwoDFA.lean`) | `PartC/Statements.lean` |
| Lemma `lem:compute-configuration-graph` (computing the configuration graph) | `Transducers.twoWay_isRationalFun_enc`; the main observation it rests on: `Transducers.twoWay_encLang_isRegular` | **proved** (`ConfGraph.lean`, `ConfGraphRun.lean`, `ConfGraphAnnot.lean`, `ConfGraphReg.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`).  The alphabet `C` of the book is `Transducers.CLet` and the representation is `Transducers.TwoWay.enc` | `PartC/Statements.lean` |
| Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L` (output string of the configuration graph in `L`) | `Transducers.twoWay_encOutputLang_isRegular` | **proved** (`ConfGraphReg.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`), for a transducer that computes a total function, which is taken as an explicit hypothesis — see *Divergences from the book* above.  The output string of a representation is the string printed by the transducer `Transducers.TwoWay.pathTrans`, which walks along the represented graph; on a representation it is the output of the transducer itself (`Transducers.TwoWay.computes_enc`) | `PartC/Statements.lean` |
| Lemma `lem:output-of-snake-graph-is-regular` (the output of a snake graph is regular) | `Transducers.SnakeGraph.snakeOut_isRegular`; the general form it is proved from: `Transducers.boundedWidth_isRegular` | **proved** (axioms: `propext`, `Classical.choice`, `Quot.sound`).  Stated as in the book, over the alphabet `Transducers.SnakeLetter Q B` of snake letters (`SnakeAlph.lean`), whose regular language of snake graphs is `SnakeAlphLoc.lean`, `SnakeAlphChar.lean`, `SnakeAlphLocLang.lean`, `SnakeAlphCyc.lean` and whose output is computed by the walking transducer of `SnakeAlphRun.lean`; the general form `boundedWidth_isRegular`, for the width-`k` output function `TwoWay.widthOut` of a two-way transducer, is proved in `SnakeReg.lean`, on top of `SnakeBase.lean`, `SnakeWalk.lean`, `SnakeRec.lean`, `SnakeLoop.lean` and the checking automaton of `SnakeStage1.lean`/`SnakeChk*.lean`.  Both forms are proved for every `k : ℕ` rather than only for `k ∈ {1, …, \|Q\|}`, which is more general | `PartC/SnakeAlphReg.lean`, `PartC/SnakeReg.lean` |
| Theorem `thm:composition-of-two-way-transducers` (composition) | `Transducers.twoWay_comp` | proved (`TwoWayRun.lean`, `TwoWayVisit.lean`, `TwoWayAnnot.lean`, `TwoWayAnnotBim.lean`, `TwoWayCompAux.lean`, `TwoWayCompPred.lean`, `TwoWayComp.lean`, `TwoWayCompFinal.lean`) | `PartC/Statements.lean` |
| Lemma `lem:2dfa-precomposition-with-mealy` (pre-composition with Mealy machines) | `Transducers.twoWay_precomp_mealy` | proved | `PartC/Statements.lean` |
| Corollary `cor:2dfa-closure-under-composition` (pre-composition with rational functions) | `Transducers.twoWay_precomp_rational` | proved (`TwoWayHom.lean`, `TwoWayBlock.lean`, `TwoWayErase.lean` and `TwoWayRat.lean`, from Theorem `thm:rational-primes` and Lemma `lem:2dfa-precomposition-with-mealy`) | `PartC/Statements.lean` |
| Corollary `cor:2dfa-computes-all-regular-functions` (regular ⊆ two-way) | `Transducers.regularFun_isTwoWay`, `Transducers.isTwoWay_of_isRegularFun` | proved (`TwoWaySweep.lean`, `TwoWayRegular.lean`, from Corollary `cor:2dfa-closure-under-composition` and Theorem `thm:composition-of-two-way-transducers`) | `PartC/Statements.lean` |
| Theorem `thm:2dfa-decomposition-into-primes` (two-way = regular) | `Transducers.twoWay_iff_regular`, `Transducers.twoWay_isRegular` | **both implications are proved**: the right-to-left one is Corollary `cor:2dfa-computes-all-regular-functions` above, and the left-to-right one, `Transducers.twoWay_isRegular` (two-way ⊆ regular, the inclusion printed in Corollary `cor:2dfa-computes-all-regular-functions`), is reduced to the snake lemma `Transducers.boundedWidth_isRegular` of `SnakeReg.lean`, whose base cases `k ≤ 1` are in `SnakeBase.lean`, whose combinatorial content is in `SnakeWalk.lean`, `SnakeRec.lean` and `SnakeLoop.lean`, and whose induction step `Transducers.boundedWidth_isRegular_step` is proved through the checking automaton of stage 1 (`SnakeStage1.lean`, `SnakeChk*.lean`); the whole theorem depends only on `propext`, `Classical.choice`, `Quot.sound` — see *How Theorem `thm:2dfa-decomposition-into-primes` is proved* below | `PartC/Statements.lean` |
| Lemma `lem:regular-closure-properties` (closure properties) | `Transducers.regular_closure_properties` | **proved** (`MapLiftAux.lean`, `MapLiftRat.lean`, `MapLiftPrime.lean`, `RegMapLift.lean`, `RatSeq.lean`, `RegClosure.lean`) | `PartC/Statements.lean` |
| Claim `claim:conditional` (disjoint sums) | `Transducers.sum_of_regular` | **proved** (`SumShape.lean`, `SumPrime.lean`, `SumReg.lean`, `RegSum.lean`), in the corrected form — the claim as printed is false on the empty input, see *An error in Claim `claim:conditional`* below | `PartC/Statements.lean` |
| Definition `def:sst` (sst) | `Transducers.SST`, `Transducers.IsSST` | — | `PartC/SSTDef.lean` |
| Theorem `theorem:sst-two-way-equivalence` (sst = regular) | `Transducers.sst_iff_regular` | both implications are **proved** (`SSTComp.lean`, `SSTMealyRev.lean`, `SSTMealyFF.lean`, `SSTMealy.lean`, `SSTMapRev.lean`, `SSTMapDup.lean`, `SSTRegular.lean` for `regular ⊆ sst`; `SSTNorm.lean`, `SSTWalk.lean`, `SSTTwoWay.lean` for `sst ⊆ two-way`), and since Theorem `thm:2dfa-decomposition-into-primes` is now proved the statement depends only on `propext`, `Classical.choice`, `Quot.sound` — see *The proof of Theorem `theorem:sst-two-way-equivalence`* below | `PartC/Statements.lean` |
| Theorem `thm:mso-logic-languages` (mso = regular languages) | `Transducers.regular_iff_msoDefinable` | **proved** (`MSO.lean`, from `MSOSyntax.lean`, `RegAut.lean`, `MSOAnnot.lean`, `MSOBuchi.lean`) | `PartC/MSO.lean` |
| Lemma `lem:mso-free-variables` (formulas with free variables) | `Transducers.mso_annotated_regular` | **proved** (`RegAut.lean`, `MSOSyntax.lean`, `MSOAnnot.lean`) | `PartC/MSO.lean` |
| Definition `def:mso-relabeling` (mso relabelling) | `Transducers.MSORelabelling`, `Transducers.IsMSORelabelling` | — | `PartC/MSODef.lean` |
| Theorem `thm:logic-rational-functions` (rational = mso relabelling) | `Transducers.rational_iff_msoRelabelling` | **proved** (`MSO.lean`, from `MSORatRelab.lean`, `MarkStr.lean`, `MarkLogic.lean`, `MarkBimach.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) | `PartC/MSO.lean` |
| Claim `claim:transition-formula` (the transition formula) | `Transducers.RatRelab.exists_form` | proved (`MSORatRelab.lean`), as the internal step of Theorem `thm:logic-rational-functions`; stated for the index of a bimachine rather than for an unambiguous transducer | `PartC/MSORatRelab.lean` |
| Claim `claim:mso-annotation-regular` (annotated relabellings) | `Transducers.msoRelabelling_annotation_regular` | **proved** (`MSORelab.lean`, from Lemma `lem:mso-free-variables`) | `PartC/MSO.lean` |
| Definition `def:mso-transduction` (mso transduction) | `Transducers.MSOTransduction`, `Transducers.IsMSOTransduction` | — | `PartC/MSODef.lean` |
| Theorem `thm:logic-regular-functions` (mso transductions = regular) | `Transducers.msoTransduction_iff_regular` | both implications are **proved** (`MSO.lean`, from `MSOReg.lean`, `MSOWalkData.lean`, `WalkAut.lean`, `MSOWalkForms.lean`, `MSONorm.lean`, `SortedEnum.lean` for `mso ⊆ regular`; `TwoWayMSO.lean`, `RunProbe.lean`, `RunMark.lean`, `RunElts.lean`, `MarkLogic2.lean` for `regular ⊆ mso`), and since Theorem `thm:2dfa-decomposition-into-primes` is now proved the statement depends only on `propext`, `Classical.choice`, `Quot.sound` — see *The proof of Theorem `thm:logic-regular-functions`* below | `PartC/MSO.lean` |
| Lemma `lem:logic-reduction-to-type-n` (reduction to a normalised type) | `Transducers.MSOTransduction.exists_norm` | proved (`MSONorm.lean`), as the normalisation of the type τ inside the proof of Theorem `thm:logic-regular-functions` | `PartC/MSONorm.lean` |
| Lemma `lem:logic-precomputation` (formulas via rational functions) | `Transducers.mso_formulas_via_rational` | **proved** (`MSO.lean`, from `MSOPrecomp.lean`, `MarkStr.lean`, `MarkBimach.lean`, `MarkDelay.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) | `PartC/MSO.lean` |
| Theorem `thm:logic-aperiodic` (first-order = aperiodic) | `Transducers.foDefinable_iff_aperiodic_dfa` | **proved** (`MSO.lean`, from `FOTypeDFA.lean` and `FOMealy.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) | `PartC/MSO.lean` |
| Definition `def:k-types` (k-types) | `Transducers.tp` | — | `PartC/KTypes.lean` |
| Lemma `lem:k-types-fo-equivalence` (types and formulas) | `Transducers.tp_eq_iff_fo_equiv` | **proved** (`MSO.lean`, from `FOComp.lean` and `FOHintikka.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) | `PartC/MSO.lean` |
| Claim `claim:fo-composition-quantifier-rank` (compositionality at a fixed quantifier rank) | `Transducers.sat_iff_of_kEquiv` | proved (`FOComp.lean`), as the internal step of the proof of Lemma `lem:k-types-fo-equivalence` | `PartC/FOComp.lean` |
| Lemma `lem:k-types-properties` (properties of types) | `Transducers.tp_properties` | proved (`KTypes.lean`) | `PartC/MSO.lean` |
| Theorem `thm:fo-rational-functions` (first-order relabellings) | `Transducers.foRelabelling_iff_aperiodicBimachine` | **proved** (`MSO.lean`, from `FORelabBimach.lean` for `first-order relabelling ⊆ aperiodic bimachine` and `FOBimachRelab.lean` for the converse, on top of `FORev.lean` and `FOPos.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) | `PartC/MSO.lean` |
| Theorem `nolabel:thm-fo-transduction-into-primes` (first-order transductions) | **removed from the formalised theorems at the user's request** (its statement is kept, commented out, in `MSOOpen.lean`) | not formalised as a theorem any more. What remains is the inclusion `compositions of primes ⊆ first-order transductions`, **proved** as `Transducers.isFOTransduction_of_compClosure` (`FOTransPrimeComp.lean`, on top of the closure under composition of `FOTransComp.lean` and the three primes of `FORelabTrans.lean`, `FOTransRev.lean` and `FOTransDup.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) — see *Theorem `nolabel:thm-fo-transduction-into-primes`: what was removed and what remains* below | `PartC/MSOOpen.lean`, `PartC/FOTransPrimeComp.lean` |

Supporting files for Part C: `ContAux.lean` (continuity is closed under
composition; letter-to-letter maps, reversal, duplication and the map lifting of
a continuous function are continuous), `TwoDFA.lean` (deterministic two-way
automata and Shepherdson's Theorem: their languages are regular, proved with the
Myhill–Nerode theorem and the profile of a prefix), `TwoWayCont.lean` (the
definitions of two-way transducers, and the two-way automaton obtained by
running a deterministic automaton on the output) and `KTypes.lean` (`k`-types
and Lemma `lem:k-types-properties`).

The files added for Corollary `cor:2dfa-closure-under-composition` are:

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
* `TwoWayRat.lean` — Corollary `cor:2dfa-closure-under-composition`: an arbitrary homomorphism is a
  block homomorphism whose blocks are padded with a fresh letter, followed by the erasing
  homomorphism that deletes the padding; with Lemma `lem:2dfa-precomposition-with-mealy`, with
  pre-composition with reversal and with appending a letter, this covers all the prime rational
  functions of Theorem `thm:rational-primes`, and the general case follows by induction on the
  composition.

The files added for Theorem `thm:composition-of-two-way-transducers` are:

* `TwoWayRun.lean` — the run of a two-way transducer indexed by time: it is
  injective up to the halting time, so a configuration on the run has a *unique*
  predecessor on the run (`TwoWay.pred_unique`).  This is what makes it possible
  to walk backwards along the run.
* `TwoWayVisit.lean` — the configurations that lie on the run form a regular
  property of the input: mark one letter with a state and a side, and the marked
  inputs whose run visits the marked cut in the marked state form a regular
  language, by Shepherdson's Theorem applied to the two-way automaton that
  accepts as soon as the run reaches the marked cut.  This replaces, inside the
  proof of Theorem `thm:composition-of-two-way-transducers`, the analysis of the
  reachable configuration graph of Lemma `lem:compute-configuration-graph`; it is
  also what the string representation of that graph is built from, in
  `ConfGraphAnnot.lean`.
* `TwoWayAnnot.lean`, `TwoWayAnnotBim.lean` — the annotation of every position
  of the input by a window of three letters, the state of the deterministic
  automaton of the previous item after the prefix, and the acceptance function
  of the suffix.  It is computed by a bimachine, hence is a rational function
  (Theorem `thm:bimachines`), and from the annotations of the two letters adjacent to a cut
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
* `TwoWayCompFinal.lean` — Theorem `thm:composition-of-two-way-transducers` in general: the outputs
  of the first transducer are padded with a blank letter to a common length, which is harmless
  because two-way transducers are closed under pre-composition with the erasing homomorphism that
  deletes the blanks.

#### The string representation of the reachable configuration graph

The book proves Theorem `thm:continuity-2dfas` through a string representation of
the reachable configuration graph of a two-way transducer over a finite alphabet
`C`, and states two lemmas about it, Lemma `lem:compute-configuration-graph` and
Lemma `lem:check-if-output-string-of-configuration-graph-belongs-to-L`.  Both are
now formalised, in four files.

* `ConfGraph.lean` — the alphabet and the representation.  A letter of `C` for a
  non-empty input is `Transducers.Slice Q L`, a bipartite graph on two copies of
  the state set: a function which assigns to each vertex — a state `q` in the
  left copy `(false, q)`, standing for the cut to the left of the sliced letter,
  or in the right copy `(true, q)`, the cut to its right — its unique outgoing
  edge, which is either absent (`VOut.nil`), or goes to a state of the *other*
  copy with an output label (`VOut.move`), or leads to the halting vertex
  (`VOut.halt`).  The labels range over `TwoWay.Lab M`, the finite set of output
  strings that occur in the transition function, which is the book's reason for
  `C` being finite.  `Transducers.CLet Q L` adds the book's special letter for
  the empty input, carrying the output produced when the transducer halts
  immediately.  `TwoWay.enc M w` is the representation of the reachable
  configuration graph of `M` on `w`: one letter per input position, in which a
  vertex not visited by the run gets `VOut.nil`.  `TwoWay.pathTrans M` is the
  two-way transducer over `C` that walks along a represented graph and prints the
  labels it meets; this is what "the output string of the configuration graph"
  means.
* `ConfGraphRun.lean` — the representation and the run semantics of
  `TwoWayRun.lean` agree: `TwoWay.computes_enc` says that if `M` outputs `v` on
  `w` then `pathTrans M` outputs `v` on `enc M w`, and `TwoWay.computes_enc_iff`
  is the equivalence.  So the two views are interchangeable.
* `ConfGraphAnnot.lean` — the representation is read off the annotation of
  `TwoWayAnnot.lean`: `TwoWay.enc_eq_map_annot` writes `enc M w`, for `w ≠ []`,
  as the image of `annot D w` under a letter-to-letter map, and
  `TwoWay.validLang_isRegular` says that the correct annotations form a regular
  language.  This is where the reachability information comes from: which
  configurations lie on the run is regular in the input by `TwoWayVisit.lean`.
* `ConfGraphReg.lean` — **the main observation** of the book, that the strings
  over `C` which represent a reachable configuration graph form a regular
  language (`Transducers.twoWay_encLang_isRegular`, in the form
  `TwoWay.encImage_isRegular` for the graphs of the inputs in a regular language),
  and the two lemmas on top of it.  Lemma `lem:compute-configuration-graph` is
  the annotation, a rational function, followed by a letter-to-letter map; Lemma
  `lem:check-if-output-string-of-configuration-graph-belongs-to-L` is the image
  under the representation of the regular language `{w | f w ∈ L}`, regular by
  the continuity argument of `TwoWayCont.lean`.

The proof of Theorem `thm:continuity-2dfas` in `Statements.lean` does not go
through the representation — it runs a deterministic automaton for the output
language inside the transducer and appeals to Shepherdson's Theorem — so the two
lemmas are proved independently of it and no earlier proof changed.

#### The conditional result of Part C

Theorem `thm:decidable-equivalence-regular`, in its form as a decision procedure on codes of two-way
transducers, is proved in the same style as Theorems `thm:equivalence-weighted-automata` and
`thm:zeroness-weighted-automata` of Part B: from explicit effectivity hypotheses, with everything
else discharged in full and with no `sorry` anywhere in its dependencies (`#print axioms` reports
only `propext`, `Classical.choice`, `Quot.sound`).  The unconditional statement is kept, commented
out, in `PartC/Statements.lean`.

The two hypotheses are in `PartC/EffectiveReg.lean`:

* `EffectiveTwoWayEvalEq` — there is a computable procedure which, given two
  codes of two-way transducers and an input, decides whether the two
  transducers have the same outputs on it (correctly at least when both codes
  describe total functions).  A deterministic two-way transducer promised to
  halt can be simulated, so this is a true statement about ordinary
  computability.
* `EffectiveTwoWayBound` — there is a computable function which, given two
  codes, returns a length bound after which agreement on all shorter inputs
  forces the two coded transducers to compute the same relation.  Only its
  *computability* is assumed: that such a bound exists is proved, in
  `PartC/RegCodeBound.lean`, as `Transducers.exists_twoWayCode_bound`.

Everything else is proved:

* `RegCodeSan.lean` — a code is a finite table, so it cannot distinguish two
  letters that are both absent from it; renaming the letters outside the table
  does not change the computed relation (`Transducers.RegDec.twoWayCodeRel_map`,
  by a step-by-step correspondence between the two runs).  This is what makes
  the test finite: it is enough to compare the two codes on the strings over
  their letters together with one fresh letter.
* `RegCodeBound.lean` — the existence of the bound.  A code describes a transducer over the infinite
  alphabet `ℕ` with the infinite state set `ℕ`, while Theorem `thm:2dfa-decomposition-into-primes`
  speaks about finite alphabets; but only finitely many letters, output letters and states occur in
  a code, so the code also describes a transducer `finAut` over those finite sets, whose runs
  correspond step by step to the runs of the coded transducer.  Its computed function is regular
  (`Transducers.isRegularFun_of_isTwoWay`), so `Transducers.regularFun_eq_of_short` supplies the
  bound, and the determinism of two-way transducers (`TwoWay.computes_unique`) turns the equality of
  the two computed functions back into the equality of the two coded relations.
* `RegEqDec.lean` — the decision procedure, assembled as in
  `PartB/WeightedDec.lean`, and its computability.

#### Corollary `cor:2dfa-computes-all-regular-functions`: the typo is gone from the book

An earlier edition printed the corollary as "if a function is computed by a two-way transducer, then
it is regular", which is the *opposite* of what its proof establishes.  The sources now read "Every
regular function is computed by a two-way transducer" (`2dfa.tex`), which is the direction that this
project formalises, so there is no longer a divergence here.  The comment in `PartC/Statements.lean`
that records the printed statement and explains the typo is a leftover from that edition; the
statement it discusses, `two-way ⊆ regular`, is the left-to-right implication of Theorem
`thm:2dfa-decomposition-into-primes`, stated and proved there as `Transducers.twoWay_isRegular`, and
it is not duplicated as a separate statement.

Corollary `cor:2dfa-computes-all-regular-functions` is formalised as
`Transducers.regularFun_isTwoWay` and proved in full.  Its ingredients are:

* `TwoWaySweep.lean` — the two-way transducer for the identity, closure under
  post-composition with a letter-to-letter map, and the *block sweeping*
  transducer: on each block of the input (a maximal factor without separators)
  it sweeps left to right, right to left and left to right again, emitting a
  string for each letter it passes.  Map reverse is the instance in which only
  the middle sweep produces output, map duplicate the one in which only the two
  outer sweeps do.
* `TwoWayRegular.lean` — closure under pre-composition with a letter-to-letter map (a special case
  of Corollary `cor:2dfa-closure-under-composition`), and the two instances of the sweeping
  transducer.  The corollary then follows by induction on the composition tree of the regular
  function, using Corollary `cor:2dfa-closure-under-composition` for the rational primes and Theorem
  `thm:composition-of-two-way-transducers` for the composition step.

#### An error in Claim `claim:conditional`

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

`PartC/Statements.lean` keeps the statement as printed, commented out, next to the corrected
statement `Transducers.sum_of_regular`, which restricts the first two clauses to *nonempty* inputs,
assumes `[Nonempty B₁] [Nonempty B₂]`, and leaves the value on the empty input unspecified.  The
correction is harmless for the use the book makes of the claim: in the proof of Lemma
`lem:regular-closure-properties` the blocks the sum is applied to always carry a marker and are
therefore nonempty.

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

#### How Theorem `thm:2dfa-decomposition-into-primes` is proved

Theorem `thm:2dfa-decomposition-into-primes` is **proved**, in both directions.  The right-to-left
implication is Corollary `cor:2dfa-computes-all-regular-functions`.  The left-to-right implication,
`Transducers.twoWay_isRegular`, follows the book: it decomposes a two-way transducer as

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

What remained, and is now proved, is the **induction step**, in
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
Section *Two-way transducers* now contains no `sorry` at all.

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

  The construction is the book's one: a rational function appends a copy of the separator at the end
  of each block, map duplicate produces `w₀$w₀$ # ⋯ # wₙ$wₙ$`, a bilateral rewriting (`RatBi.lean`)
  deletes the first copy of `w₀` and the second copy of `wₙ` and re-brackets the rest, the map
  lifting of `f` (Lemma `lem:regular-closure-properties`) is applied to every block and a
  homomorphism erases the separators.  The book's stage 3 -- duplicating each block once more,
  because each block carries both a loop part and a progress part -- is not needed separately:
  taking for `f` a concatenation `f = g₁ · g₂ ⋯ g_m` of boundedly many regular functions is already
  allowed, by the concatenation closure of Lemma `lem:regular-closure-properties`.  Likewise,
  cutting a factor out of a block by regular conditions and applying a regular function to it is the
  composition of `Transducers.isRationalFun_biFilter` with that function.
* The *order in time of the visits of the run to a cut*, which is what the
  recursion defining the record-breaking columns refers to, is available as a
  rational annotation of the input,
  `Transducers.TwoWay.exists_rational_visitOrder_annot`
  (`TwoWayOrder.lean`, `TwoWayAnnotOrd.lean`): a two-way automaton decides, for
  a cut marked with a pair of states `(q₁, q₂)`, whether the run visits it in
  `q₁` before it ever visits it in `q₂`, its language is regular, and the
  corresponding bimachine annotation makes the first and the last visit to every
  cut readable locally.

The book's **stage 1** -- the rational function that marks the record-breaking
columns and the pieces that they delimit -- is proved in the shape in which the
book states it: *"a nondeterministic automaton with output can guess the
record-breakers, and then check that they satisfy the conditions in the
definition"*.  What has to be produced is the language of the **checking**
automaton, that is, a regular language of correctly annotated inputs containing
an annotation of every input:

```lean
theorem exists_regular_snakeLang [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) :
    ∃ L : Language (A × TwoWay.SnakeDatum A Q K), L.IsRegular ∧
      (∀ u ∈ L, TwoWay.SnakeRel M K (homOf (TwoWay.snakeIn K) u)
        (homOf (TwoWay.snakeOutLet K) u)) ∧
      (∀ w : List A, ∃ u ∈ L, homOf (TwoWay.snakeIn K) u = w)
```

(`SnakeStage1.lean`, proved in `SnakeChkMain.lean`).  The annotation is kept
letter to letter -- a letter of the input together with a `TwoWay.SnakeDatum`,
that is, the bit marking a block boundary before (or, at the last letter, after)
it and the data of the piece slots -- so that a position of an annotation is a
position of the input; the separators are inserted afterwards by the
homomorphism `TwoWay.snakeOutLet`.

What the checking automaton verifies is not the record-breaker decomposition
itself but a weaker, purely local, condition: that the annotation describes a
**chain of pieces**, `TwoWay.Chk.ChainData` (`SnakeChkData.lean`).  A chain cuts
the input into blocks and gives, for every pair of neighbouring blocks and every
piece slot, a window inside that pair together with the parameters of a window
transducer, subject to conditions that only relate a piece to the next one: the
first piece starts at the left end of the input in the initial state,
consecutive pieces meet at a common cut in a common state, the last piece halts,
and every window satisfies the **window condition** `TwoWay.Chk.WinCond`, which
is a regular language of windows (`TwoWay.Chk.isRegular_winCond`).  The whole
mathematical content of the *soundness* of the automaton is then
`TwoWay.Chk.runOut_of_chainData`: the outputs of the pieces of a chain
concatenate to the output of the run.  Reading a chain off an accepted
annotation (`SnakeChkRead.lean`) and building an annotation from a chain
(`SnakeChkBuild.lean`) is bookkeeping, and the regularity of the accepted
language is the conjunction of finitely many regular conditions on the annotated
alphabet (`SnakeChkEnc.lean`, `SnakeChkVerify.lean`, `SnakeChkAcc.lean`).

The *completeness* of the automaton -- that every good input carries a chain --
is the record-breaker decomposition itself:

```lean
theorem nonempty_chainData_of_good [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) {w : List A} (hgood : GoodInput M K w) :
    Nonempty (ChainData M K w)
```

(`SnakeChkRB.lean`).  The blocks are cut at the record-breaking columns
(`TwoWay.snakeY`), the `2K+1` piece slots of a pair are the `2K` halves of the
`K` excursions of its record-breaking column followed by its progress part, and
the confinement of each window to its pair of blocks is the one of
`SnakeConfine.lean`.  What this adds to the earlier
`TwoWay.exists_isSnakeMarking` (`SnakeData.lean`), which produces the windows and
the output identification but not the chain, is the chain structure, and it is
obtained by naming the data that `TwoWay.exists_pieceData` only asserted to
exist:

* the two states of a piece are the **states of the run** at the two times that
  delimit it (`TwoWay.qAt`, `SnakeChkPieceWin.lean`), so that the exit state of a
  piece is literally the entry state of the next one;
* the two cuts of a piece are the **positions of the head** at those two times,
  so that consecutive pieces automatically meet at a common cut;
* the two times themselves are named for every slot (`TwoWay.Chk.pcStart`,
  `TwoWay.Chk.pcEnd`, `SnakeChkSlot.lean`) and consecutive slots are shown to
  meet -- the halves of an excursion at its cutting point, the last excursion at
  the last visit to the record-breaking column (`TwoWay.excT_stab`), and the
  progress part of a pair at the first visit to the next record-breaking column;
* the window condition of each of the four kinds of piece is derived from the
  identification of that piece with the whole run of a window transducer
  (`TwoWay.Chk.winCond_kind_one` … `winCond_kind_four`,
  `SnakeChkPieceWin.lean`): for the kinds `1` and `2` the window run reaches the
  far end of the window in the announced state (`TwoWay.endLang`) and halts
  there, for the kinds `3` and `4` it halts inside the window
  (`TwoWay.haltLang`), and in all four cases it has width at most `K - 1`, which
  is what lets the induction hypothesis compute its output.

The three kinds of piece of the decomposition are then packaged uniformly
(`TwoWay.Chk.CrossOK`, `TwoWay.Chk.HaltOK`, `SnakeChkCross.lean`) and produced
slot by slot (`TwoWay.Chk.exists_slotOK`, `SnakeChkSlotOK.lean`), and
`SnakeChkRB.lean` checks that the slots chain.

Everything that turns the language of the checking automaton into the regular
marking function that the induction step consumes was already proved:

* `Transducers.isRationalRel_of_regular_nivat` (`PartB/GuessCheck.lean`): a
  regular language of annotations, read through one homomorphism and written
  through another, is a rational relation (one half of Nivat's theorem).  This
  is the "guess and check" step.
* `Transducers.exists_rationalFun_of_total_rel` (`PartB/UniformFun.lean`,
  Lemma `lem:uniformisation`): a total rational relation contains the graph of a rational
  function.  This is why no functionality of the guessing has to be proved.
* `TwoWay.exists_rational_snakeRel`, `TwoWay.exists_snakeMarking` and
  `TwoWay.widthOut_eq_pairMap` (`SnakeStage1.lean`) chain the three together and
  hand the induction step of `SnakeReg.lean` the equation
  `widthOut M K w = pairMap (blockFun M (K-1) (2K+1)) (ann w)` for every nonempty
  `w`; the empty input is treated separately, by a case distinction over the
  regular language `{[]}`.

`Transducers.twoWay_iff_regular`, `Transducers.twoWay_isRegular`,
`Transducers.boundedWidth_isRegular_step` and
`Transducers.TwoWay.Chk.nonempty_chainData_of_good` all depend only on `propext`,
`Classical.choice` and `Quot.sound`.

#### The alphabet of snake letters

The book states Lemma `lem:output-of-snake-graph-is-regular` over the alphabet
`C` in which snakes are represented: a letter is a bipartite graph whose vertices
are two copies of the state set `Q`, whose edges are directed and labelled with
output strings, and in which each vertex has at most one outgoing edge, which
must go to the other copy.  That alphabet is `Transducers.SnakeLetter Q B`
(`SnakeAlph.lean`): a letter is a function `Bool × Q → Option (Q × Option B)`,
where `(false, q)` is the copy of `q` at the cut to the left of the letter and
`(true, q)` the copy at the cut to its right.  A string `w` over `C` glues the
letters into a graph whose vertices are the pairs `(q, x)` of a state and a
column `x ≤ |w|`; it *represents a snake graph* when all its edges lie on a
single directed path (`SnakeGraph.RepresentsSnake`), and the output of that graph
is the concatenation of the labels along the path (`SnakeGraph.pathOut`).  The
function of the lemma is `SnakeGraph.snakeOut k`, which returns that output when
`w` represents a snake graph of width at most `k` and the empty string otherwise.

The book's form of the lemma, `SnakeGraph.snakeOut_isRegular`
(`SnakeAlphReg.lean`), is proved *from* the form the project already had,
`Transducers.boundedWidth_isRegular`, and not by repeating the induction on the
width.  Two things are needed.

* The strings that represent a snake graph of width at most `k` form a regular
  language.  `SnakeGraph.representsSnake_iff` (`SnakeAlphChar.lean`) replaces
  "all edges lie on one path" by four local-looking conditions -- out-degree at
  most one, in-degree at most one, at most one source, no directed cycle -- and
  each of them is regular: the degree conditions and the width condition are
  conditions on pairs of consecutive letters (`SnakeAlphLocLang.lean`), the
  uniqueness of the source is checked by a left-to-right automaton that
  remembers whether it has seen one source and whether it has seen two (same
  file), and acyclicity by one that carries the reachability relation between
  the vertices of the current column (`SnakeAlphCyc.lean`).
* On those strings the output of the graph is the output of the run of the
  two-way transducer `SnakeGraph.snakeTrans` that walks along the snake
  (`SnakeAlphRun.lean`): in the state `none` it sweeps right until it stands at
  the source, and from there it follows the outgoing edge of the current vertex,
  prints its label and moves to the column of the target
  (`SnakeGraph.computes_snakeTrans`).  That run halts, so its width is at most
  the number of states and the width-bounded output function of
  `boundedWidth_isRegular` already computes the output
  (`SnakeGraph.snakeOutIs_widthOut`).

The two are combined by the conditional of Lemma
`lem:regular-closure-properties`.

The two forms have the same content, but only one direction between them is
formalised: the book's form `SnakeGraph.snakeOut_isRegular` is *derived* from the
transducer form `boundedWidth_isRegular`, so as Lean statements the book's form
is the weaker of the two -- it is one instance of the general one, over the fixed
alphabet `SnakeLetter Q B`.  The converse derivation is not formalised; it holds
mathematically, because the reachable part of the run of a two-way transducer of
width at most `k` is a snake graph of width at most `k`, whose slice encoding is
obtained from the input letter by letter, so `widthOut M k` is the composition of
a letter-to-letter map with `snakeOut k`.  `SnakeGraph.snakeOut_isRegular` and
`Transducers.boundedWidth_isRegular` both depend only on `propext`,
`Classical.choice` and `Quot.sound`.

#### The proof of Theorem `theorem:sst-two-way-equivalence`

Both implications of Theorem `theorem:sst-two-way-equivalence` are formalised, and every file that
they use is sorry-free.

The implication `regular ⊆ sst` is `Transducers.isSST_of_isRegularFun`
(`SSTRegular.lean`).  It follows the book: sst's are closed under
post-composition with each prime regular function, so, since a regular function
is a composition of primes, with every regular function; applying this to the
identity sst gives the statement.  The case of a rational function is reduced,
as in the book, to Krohn–Rhodes (Theorem `thm:krohn-rhodes`), because the naive product
construction is not copyless: keeping a register `X_q` for the image of the
content of `X` read from the state `q` breaks copylessness at a concatenation
`X ↦ Y Z`, since the state reached after the content of `Y` need not depend
injectively on `q`.  For a reversible machine it does, and for a flip-flop
machine the content of a register is split at its last reset
(`SSTMealyRev.lean`, `SSTMealyFF.lean`).  For map reverse and map duplicate the
content of a register is kept as a tuple of strings, indexed by the position of
the separators inside it (`SSTMapRev.lean`, `SSTMapDup.lean`).

The implication `sst ⊆ regular` goes, as in the book, through Theorem
`thm:2dfa-decomposition-into-primes`: an sst is simulated by a two-way transducer
(`Transducers.isTwoWay_of_isSST`, `SSTTwoWay.lean`), and a two-way transducer computes a regular
function (`Transducers.twoWay_isRegular`).  The simulation itself is proved sorry-free. It has two
parts.

* `SSTNorm.lean` normalises the sst.  A two-way transducer cannot see the state of the sst before
  the position of its head, so every input letter is annotated with that state by a Mealy machine;
  the annotation is rational and two-way transducers are closed under pre-composition with rational
  functions (Corollary `cor:2dfa-closure-under-composition`).  Moreover a register may occur several
  times in a final output string — the copyless restriction constrains only the register updates —
  so `K + 1` copies of every register are kept, where `K` bounds the number of register occurrences
  in a final output string; all copies hold the same value, and the occurrences in a final output
  string are given pairwise distinct copies (`Transducers.tagWith`).  The result is a
  `Transducers.NSST` computing the same function on the annotated input
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

`Transducers.sst_iff_regular` is therefore **proved outright**: the last gap of Theorem
`thm:2dfa-decomposition-into-primes`, the induction step of the snake lemma, is closed (see *How
Theorem `thm:2dfa-decomposition-into-primes` is proved* above), and the statement depends only on
`propext`, `Classical.choice`, `Quot.sound`.

#### The proof of Theorem `thm:logic-regular-functions`

Both implications of Theorem `thm:logic-regular-functions`
(`Transducers.msoTransduction_iff_regular`) are formalised, and no file used by either of them
contains a `sorry`.

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
and `RunMark.lean`), and Theorem `thm:mso-logic-languages` turns them into formulas with one or two
free variables (`MarkLogic.lean`, `MarkLogic2.lean`).  The combinatorics of the
output list is in `FlatIndex.lean` and `RunElts.lean`.

*From mso transductions to regular functions* (`MSOReg.lean`).  The output universe is first
normalised (Lemma `lem:logic-reduction-to-type-n`, `MSONorm.lean`): the extra elements of the linear
type `τ = k · n + c` are attached to the first position of the input, which leaves a single finite
set of tags, a universe formula and letter formulas with one free variable, and an order formula
with two free variables.  A two-way transducer then *walks* the output order (`WalkAut.lean`): it
scans for the first element, outputs its letter, and asks whether it is the last element, whether
its successor sits in the same position, or to the right, or to the left; in the last two cases it
walks in that direction and stops at the first position where the automaton for "is the successor
of" accepts.  The questions are the mso formulas of `MSOWalkForms.lean`, whose meaning is expressed
through the increasing enumeration of the selected elements (`SortedEnum.lean`).  By Lemma
`lem:logic-precomputation` the unary questions are precomputed into the letters of a rational
letter-to-letter function `pre`, and the binary ones become regular languages of infixes of `pre w`,
read by a finite family of deterministic automata whose product -- together with the last letter
read, which is what answers the unary question at the end of a rightward scan -- is the automaton of
the walk (`MSOWalkData.lean`).  Finally `f` is the composition of `pre` with the function computed
by the walking transducer; since that transducer need not halt on the strings that are not of the
form `pre w`, what is composed with `pre` is its width-bounded output `TwoWay.widthOut`, a total
function that agrees with the run wherever the run halts and is regular by Theorem
`thm:2dfa-decomposition-into-primes`.

Exactly as for Theorem `theorem:sst-two-way-equivalence`, the inclusion `mso ⊆ regular` uses the
hard half of Theorem `thm:2dfa-decomposition-into-primes`; that half is now proved (see *How Theorem
`thm:2dfa-decomposition-into-primes` is proved* above), so `Transducers.msoTransduction_iff_regular`
is **proved outright** and depends only on `propext`, `Classical.choice`, `Quot.sound`.  The
converse inclusion `regular ⊆ mso`, `Transducers.isMSOTransduction_of_isTwoWay`, is proved outright
and depends only on `propext`, `Classical.choice`, `Quot.sound`.

#### The proof of Theorem `thm:fo-rational-functions`

Theorem `thm:fo-rational-functions` is the first-order counterpart of Theorem
`thm:logic-rational-functions`, and it is proved outright, following the book's proof of Theorem
`thm:logic-rational-functions` with aperiodicity added throughout and with Theorem
`thm:logic-aperiodic` and Lemma `lem:k-types-fo-equivalence` in place of Theorem
`thm:mso-logic-languages`.

From a first-order relabelling to an aperiodic bimachine
(`Transducers.isAperiodicBimachine_of_isFORelabelling`, `FORelabBimach.lean`): let `k` bound the
quantifier rank of the finitely many formulas of the relabelling.  The prefix automaton of the
bimachine computes the `k`-type of the prefix read so far and the suffix automaton the `k`-type of
the suffix; both transition functions are aperiodic, because `k`-types are (Lemma
`lem:k-types-properties`, `Transducers.transAperiodic_tpStep`).  By the compositionality of
first-order logic at a position (`Transducers.sat_const_iff_of_tp_split`, `FOPos.lean`, an
application of Claim `claim:fo-composition-quantifier-rank`), whether a formula of the relabelling holds
at a position depends only on the `k`-type of the prefix, the letter and the `k`-type of the suffix;
so the index chosen at a position, hence the output block, is a function of the bimachine's two
states, which is exactly the output function of a bimachine.  The one place where the two notions
differ is bookkeeping: a bimachine outputs one block per *gap*, one more than the number of
positions, while a relabelling outputs one block per position; the block of the last gap is appended
to the block of the last position, and the empty input is handled by `emptyOut`.

From an aperiodic bimachine to a first-order relabelling
(`Transducers.isFORelabelling_of_isAperiodicBimachine`, `FOBimachRelab.lean`):
the indices of the relabelling are the quadruples `(q, a, s, last?)` consisting
of a state of the prefix automaton, a letter, a state of the suffix automaton and
a Boolean.  The formula of such an index says that the prefix strictly before the
position drives the prefix automaton to `q`, that the letter is `a`, that the
suffix strictly after the position drives the suffix automaton to `s`, and that
the position is (or is not) the last one.  The first conjunct is a first-order
sentence by Theorem `thm:logic-aperiodic` (the language `{u | δ*(q₀,u) = q}` of an aperiodic
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

#### Theorem `nolabel:thm-fo-transduction-into-primes`: what was removed and what remains

Theorem `nolabel:thm-fo-transduction-into-primes` (the first-order transductions are exactly the
compositions of map reverse, map duplicate and first-order rational functions) has been **removed
from the formalised theorems at the user's request**.  Its statement, and the statement of its open
half, are kept only as comments in `PartC/MSOOpen.lean`; neither is a Lean declaration any more.
The family of primes `Transducers.FORegularFam` (`PartC/FOPrimeFam.lean`) and everything proved
about it are unaffected.

The inclusion from right to left -- every composition of primes is a first-order transduction -- is
**proved**, as `Transducers.isFOTransduction_of_compClosure` in `PartC/FOTransPrimeComp.lean`, by
induction on `CompClosure`.  It is not free, because in the mso case the corresponding inclusion is
obtained *through* Theorem `thm:logic-regular-functions` and the definition of regular functions as
compositions of primes, and that route is unavailable in the first-order setting.  It rests on four
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

The inclusion from left to right -- every first-order transduction is a composition of primes -- is
no longer part of the formalisation; it was the only `sorry` of Section *Logic*, and it has been
removed together with Theorem `nolabel:thm-fo-transduction-into-primes` itself.  The book does not
prove it either: it only states the result and leaves the proof "for a future edition of these
notes", with a sketch of what would be needed, namely first-order variants of (1) the lemma saying
that a string representation of the configuration graph of a two-way transducer can be computed, and
(2) the main step in the decomposition of two-way transducers into primes, which says that the
output string can be read off the configuration graph by a composition of primes -- "the second one
being more technical".  In this project those two ingredients are the contents of the dozen files
behind Theorem `thm:logic-regular-functions` and Theorem `thm:rational-primes`, and their aperiodic
counterparts are not available; producing them is a development of the same order of magnitude as
the mso case.  What *is* available towards them is the relabelling half of the picture, Theorem
`thm:fo-rational-functions` above, which identifies the first-order rational functions appearing
among the primes.

`#print axioms` on `Transducers.isFOTransduction_of_compClosure`,
`Transducers.isFOTransduction_comp`,
`Transducers.isFOTransduction_of_isFORelabelling`,
`Transducers.isFOTransduction_mapReverse` and
`Transducers.isFOTransduction_mapDuplicate` reports only `propext`,
`Classical.choice`, `Quot.sound`.

### Part D: Polyregular functions

| Book | Lean | Status | File |
| --- | --- | --- | --- |
| Definition `def:polyregular-functions` (polyregular functions) | `Transducers.IsPolyregular`, `Transducers.markedSquare` | — | `PartD/PolyDef.lean` |
| Theorem `thm:polyregular-functions-are-continuous` (continuity) | `Transducers.polyregular_continuous` | proved (continuity of marked squaring, `MarkedSquare.lean`) | `PartD/Statements.lean` |
| For-transducers (Section *For-transducers*) | `Transducers.ForProg`, `Transducers.IsForTransducer` | — | `PartD/ForDef.lean` |
| Theorem `thm:for-transducers-are-polyregular` (polyregular = for-transducers) | `Transducers.polyregular_iff_forTransducer` | proved (`ForPolyreg.lean` and `PolyFor.lean`) | `PartD/Statements.lean` |
| Definition `def:prenex-normal-form-for-transducers` (prenex form) | `Transducers.ForProg.PrenexForm` | — | `PartD/ForDef.lean` |
| Lemma `lemma:prenex-normal-form` (prenex normal form) | `Transducers.forTransducer_prenex` | proved (`ForPrenexTop.lean`) | `PartD/Statements.lean` |
| Lemma `lem:for-closed-under-composition` (composition) | `Transducers.forTransducer_comp` | proved (`ForCompTop.lean`) | `PartD/Statements.lean` |
| Pebble transducers (Section *Pebble transducers*) | `Transducers.Pebble`, `Transducers.IsPebbleTransducer` | — | `PartD/PebbleDef.lean` |
| Theorem `thm:pebble-are-continuous` (continuity) | `Transducers.pebble_continuous` | proved (`PebbleReg.lean`, on top of `PebbleAut.lean`, `PebbleProd.lean`, `PebbleSub.lean`, `PebbleAnn.lean`, `PebbleBisim.lean`, `PebbleOne.lean`, `PebbleLev1.lean`) | `PartD/Statements.lean` |
| Lemma `lem:reachability-pebble-automaton`, Claim `claim:reachability-basic-run`, Lemma `lem:children-of-configuration-in-pebble-run`, Claims `claim:from-configuration-to-child-configuration-graph`, `claim:from-child-configuration-graph-to-children` | not formalised (configuration encodings used inside proofs) | — | — |
| Theorem `thm:pebble-are-for` (pebble = for-transducers) | `Transducers.pebble_iff_forTransducer` | proved (`PebbleForTop.lean` for `for ⊆ pebble`, `PebblePoly.lean` for `pebble ⊆ polyregular`, then `thm:for-transducers-are-polyregular`) | `PartD/Statements.lean` |

Supporting files for Part D: `MarkedSquare.lean` (marked squaring and the
right-to-left automaton showing that it is continuous), the thirteen
`For*.lean` files listed in the table of files above, which carry the syntax and
the semantics of the for-transducers, the prenex form of Lemma
`lemma:prenex-normal-form`, and the composition of two for-transducers of Lemma
`lem:for-closed-under-composition`, the five `Poly*.lean` files that carry the
right-to-left inclusion of Theorem `thm:for-transducers-are-polyregular`, the
nine `Pebble*.lean` files that carry Theorem `thm:pebble-are-continuous`, and
the files that carry Theorem `thm:pebble-are-for`: `PebbleForDef.lean`,
`PebbleForRun.lean`, `PebbleForNest.lean` and `PebbleForTop.lean` for the easy
direction, and `TwoWayTotal.lean`, `SqPad.lean`, `PebbleTwoWay.lean`,
`PebbleSquareIdx.lean`, `PebbleSquareDef.lean`, `PebbleSquareRun.lean`,
`PebbleSquareSim.lean` and `PebblePoly.lean` for the hard one.

`#print axioms Transducers.pebble_continuous` reports only `propext`,
`Classical.choice`, `Quot.sound`, and so do
`Transducers.continuous_of_isPebbleTransducer`,
`Transducers.pebbleAut_answers_isRegular`,
`Transducers.OnePebble.onePebble_isRegular`,
`Transducers.pebble_iff_forTransducer` and
`Transducers.isPolyregular_of_isPebbleTransducer`.

## Status

This section is the final summary of the index above.  It was written after a
`lake build` of the whole project **from scratch** (Mathlib included), which
succeeded with **no errors**; the only diagnostics are style warnings of the
Lean linter, inventoried in *The warnings of the build* below.

### Counts

The book has **100 theorem-like environments**, listed in the dictionary of
`LABELS.md` and checked against the book's `main.aux`.  Every one of them has a
row in the index above.

| | Introduction | Part A | Part B | Part C | Part D | total |
| --- | --- | --- | --- | --- | --- | --- |
| definitions formalised | 1 | 4 | 7 | 6 | 2 | **20** |
| results proved outright | 0 | 11 | 21 | 28 | 6 | **66** |
| results proved from an explicit hypothesis | 0 | 0 | 5 | 1 | 0 | **6** |
| environments not formalised | 0 | 0 | 1 | 1 | 5 | **8** |

*Proved outright* means: the proof is complete, no file it depends on contains a
`sorry`, and `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`.  Lemma
`lem:check-if-output-string-of-configuration-graph-belongs-to-L` is counted here:
it is proved outright in that sense, but its statement carries the hypothesis
that the transducer computes a total function, as listed under *Hypotheses that
the Lean statement adds* above.  **Parts A, B and D are proved in full**, and so is Part C except
that Theorem `thm:decidable-equivalence-regular` is conditional in the sense
below.  The last column of *environments not formalised* counts labels, not rows:
one row of the index groups several labels (the five configuration-encoding
results of Part D).

### The six results proved from an explicit hypothesis

Each of these takes its hypothesis as an ordinary explicit argument of the
theorem, so it is visible in the statement, and `#print axioms` on the theorem
still reports only the three standard axioms.  No `axiom` is declared anywhere
in the project.

| result | hypothesis | where the hypothesis is defined |
| --- | --- | --- |
| Theorem `thm:undecidable-equivalence-rational-relations` | `¬ ComputablePred Transducers.PCP.Solvable` | `PartB/PCPRed.lean` |
| Theorem `thm:equivalence-weighted-automata` | `Transducers.EffectiveWeightedEvalEq` | `PartB/Effective.lean` |
| Theorem `thm:equivalence-rational-functions` | `Transducers.EffectiveWeightedEvalEq` | `PartB/Effective.lean` |
| Theorem `thm:zeroness-weighted-automata` | `Transducers.EffectiveWeightedEvalEq` | `PartB/Effective.lean` |
| Theorem `thm:decide-if-mealy` | `Transducers.EffectiveWeightedEvalEq` | `PartB/Effective.lean` |
| Theorem `thm:decidable-equivalence-regular` | `Transducers.EffectiveTwoWayEvalEq`, `Transducers.EffectiveTwoWayBound` | `PartC/EffectiveReg.lean` |

`EffectiveWeightedEvalEq` says that the values of two coded weighted automata on
a given input can be compared effectively; `EffectiveTwoWayEvalEq` and
`EffectiveTwoWayBound` say the same for coded two-way transducers, and that an
equivalence bound can be computed from the codes.  They are isolated because
Mathlib's `Primrec`/`Computable` API supplies no arithmetic on `ℤ` or `ℚ`, not
because anything mathematical is missing: the non-effective content behind them,
including Schützenberger's bound (`PartB/WeightedBound.lean`) and the reduction
of equivalence of regular functions to a finite check
(`Transducers.regularFun_eq_of_short`), is proved unconditionally.  See *The four
conditional results of Part B* and *The conditional result of Part C* above.

### The eight environments that are not formalised

None of them is an unfinished proof; each is either not a mathematical result,
or an internal step about the configuration encoding of a pebble automaton,
which this project deliberately does not introduce, and in each case the result
it serves *is* proved.

| environment | reason |
| --- | --- |
| Definition `def:rational-recognisable-subsets` | the rational and recognisable subsets of a monoid; used once in the book, in the remark explaining the name *Kleene theorem*, and by nothing else |
| Conjecture `conj:regular-via-weighted-automata` | an open conjecture of the book, not a result |
| Lemma `lem:reachability-pebble-automaton` | the reachability analysis of a pebble automaton; the Lean proof of Theorem `thm:pebble-are-for` replaces it by an induction on the number of pebbles |
| Claim `claim:reachability-basic-run` | not formalised: internal step of the same analysis |
| Lemma `lem:children-of-configuration-in-pebble-run` | not formalised: internal step of the same analysis |
| Claim `claim:from-configuration-to-child-configuration-graph` | not formalised: internal step of the same analysis |
| Claim `claim:from-child-configuration-graph-to-children` | not formalised: internal step of the same analysis |
| Theorem `nolabel:thm-fo-transduction-into-primes` | withdrawn from this formalisation at the author's request; the book states it without proof.  Its statement is kept, commented out, in `PartC/MSOOpen.lean`, and its easy half is proved as `Transducers.isFOTransduction_of_compClosure` |

One part of a formalised statement is also left out: the final sentence of
Theorem `thm:aperiodic-mealy`, "moreover, this property can be decided given a
Mealy machine that computes `f`".  See *Divergences from the book* above.

### `sorry` and axioms

There is **no `sorry` anywhere in the project**.  The string `sorry` occurs in
four places, all of them inside block comments that preserve a statement the
project does not make: the earlier edition of Theorem
`thm:sequential-function-independent` and the unconditional form of Theorem
`thm:decide-if-mealy` (`PartB/WeightedStatements.lean`), the withdrawn open half
of Theorem `nolabel:thm-fo-transduction-into-primes` (`PartC/MSOOpen.lean`), and
the unconditional form of Theorem `thm:decidable-equivalence-regular` together
with the printed form of Claim `claim:conditional` (`PartC/Statements.lean`).

There is **no `axiom` declaration**, no `@[implemented_by]` and no
`native_decide` in the project.  The only assumptions are the six explicit
hypotheses listed above, which are theorem arguments.

This is checked by the build itself.  `RequestProject/Labels.lean` declares 184
aliases — one per formalised result, with `#2`, `#3`, … when a result is rendered
by several declarations — covering the 90 environments of the book that are
formalised, and each alias is followed by `assert_no_sorry`, which fails at
compile time if the declaration depends on `sorryAx` **or on any axiom other than
`propext`, `Classical.choice`, `Quot.sound`**.  So the whole *proved outright*
column above is re-verified on every build.  No alias carries
`assert_uses_sorry`: nothing that is formalised is left unproved.

### The warnings of the build

`lake build` from scratch reports no error.  The remaining diagnostics are Lean
linter warnings inside proofs; none of them touches a statement.  After this
audit removed the mechanical ones (62 unused `simp` arguments, three deprecated
lemma names, three unnecessary `simpa`s, five `<;>` that should be `;`, two
no-op tactics and two `intro` chains), the warnings that remain are of two
kinds, both of which would change the *signature* of an auxiliary lemma if they
were acted on, and are therefore left alone:

* 28 × `automatically included section variable(s) unused in theorem …` — a
  section variable that a helper lemma does not use.  Silencing it with `omit …
  in` removes the variable from the lemma's statement.
* 17 × `unused variable …` — a hypothesis of a helper lemma that its proof does
  not use.  Removing it changes the statement of the helper.

Both kinds occur only in the internal files of Parts B, C and D and in
`Exercises/Compression.lean`; no numbered result of the book is stated with an
unused hypothesis.

### The exercises

The exercises are not numbered results of the main text and are indexed
separately, in `EXERCISES.md`.  The book has 83 exercises, 82 of them with a
written solution.  **59 are formalised and proved**, in
`RequestProject/Exercises/`; each has an alias in `RequestProject/Labels.lean`
with `assert_no_sorry`, so none of them depends on `sorryAx` or on a non-standard
axiom, and there is no `sorry` in `RequestProject/Exercises/`.  The remaining 24
are listed in `EXERCISES.md` with a reason for each; 23 of those have a written
solution in the book and 1 does not.  Three of the 59 carry an explicit
hypothesis rather than being proved outright, in the same style as the numbered
results: `exer:function-that-is-not-rational`,
`exer:rational-relations-intersection-undecidable` and item (a) of
`exer:decide-rational-colision`.

### How this index is kept honest

Four scripts in `tools/` check the bookkeeping, and all four report no problem.

* `tools/gen_labels.py --check` — `Labels.lean` against `LABELS.md`,
  `THEOREMS.md` and `EXERCISES.md`: every formalised row has an alias, every
  alias points at a declaration its row names, every environment of the book is
  either aliased or listed in the accounting comment at the end of the file, and
  every label the project mentions is a label of the book.
* `tools/tex_numbering.py --check` — the number column of `LABELS.md` against
  the book's `main.aux`.
* `tools/decl_files.py --check` — the `File` column of the index above against
  the files that actually declare the named declarations.
* `tools/relabel.py` — finds any place where a result of the book is still
  referred to by number instead of by label.

`FORMALISATION.md` is a short prose companion to this file, addressed to a
reader of the book rather than to a maintainer of the formalisation.
