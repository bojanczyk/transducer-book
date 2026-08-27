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
an alias whose Lean name is its label, and an assertion that records whether the
result is proved outright or still depends on `sorry`.  So the names and the
statuses in the tables below cannot go stale without breaking the build.

All the results of **Part A** are proved, including the Krohn-Rhodes Theorem
`thm:krohn-rhodes`, Lemma `lem:Mealy-map-lifting` and both implications of Theorem
`thm:aperiodic-mealy`.  All the results of **Part B** are proved as well; five of them
(`thm:undecidable-equivalence-rational-relations`, `thm:equivalence-weighted-automata`,
`thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata` and `thm:decide-if-mealy`)
are proved from explicit hypotheses, which are the undecidability of
the Post correspondence problem and one effectivity hypothesis about arithmetic on `ℚ` that
Mathlib's computability API cannot yet supply.  Parts C and D are partly proved; the status of every
result is recorded in the tables below.

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
a single result, in the index below.  The list was last checked against the
sources in full; a divergence that has since disappeared from the book is noted
as such rather than deleted, because the note explaining it is still in the Lean
files.

*Statements that were corrected because the printed version is false.*

* Definition `def:aperiodic-mealy` — `Transducers.Aperiodic` asks that the last letter of
  `f (u vⁿ w)` be eventually constant **as an element of `Option B`**.  Requiring an
  actual output letter makes the notion unsatisfiable, since for `u = v = w = ε`
  the output of a letter-to-letter function is empty.  The Lean definition also
  drops the book's side conditions that `f` be length preserving and that `uvw`
  be nonempty; neither is used.
* Lemma `lemma:derivatives` — the derivative is `f⁽ʷ⁾(v) = drop |w| (f (w v))`, i.e. the
  `|w|` output letters produced while reading `w` are removed.  With the literal
  reading `f⁽ʷ⁾(v) = f (w v)` even the identity has infinitely many derivatives
  and the lemma is false.
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
* Lemma `lem:output-of-snake-graph-is-regular` — stated for the run of a two-way transducer, as
  the regularity of the width-`k` output function `TwoWay.widthOut M k`, rather than
  for an alphabet of snake letters; and for every `k : ℕ`, not only for
  `k ∈ {1, …, |Q|}`.
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
* Conjecture `conj:regular-via-weighted-automata`, Lemmas `lem:compute-configuration-graph` and
  `lem:check-if-output-string-of-configuration-graph-belongs-to-L`, and the five results of
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

*Divergences that the book has since removed.*

* Corollary `cor:2dfa-computes-all-regular-functions` — an earlier edition printed the inclusion
  the wrong way round.  The sources now read "Every regular function is computed
  by a two-way transducer", which is what is formalised.  See the section below.
* Theorem `thm:sequential-function-independent` — an earlier edition omitted the condition
  "outputs ε when the input is ε", which makes the theorem false.  The sources now
  list it as item (c), so the Lean statement is faithful; the earlier version is
  kept, commented out, in `PartB/WeightedStatements.lean`.
* Theorem `nolabel:thm-fo-transduction-into-primes` — this is no longer a numbered environment of
  the book at all: `logic.tex` ends with an unnumbered paragraph that states the
  result and leaves its proof "for a future edition".  It was withdrawn from this
  formalisation at the author's request; the placeholder tag stays because the
  paragraph carries no `\label`.

## Index

### Introduction

| Book | Lean |
| --- | --- |
| Definition `def:continuity` (continuity) | `Transducers.Continuous` |

### Part A: Mealy machines

| Book | Lean | Status |
| --- | --- | --- |
| Definition `def:mealy-machine` (Mealy machine) | `Transducers.Mealy`, `Transducers.Mealy.eval`, `Transducers.IsMealy` | — |
| Theorem `thm:equivalence-decidable-mealy` (decidable equivalence) | `Transducers.mealy_equiv_iff_bounded` | proved |
| Theorem `thm:composition-mealy` (composition) | `Transducers.mealy_comp` | proved |
| Theorem `thm:continuity-mealy` (continuity) | `Transducers.mealy_continuous` | proved |
| Definition `def:prime-mealy-machines` (prime Mealy machines) | `Transducers.Mealy.Reversible`, `Transducers.Mealy.FlipFlop`, `Transducers.PrimeMealyFam` | — |
| Theorem `thm:krohn-rhodes` (Krohn–Rhodes) | `Transducers.krohn_rhodes` | proved |
| Definition `def:map-lifting` (map lifting) | `Transducers.mapLift` | — |
| Lemma `lem:map-lifting-decomposition-mealy` (map lifting of a decomposition) | `Transducers.mapLift_prime_decomposition` | proved (in `MapLift.lean`) |
| Lemma `lem:Mealy-map-lifting` (state transformation transducer) | `Transducers.stateTransTransducer_prime_decomposition` | proved (in `StateTrans.lean`): induction basis `stateTransTransducer_prime_of_reversible`, induction step by the tripartite decomposition into `a`-blocks (`krStages_eq`, `krStages_compClosure`) |
| Lemma `lem:reversible-composition` (reversible machines compose) | `Transducers.reversible_comp` | proved |
| Definition `def:aperiodic-mealy` (aperiodic) | `Transducers.Aperiodic` | — |
| Theorem `thm:aperiodic-mealy` (aperiodic = flip-flops) | `Transducers.aperiodic_iff_flipflop_composition` | proved ("⇐" by `flipflop_composition_aperiodic`, "⇒" by `krohn_rhodes_flipFlop`, which runs the construction of `StateTrans.lean` inside the class of flip-flops, using that only realisable state transformations occur, see `StateTransAperiodic.lean`).  The theorem's last sentence, "moreover, this property can be decided", is *not* part of the Lean statement — see *Divergences from the book* above |
| Claim `claim:aperiodic-pumping` (pumping form of aperiodicity) | `Transducers.aperiodic_iff_pumping` | proved |
| Lemma `lemma:derivatives` (Myhill–Nerode) | `Transducers.myhill_nerode_mealy` | proved |
| Lemma `lem:aperiodicity-minimal-machine` (condition (*)) | `Transducers.aperiodic_iff_transStabilises` | proved |

Two definitions of Part A had to be corrected in order to make the corresponding
statements true; both corrections are documented in the docstrings.

* `Aperiodic` (Definition `def:aperiodic-mealy`) asks that the sequence of last letters of
  `f (u vⁿ w)` is eventually constant *as an element of `Option B`*.  Requiring
  an actual output letter would make the notion unsatisfiable, since for
  `u = v = w = ε` the output of a letter-to-letter function is empty.
* `deriv` (the derivative used in Lemma `lemma:derivatives`) removes the `|w|` output letters
  produced while reading `w`: `f⁽ʷ⁾(v) = drop |w| (f (w v))`.  With the literal
  reading `f⁽ʷ⁾(v) = f (w v)` even the identity function would have infinitely
  many derivatives, and Lemma `lemma:derivatives` would be false.

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

| Book | Lean | Status |
| --- | --- | --- |
| Definition `def:nfa-with-output` (nfa with output) | `Transducers.NFAO` (via `Transducers.LabAut`) | — |
| Definition `def:rational-relation` (rational relation) | `Transducers.IsRationalRel` | — |
| Definition `def:rational-recognisable-subsets` (the rational and the recognisable subsets of a monoid) | — | not formalised.  The book uses it once, in the remark that explains the name *Kleene Theorem*; nothing else in the book, and nothing in this project, depends on it.  The recognisable subsets of `A* × B*` are formalised, for that monoid only, as `Transducers.Exercises.IsRecognisableRel` (Exercise `ex:recognisable-relations`, see `EXERCISES.md`) |
| Theorem `thm:composition-rational-relations` (composition) | `Transducers.rationalRel_comp` | proved (product automaton in `RatComp.lean`, on the atomic normal form of `Atomize.lean`) |
| Theorem `thm:continuity-rational-relations` (continuity) | `Transducers.rationalRel_continuous` | proved (ε-automaton running a dfa on the output, `RatCont.lean`) |
| Theorem `thm:undecidable-equivalence-rational-relations` (undecidable equivalence) | `Transducers.rationalRel_equivalence_undecidable` | proved from an explicit hypothesis that the Post correspondence problem is undecidable (reduction in `PCPRed.lean`) |
| Claim `claim:homomorphism-complement-rational` (complement of a homomorphism) | `Transducers.hom_complement_rational` | proved (explicit four-state automaton, `HomComplement.lean`) |
| Definition `def:rational-function` (rational function) | `Transducers.IsRationalFun` | — |
| Definition `def:bimachine` (bimachine) | `Transducers.Bimachine`, `Transducers.IsBimachine` | — |
| Theorem `thm:bimachines` (rational = unambiguous = bimachine) | `Transducers.rational_iff_unambiguous_iff_bimachine` | proved (unambiguity by the least accepting run, `Unambig.lean` and `Uniform.lean`; bimachine → rational in `Bimachine.lean`, rational → bimachine in `RatBimach.lean`) |
| Lemma `lemma:eliminate-epsilon-transitions` (elimination of ε-transitions) | `Transducers.epsilon_elimination` | proved (`EpsElim.lean`, using the regularity of the outputs on a fixed input, `OutLang.lean`) |
| Lemma `lem:uniformisation` (uniformisation) | `Transducers.uniformisation` | proved (`Uniform.lean`, from the ε-free normal form of Lemma `lemma:eliminate-epsilon-transitions` and the unambiguisation of `Unambig.lean`) |
| Theorem `thm:rational-primes` (decomposition into primes) | `Transducers.rational_iff_prime_composition` | proved (`PrimeRat.lean` and `BimachPrime.lean`, from Theorem `thm:bimachines` and the Krohn–Rhodes Theorem) |
| Theorem `thm:rational-is-mealy-characterisation` (Mealy machines inside rational functions) | `Transducers.rational_isMealy_iff` | proved (from Theorem `thm:mealy-machine-independent` and Theorem `thm:continuity-rational-relations`) |
| Definition `def:semiring` (semiring) | Mathlib's `Semiring` | — |
| Definition `def:weighted-automaton` (weighted automaton) | `Transducers.LabAut.wEval`, `Transducers.IsWeighted` | — |
| Theorem `thm:equivalence-weighted-automata` (equivalence over ℚ) | `Transducers.weighted_equivalence_decidable` | proved from the effectivity hypothesis `EffectiveWeightedEvalEq` (`WeightedDec.lean`) |
| Theorem `thm:equivalence-rational-functions` (equivalence of rational functions) | `Transducers.rationalFun_equivalence_decidable` | proved from `EffectiveWeightedEvalEq` (reduction to `thm:equivalence-weighted-automata` in `RatEqDec.lean`) |
| Lemma `lem:closure-weighted-automata-precomposition` (pre-composition) | `Transducers.weighted_precomp_rational` | proved (`WeightedNF.lean`, `WeightedLinRep.lean` and `WeightedPrecomp.lean`) |
| Theorem `thm:characterisation-rational-functions-weighted-automata` (characterisation of rationality) | `Transducers.rational_iff_weighted_precomp` | proved ("⇒" is Lemma `lem:closure-weighted-automata-precomposition`, "⇐" in `WeightedRegular.lean`) |
| Theorem `thm:zeroness-weighted-automata` (zeroness) | `Transducers.weighted_zeroness_decidable` | proved from `EffectiveWeightedEvalEq` (special case of `thm:equivalence-weighted-automata`, `WeightedDec.lean`) |
| Theorem `thm:mealy-machine-independent` (characterisation of Mealy machines) | `Transducers.isMealy_iff` | proved (`MealyChar.lean`) |
| Theorem `thm:decide-if-mealy` (deciding the Mealy fragment) | `Transducers.rationalFun_isMealy_decidable` | proved from `EffectiveWeightedEvalEq` (`PrefixCodes.lean`, `CodeRat.lean`, `MealyDec.lean`); the statement is relativised to the strings over the alphabet of the code |
| Lemma `lem:decide-if-length-preserving` (deciding length preservation) | `Transducers.rationalFun_lengthPreserving_decidable` | proved (bounded enumeration of transition sequences, `PathComb.lean` and `LenDec.lean`) |
| Claim `claim:typing-length-preserving` (typings) | `Transducers.lengthPreserving_iff_typing` | proved (`Typing.lean`) |
| Lemma `lem:characterisation-length-preserving` (length-preserving normal form) | `Transducers.lengthPreserving_rational_normal_form` | proved (`LenNormalForm.lean`) |
| Theorem `thm:sequential-function-independent` (sequential functions) | `Transducers.isSequential_iff` | proved (`SeqChar.lean`).  The Lean statement is faithful: the book's condition (c) — *outputs ε when the input is ε* — is the Lean conjunct `f [] = []`.  An earlier edition of the book omitted (c), which made the theorem false; the docstring in `PartB/WeightedStatements.lean` still keeps that version, commented out, as a record |
| Definition `def:left-distance` (left distance) | `Transducers.leftDist` | — |
| Theorem `thm:subsequential-functions` (subsequential functions) | `Transducers.isSubsequential_iff` | proved (`SubseqDef.lean`, `SubseqAlpha.lean`, `SubseqState.lean`, `SubseqBound.lean`, `SubseqChar.lean`) |
| Claim `claim:bounded-extensions` (short extensions suffice) | `Transducers.Subseq.delay_bound`, `Transducers.Subseq.exists_short_extension` | proved (`SubseqAlpha.lean`); a **reorganised** step, not a literal rendering — see the note below |
| Claim `claim:computing-branching-part` (the branching part) | `Transducers.Subseq.key_drop` | proved (`SubseqState.lean`); phrased through Myhill–Nerode states rather than through regular languages — see the note below |
| Claim `claim:offsets-are-regular` (the offsets) | `Transducers.Subseq.incr_congr` | proved (`SubseqState.lean`); phrased through Myhill–Nerode states rather than through regular languages — see the note below |
| Claim `claim:eliminating-negative-letters` (negative letters) | `Transducers.Subseq.exists_deletion_bound` | proved (`SubseqBound.lean`); the free group is not used — see the note below |
| Theorem `thm:machine-independent-rational-functions` (rational functions) | `Transducers.isRationalFun_iff` | proved (`RatIndex.lean`, `SubseqRat.lean`, `RatAnnot.lean`) |

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

| Book | Lean | Status |
| --- | --- | --- |
| Definition `def:regular-functions` (regular functions) | `Transducers.IsRegularFun`, `Transducers.RegularFam` | — |
| Theorem `thm:regular-functions-are-continuous-and-closed-under-composition` (continuity, composition) | `Transducers.regular_continuous`, `Transducers.regular_comp` | proved (continuity by induction on the decomposition into primes, `ContAux.lean`) |
| Lemma `lem:reversal-duplication-continuous` (reversal, duplication) | `Transducers.reverse_duplicate_continuous` | proved (`ContAux.lean`) |
| Lemma `lem:map-lifting-continuous` (map lifting) | `Transducers.mapLift_continuous` | proved (Myhill–Nerode, `ContAux.lean`) |
| Theorem `thm:decidable-equivalence-regular` (decidable equivalence) | `Transducers.regular_equivalence_decidable`; the book's proof: `Transducers.isWeighted_comp_regular`, `Transducers.isWeighted_comp_mapReverse`, `Transducers.isWeighted_comp_mapDuplicate`, `Transducers.exists_injective_weighted`, `Transducers.regularFun_eq_iff_weighted_eq`, `Transducers.regularFun_eq_iff_weighted_zero`, `Transducers.regularFun_eq_of_short`, `Transducers.exists_twoWayCode_bound` | the mathematical content of the book's proof is **proved** (`WeightedLin.lean`, `WeightedMapLift.lean`, `WeightedRegClosure.lean`): the reduction to zeroness of weighted automata over `ℚ` through the prime decomposition, with the constructions for map reverse (transposition of the matrices of a linear representation, where commutativity of the semiring is used) and map duplicate (Kronecker squares), the injective encoding of output strings by rationals, and the resulting bound reducing equivalence to a finite check. The decidability statement on *codes*, `Transducers.regular_equivalence_decidable`, is **proved from two explicit effectivity hypotheses** (`EffectiveTwoWayEvalEq` and `EffectiveTwoWayBound` of `PartC/EffectiveReg.lean`, `PartC/RegEqDec.lean`), exactly as Theorems `thm:equivalence-weighted-automata` and `thm:zeroness-weighted-automata` are: what those hypotheses isolate is the missing `Primrec`/`Computable` arithmetic on `ℤ` and `ℚ`. The *existence* of the equivalence bound, the mathematical content of the second hypothesis, is proved (`Transducers.exists_twoWayCode_bound`, `PartC/RegCodeBound.lean`) |
| Conjecture `conj:regular-via-weighted-automata` (regular functions via weighted automata) | — | not formalised: it is an open conjecture of the book, not a result |
| Definition `def:two-way-transducer` (two-way transducer) | `Transducers.TwoWay`, `Transducers.IsTwoWay` | — |
| Theorem `thm:continuity-2dfas` (continuity) | `Transducers.twoWay_continuous` | proved (`TwoWayCont.lean`, from Shepherdson's Theorem in `TwoDFA.lean`) |
| Lemmas `lem:compute-configuration-graph`, `lem:check-if-output-string-of-configuration-graph-belongs-to-L` | not formalised (the string encoding of the configuration graph, used only inside the book's proof of Theorem `thm:composition-of-two-way-transducers`) | — |
| Lemma `lem:output-of-snake-graph-is-regular` (the output of a snake graph is regular) | `Transducers.boundedWidth_isRegular` | **proved** (`SnakeReg.lean`, on top of `SnakeBase.lean`, `SnakeWalk.lean`, `SnakeRec.lean`, `SnakeLoop.lean` and the checking automaton of `SnakeStage1.lean`/`SnakeChk*.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`).  Stated for the width-`k` output function `TwoWay.widthOut` of a two-way transducer rather than for an alphabet of snake letters, and for every `k : ℕ` rather than for `k ∈ {1, …, |Q|}` |
| Theorem `thm:composition-of-two-way-transducers` (composition) | `Transducers.twoWay_comp` | proved (`TwoWayRun.lean`, `TwoWayVisit.lean`, `TwoWayAnnot.lean`, `TwoWayAnnotBim.lean`, `TwoWayCompAux.lean`, `TwoWayCompPred.lean`, `TwoWayComp.lean`, `TwoWayCompFinal.lean`) |
| Lemma `lem:2dfa-precomposition-with-mealy` (pre-composition with Mealy machines) | `Transducers.twoWay_precomp_mealy` | proved |
| Corollary `cor:2dfa-closure-under-composition` (pre-composition with rational functions) | `Transducers.twoWay_precomp_rational` | proved (`TwoWayHom.lean`, `TwoWayBlock.lean`, `TwoWayErase.lean` and `TwoWayRat.lean`, from Theorem `thm:rational-primes` and Lemma `lem:2dfa-precomposition-with-mealy`) |
| Corollary `cor:2dfa-computes-all-regular-functions` (regular ⊆ two-way) | `Transducers.regularFun_isTwoWay`, `Transducers.isTwoWay_of_isRegularFun` | proved (`TwoWaySweep.lean`, `TwoWayRegular.lean`, from Corollary `cor:2dfa-closure-under-composition` and Theorem `thm:composition-of-two-way-transducers`) |
| Theorem `thm:2dfa-decomposition-into-primes` (two-way = regular) | `Transducers.twoWay_iff_regular`, `Transducers.twoWay_isRegular` | **both implications are proved**: the right-to-left one is Corollary `cor:2dfa-computes-all-regular-functions` above, and the left-to-right one, `Transducers.twoWay_isRegular` (two-way ⊆ regular, the inclusion printed in Corollary `cor:2dfa-computes-all-regular-functions`), is reduced to the snake lemma `Transducers.boundedWidth_isRegular` of `SnakeReg.lean`, whose base cases `k ≤ 1` are in `SnakeBase.lean`, whose combinatorial content is in `SnakeWalk.lean`, `SnakeRec.lean` and `SnakeLoop.lean`, and whose induction step `Transducers.boundedWidth_isRegular_step` is proved through the checking automaton of stage 1 (`SnakeStage1.lean`, `SnakeChk*.lean`); the whole theorem depends only on `propext`, `Classical.choice`, `Quot.sound` — see *How Theorem `thm:2dfa-decomposition-into-primes` is proved* below |
| Lemma `lem:regular-closure-properties` (closure properties) | `Transducers.regular_closure_properties` | **proved** (`MapLiftAux.lean`, `MapLiftRat.lean`, `MapLiftPrime.lean`, `RegMapLift.lean`, `RatSeq.lean`, `RegClosure.lean`) |
| Claim `claim:conditional` (disjoint sums) | `Transducers.sum_of_regular` | **proved** (`SumShape.lean`, `SumPrime.lean`, `SumReg.lean`, `RegSum.lean`), in the corrected form — the claim as printed is false on the empty input, see *An error in Claim `claim:conditional`* below |
| Definition `def:sst` (sst) | `Transducers.SST`, `Transducers.IsSST` | — |
| Theorem `theorem:sst-two-way-equivalence` (sst = regular) | `Transducers.sst_iff_regular` | both implications are **proved** (`SSTComp.lean`, `SSTMealyRev.lean`, `SSTMealyFF.lean`, `SSTMealy.lean`, `SSTMapRev.lean`, `SSTMapDup.lean`, `SSTRegular.lean` for `regular ⊆ sst`; `SSTNorm.lean`, `SSTWalk.lean`, `SSTTwoWay.lean` for `sst ⊆ two-way`), and since Theorem `thm:2dfa-decomposition-into-primes` is now proved the statement depends only on `propext`, `Classical.choice`, `Quot.sound` — see *The proof of Theorem `theorem:sst-two-way-equivalence`* below |
| Theorem `thm:mso-logic-languages` (mso = regular languages) | `Transducers.regular_iff_msoDefinable` | **proved** (`MSO.lean`, from `MSOSyntax.lean`, `RegAut.lean`, `MSOAnnot.lean`, `MSOBuchi.lean`) |
| Lemma `lem:mso-free-variables` (formulas with free variables) | `Transducers.mso_annotated_regular` | **proved** (`RegAut.lean`, `MSOSyntax.lean`, `MSOAnnot.lean`) |
| Definition `def:mso-relabeling` (mso relabelling) | `Transducers.MSORelabelling`, `Transducers.IsMSORelabelling` | — |
| Theorem `thm:logic-rational-functions` (rational = mso relabelling) | `Transducers.rational_iff_msoRelabelling` | **proved** (`MSO.lean`, from `MSORatRelab.lean`, `MarkStr.lean`, `MarkLogic.lean`, `MarkBimach.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Claim `claim:transition-formula` (the transition formula) | `Transducers.RatRelab.exists_form` | proved (`MSORatRelab.lean`), as the internal step of Theorem `thm:logic-rational-functions`; stated for the index of a bimachine rather than for an unambiguous transducer |
| Claim `claim:mso-annotation-regular` (annotated relabellings) | `Transducers.msoRelabelling_annotation_regular` | **proved** (`MSORelab.lean`, from Lemma `lem:mso-free-variables`) |
| Definition `def:mso-transduction` (mso transduction) | `Transducers.MSOTransduction`, `Transducers.IsMSOTransduction` | — |
| Theorem `thm:logic-regular-functions` (mso transductions = regular) | `Transducers.msoTransduction_iff_regular` | both implications are **proved** (`MSO.lean`, from `MSOReg.lean`, `MSOWalkData.lean`, `WalkAut.lean`, `MSOWalkForms.lean`, `MSONorm.lean`, `SortedEnum.lean` for `mso ⊆ regular`; `TwoWayMSO.lean`, `RunProbe.lean`, `RunMark.lean`, `RunElts.lean`, `MarkLogic2.lean` for `regular ⊆ mso`), and since Theorem `thm:2dfa-decomposition-into-primes` is now proved the statement depends only on `propext`, `Classical.choice`, `Quot.sound` — see *The proof of Theorem `thm:logic-regular-functions`* below |
| Lemma `lem:logic-reduction-to-type-n` (reduction to a normalised type) | `Transducers.MSOTransduction.exists_norm` | proved (`MSONorm.lean`), as the normalisation of the type τ inside the proof of Theorem `thm:logic-regular-functions` |
| Lemma `lem:logic-precomputation` (formulas via rational functions) | `Transducers.mso_formulas_via_rational` | **proved** (`MSO.lean`, from `MSOPrecomp.lean`, `MarkStr.lean`, `MarkBimach.lean`, `MarkDelay.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Theorem `thm:logic-aperiodic` (first-order = aperiodic) | `Transducers.foDefinable_iff_aperiodic_dfa` | **proved** (`MSO.lean`, from `FOTypeDFA.lean` and `FOMealy.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Definition `def:k-types` (k-types) | `Transducers.tp` | — |
| Lemma `lem:k-types-fo-equivalence` (types and formulas) | `Transducers.tp_eq_iff_fo_equiv` | **proved** (`MSO.lean`, from `FOComp.lean` and `FOHintikka.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Claim `claim:fo-composition-quantifier-rank` (compositionality at a fixed quantifier rank) | `Transducers.sat_iff_of_kEquiv` | proved (`FOComp.lean`), as the internal step of the proof of Lemma `lem:k-types-fo-equivalence` |
| Lemma `lem:k-types-properties` (properties of types) | `Transducers.tp_properties` | proved (`KTypes.lean`) |
| Theorem `thm:fo-rational-functions` (first-order relabellings) | `Transducers.foRelabelling_iff_aperiodicBimachine` | **proved** (`MSO.lean`, from `FORelabBimach.lean` for `first-order relabelling ⊆ aperiodic bimachine` and `FOBimachRelab.lean` for the converse, on top of `FORev.lean` and `FOPos.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) |
| Theorem `nolabel:thm-fo-transduction-into-primes` (first-order transductions) | **removed from the formalised theorems at the user's request** (its statement is kept, commented out, in `MSOOpen.lean`) | not formalised as a theorem any more. What remains is the inclusion `compositions of primes ⊆ first-order transductions`, **proved** as `Transducers.isFOTransduction_of_compClosure` (`FOTransPrimeComp.lean`, on top of the closure under composition of `FOTransComp.lean` and the three primes of `FORelabTrans.lean`, `FOTransRev.lean` and `FOTransDup.lean`; axioms: `propext`, `Classical.choice`, `Quot.sound`) — see *Theorem `nolabel:thm-fo-transduction-into-primes`: what was removed and what remains* below |

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
  accepts as soon as the run reaches the marked cut.  This replaces the analysis
  of the reachable configuration graph of Lemma `lem:compute-configuration-graph`.
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

| Book | Lean | Status |
| --- | --- | --- |
| Definition `def:polyregular-functions` (polyregular functions) | `Transducers.IsPolyregular`, `Transducers.markedSquare` | — |
| Theorem `thm:polyregular-functions-are-continuous` (continuity) | `Transducers.polyregular_continuous` | proved (continuity of marked squaring, `MarkedSquare.lean`) |
| For-transducers (Section *For-transducers*) | `Transducers.ForProg`, `Transducers.IsForTransducer` | — |
| Theorem `thm:for-transducers-are-polyregular` (polyregular = for-transducers) | `Transducers.polyregular_iff_forTransducer` | proved (`ForPolyreg.lean` and `PolyFor.lean`) |
| Definition `def:prenex-normal-form-for-transducers` (prenex form) | `Transducers.ForProg.PrenexForm` | — |
| Lemma `lemma:prenex-normal-form` (prenex normal form) | `Transducers.forTransducer_prenex` | proved (`ForPrenexTop.lean`) |
| Lemma `lem:for-closed-under-composition` (composition) | `Transducers.forTransducer_comp` | proved (`ForCompTop.lean`) |
| Pebble transducers (Section *Pebble transducers*) | `Transducers.Pebble`, `Transducers.IsPebbleTransducer` | — |
| Theorem `thm:pebble-are-continuous` (continuity) | `Transducers.pebble_continuous` | proved (`PebbleReg.lean`, on top of `PebbleAut.lean`, `PebbleProd.lean`, `PebbleSub.lean`, `PebbleAnn.lean`, `PebbleBisim.lean`, `PebbleOne.lean`, `PebbleLev1.lean`) |
| Lemma `lem:reachability-pebble-automaton`, Claim `claim:reachability-basic-run`, Lemma `lem:children-of-configuration-in-pebble-run`, Claims `claim:from-configuration-to-child-configuration-graph`, `claim:from-child-configuration-graph-to-children` | not formalised (configuration encodings used inside proofs) | — |
| Theorem `thm:pebble-are-for` (pebble = for-transducers) | `Transducers.pebble_iff_forTransducer` | proved (`PebbleForTop.lean` for `for ⊆ pebble`, `PebblePoly.lean` for `pebble ⊆ polyregular`, then `thm:for-transducers-are-polyregular`) |

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

All statements compile.  Part A is proved in full.  **Part B is now proved in full**: eighteen of
its numbered results are proved outright (`thm:composition-rational-relations`,
`thm:continuity-rational-relations`, `claim:homomorphism-complement-rational`, `thm:bimachines`,
`lemma:eliminate-epsilon-transitions`, `lem:uniformisation`, `thm:rational-primes`,
`thm:rational-is-mealy-characterisation`, `lem:closure-weighted-automata-precomposition`,
`thm:characterisation-rational-functions-weighted-automata`, `thm:mealy-machine-independent`,
`lem:decide-if-length-preserving`, `claim:typing-length-preserving`,
`lem:characterisation-length-preserving`, `thm:sequential-function-independent`,
`thm:subsequential-functions`, `thm:machine-independent-rational-functions`),
`thm:undecidable-equivalence-rational-relations` is proved from an explicit
hypothesis stating that the Post correspondence problem is undecidable, and the four remaining
decidability statements (`thm:equivalence-weighted-automata`,
`thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata`, `thm:decide-if-mealy`) are
proved from the single effectivity
hypothesis `EffectiveWeightedEvalEq` of `PartB/Effective.lean` — see the subsection *The four
conditional results of Part B* above for what that hypothesis says, why it is true, and why it
cannot currently be discharged inside Mathlib (its `Primrec`/`Computable` API provides no arithmetic
on `ℤ` or `ℚ`).  The effective Schützenberger bound, which these four results also need and which
used to be a second hypothesis, is proved in `PartB/WeightedBound.lean`.  No file of Part B contains
a `sorry`, and every numbered result of Part B depends only on `propext`, `Classical.choice`,
`Quot.sound`. In Part C, Theorem
`thm:regular-functions-are-continuous-and-closed-under-composition`, **Theorem
`thm:decidable-equivalence-regular`**, Lemmas `lem:reversal-duplication-continuous` and
`lem:map-lifting-continuous`, Theorem `thm:continuity-2dfas`, **Theorem
`thm:composition-of-two-way-transducers`**, Lemma `lem:2dfa-precomposition-with-mealy`, **Corollary
`cor:2dfa-closure-under-composition`**, **Corollary `cor:2dfa-computes-all-regular-functions`**,
**Theorem `thm:2dfa-decomposition-into-primes`**, **Lemma `lem:regular-closure-properties`**,
**Claim `claim:conditional`**, **Theorem `theorem:sst-two-way-equivalence`**, **Theorem
`thm:logic-regular-functions`**, **Theorem `thm:mso-logic-languages`**, **Lemma
`lem:mso-free-variables`**, **Theorem `thm:logic-rational-functions`**, **Claim
`claim:mso-annotation-regular`**, **Lemma `lem:logic-precomputation`**, **Theorem
`thm:logic-aperiodic`**, **Lemma `lem:k-types-fo-equivalence`**, **Theorem
`thm:fo-rational-functions`** and Lemma `lem:k-types-properties` are proved; Theorem
`thm:decidable-equivalence-regular` is proved from the two effectivity hypotheses of
`PartC/EffectiveReg.lean` — see the subsection *The conditional result of Part C* above —
and everything else it needs, including the existence of its equivalence bound, is proved.  Theorem
`thm:mso-logic-languages` (Büchi-Elgot-Trakhtenbrot), Lemma `lem:mso-free-variables`, Theorem
`thm:logic-rational-functions` (rational functions are exactly the mso relabellings), Claim
`claim:mso-annotation-regular`, Lemma `lem:logic-precomputation` (the precomputation of
a finite family of formulas by a letter-to-letter rational function), Theorem `thm:logic-aperiodic`
(a language is first-order definable if and only if it is recognised by an aperiodic dfa), Lemma
`lem:k-types-fo-equivalence` (two strings have the same `k`-type if and only if they
satisfy the same first-order sentences of quantifier rank at most `k`) and Theorem
`thm:fo-rational-functions` (the first-order relabellings are exactly the functions computed by
aperiodic bimachines) are proved outright: no file they use contains a `sorry`, and each of them
depends only on `propext`, `Classical.choice`, `Quot.sound` (checked again on a clean build of the
whole project, `lake build` with no errors, and with `#print axioms`; Lemma
`lem:k-types-properties` needs only `propext` and `Quot.sound`).  Both directions of Theorem
`thm:logic-rational-functions`, and Lemma `lem:logic-precomputation`, go through bimachines (Theorem
`thm:bimachines`) and through the doubly marked alphabet `Mark2 A = A × 2 × 2`, for which Lemma
`lem:mso-free-variables` gives the regular language `markedSat2 φ` of the marked strings
satisfying a formula; Claim `claim:transition-formula` of the book is the internal step of Theorem
`thm:logic-rational-functions` and is formalised, as `Transducers.RatRelab.exists_form`, for the
index of a bimachine rather than for the transitions of an unambiguous transducer.  So that the
state of the section is visible file by file, the numbered results of Section *Logic* that are still
open have been moved, unchanged, from `PartC/MSO.lean` to `PartC/MSOOpen.lean`, which
`PartC/MSO.lean` imports: `PartC/MSO.lean` now contains exactly the ten proved results of Section
*Logic* (`thm:mso-logic-languages`, `lem:mso-free-variables`, `thm:logic-rational-functions`,
`claim:mso-annotation-regular`, `thm:logic-regular-functions`, `lem:logic-precomputation`,
`thm:logic-aperiodic`, `lem:k-types-fo-equivalence`, `lem:k-types-properties`,
`thm:fo-rational-functions`) and no `sorry`,
while every name of Section *Logic* is still available from `RequestProject.PartC.MSO` as before;
`PartC/MSOOpen.lean` now declares nothing at all.  Of **Theorem
`nolabel:thm-fo-transduction-into-primes`** (the first-order transductions are exactly the
compositions of map reverse, map duplicate and first-order rational functions), which has been
removed from the formalised theorems at the user's request, the inclusion from compositions of
primes to first-order transductions is proved (`Transducers.isFOTransduction_of_compClosure`,
`FOTransPrimeComp.lean`, depending only on `propext`, `Classical.choice`, `Quot.sound`), on top of
the closure of first-order transductions under composition (`FOTransTr.lean`, `FOTransComp.lean`)
and of the three primes (`FORelabTrans.lean`, `FOTransRev.lean`, `FOTransDup.lean`, with the block
combinatorics of `BlockPos.lean`, `BlockForm.lean` and the tools of `ITransBuild.lean`).  The
converse inclusion, which was the only `sorry` of Section *Logic*, has been removed along with the
theorem; the book gives no proof of it either -- see *Theorem
`nolabel:thm-fo-transduction-into-primes`: what was removed and what remains* above. Lemma
`lem:k-types-fo-equivalence` is proved by the Ehrenfeucht-Fraïssé argument of the book:
the compositionality of first-order logic (Claim `claim:fo-composition-quantifier-rank`, `FOComp.lean`)
gives one direction, and Hintikka sentences of quantifier rank `k`, built by induction from the
finitely many `k`-types (`FOHintikka.lean`, using Lemma `lem:k-types-properties`), give the
other.  For Theorem `thm:logic-aperiodic`, the easy direction runs the finite aperiodic automaton of
`k`-types (`FOTypeDFA.lean`), and the hard one follows the book through the aperiodic Krohn-Rhodes
Theorem `thm:aperiodic-mealy`: the Mealy machine of the dfa has the transition function of the dfa,
so aperiodicity is literally the hypothesis of `Transducers.krohn_rhodes_flipFlop`, and the
resulting composition of flip-flops is first-order definable because flip-flops are
(`FOFlipFlop.lean`, `FOMealy.lean`) and first-order definable Mealy machines are closed under
composition, by substitution of formulas (`FOSubstRel.lean`). **Theorem
`thm:logic-regular-functions`** (mso transductions compute exactly the regular functions) is proved
outright in both directions, and no file it uses contains a `sorry`: `regular ⊆ mso` is
`Transducers.isMSOTransduction_of_isTwoWay`, and `mso ⊆ regular` is
`Transducers.MSOReg.isRegularFun_of_isMSOTransduction`, which normalises the type τ (Lemma
`lem:logic-reduction-to-type-n`, `MSONorm.lean`), precomputes the questions of the walk by Lemma
`lem:logic-precomputation` and composes the resulting rational function with the walking two-way
transducer, appealing to Theorem `thm:2dfa-decomposition-into-primes` for the regularity of the
latter; `Transducers.msoTransduction_iff_regular` depends only on `propext`, `Classical.choice`,
`Quot.sound` — see *The proof of Theorem `thm:logic-regular-functions`* above. **Theorem
`theorem:sst-two-way-equivalence`** (sst = regular) is likewise proved outright in both directions,
with every file it uses sorry-free: `regular ⊆ sst` is `Transducers.isSST_of_isRegularFun` and `sst
⊆ regular` is proved from Theorem `thm:2dfa-decomposition-into-primes`, the simulation of an sst by
a two-way transducer (`Transducers.isTwoWay_of_isSST`) being itself proved outright;
`Transducers.sst_iff_regular` depends only on `propext`, `Classical.choice`, `Quot.sound` — see *The
proof of Theorem `theorem:sst-two-way-equivalence`* above. In Part D, Theorem
`thm:polyregular-functions-are-continuous`, **Lemma `lemma:prenex-normal-form`** (every
for-transducer is equivalent to one in prenex form) and **Lemma
`lem:for-closed-under-composition`** (the functions computed by for-transducers are closed under
composition) are proved outright, each depending only on `propext`, `Classical.choice`,
`Quot.sound`; **Theorem `thm:for-transducers-are-polyregular`** (a function is polyregular if and
only if it is computed by a for-transducer) is now proved outright as well, in both directions --
`polyregular ⊆ for` is `Transducers.isForTransducer_of_isPolyregular` (`ForPolyreg.lean`) and
`for ⊆ polyregular` is `Transducers.PolyEnum.isPolyregular_of_isForTransducer` (`PolyFor.lean`),
which factors a program in prenex form as the polyregular enumeration of the tuples of positions
visited by its nest of loops followed by a regular scan of that enumeration -- and
`Transducers.polyregular_iff_forTransducer` depends only on `propext`, `Classical.choice`,
`Quot.sound`.  **Theorem `thm:pebble-are-continuous`** (pebble transducers compute continuous
functions) is now proved outright as well, and depends only on `propext`, `Classical.choice`,
`Quot.sound`: running a deterministic automaton for the target language on the output of the
transducer turns it into a pebble *automaton* (`PebbleProd.lean`), and pebble automata recognise
regular languages (`Transducers.pebbleAut_answers_isRegular`, `PebbleLev1.lean`) by induction on
the number of pebbles -- a `(k+1)`-pebble automaton is simulated by a one-pebble automaton over
the input annotated at every gap with the outcome of the run above a bottom pebble placed there
(`PebbleSub.lean`, `PebbleAnn.lean`), that annotation is continuous because it is computed by a
bimachine, and one-pebble automata are regular through a deterministic two-way automaton and
Shepherdson's Theorem (`PebbleOne.lean`).  **Part D is now proved in full**: its last result,
**Theorem `thm:pebble-are-for`** (pebble transducers and for-transducers compute the same
string-to-string functions), is proved outright and depends only on `propext`,
`Classical.choice`, `Quot.sound`.  From a for-transducer to a pebble transducer, the program is
put in prenex form and its nest of loops is run with one pebble per loop
(`PebbleForTop.lean`).  In the other direction a pebble transducer is shown to compute a
polyregular function (`PebblePoly.lean`), which is a for-transducer by
`thm:for-transducers-are-polyregular`; instead of the reachability analysis of a pebble automaton
that the book uses there (Lemma `lem:reachability-pebble-automaton` and the claims inside its
proof, which are not formalised), the proof is by induction on the number of pebbles.  A
one-pebble transducer is a two-way transducer, hence computes a regular function
(`PebbleTwoWay.lean`, `TwoWayTotal.lean`), and a `(k+2)`-pebble transducer is simulated by a
`(k+1)`-pebble transducer on the marked square of the padded input
(`SqPad.lean`, `PebbleSquareIdx.lean`, `PebbleSquareDef.lean`, `PebbleSquareRun.lean`,
`PebbleSquareSim.lean`): the bottom pebble is remembered by the block of the square in which the
other pebbles sit, and the auxiliary phases of the simulating machine walk its topmost pebble to
the gap that the encoding requires.  Since marked squaring and padding are polyregular, the
composition is polyregular.  Examples of the book are not included; the exercises are not numbered results either,
and are formalised separately, in `RequestProject/Exercises/` and indexed in `EXERCISES.md` — all
twelve exercises of Part A (`mealy.tex` and `krohn-rhodes.tex`) are formalised and proved there.

**Theorem `thm:2dfa-decomposition-into-primes`** (two-way transducers compute exactly the regular
functions) is now **proved outright**, in both directions, and Section *Two-way transducers*
contains no `sorry`. The right-to-left implication is Corollary
`cor:2dfa-computes-all-regular-functions`; the left-to-right one, isolated as
`Transducers.twoWay_isRegular`, is reduced, sorry-free, to the book's snake lemma
`Transducers.boundedWidth_isRegular` (`SnakeReg.lean`), which is proved by induction on the width
`k`: the base cases `k = 0` and `k = 1` (`Transducers.TwoWay.widthOut_zero_isRegular`,
`Transducers.TwoWay.widthOut_one_isRegular`) are in `SnakeBase.lean`, and the induction step
`Transducers.boundedWidth_isRegular_step` is now proved as well. Its combinatorics — record-breaking
columns, loop and progress parts, and the splitting of a run of width `k` into pieces of width `k -
1` together with the corresponding factorisation of its output — is in `SnakeWalk.lean`,
`SnakeRec.lean` and `SnakeLoop.lean`, the confinement of those pieces to two consecutive blocks in
`SnakeConfine.lean`, the book's "reverse the snake" in `SnakeMirror.lean`, the identification of a
piece with the whole run of a window transducer in `SnakeLocal.lean`, `SnakePiece.lean`,
`SnakePieceRev.lean`, `SnakeExc.lean`, `SnakeParts.lean`, `SnakePieceIdent.lean` and
`SnakeFinalConf.lean`, the gluing of the pieces in `Transducers.RegPair.isRegularFun_pairMap`
(`RegPair.lean`, on top of `RatBi.lean`), the block function and the map combinator in
`SnakeBlock.lean` and `SnakeRegTools.lean`, and the existence of a correct marking of every input in
`SnakeAssemble.lean` and `SnakeData.lean`.  The book's stage 1 — that the correct markings can be
*recognised* — is `Transducers.TwoWay.exists_regular_snakeLang` (`SnakeStage1.lean`), proved by the
checking automaton of the `SnakeChk*` files: it verifies a *chain of pieces*
(`Transducers.TwoWay.Chk.ChainData`), whose soundness is
`Transducers.TwoWay.Chk.runOut_of_chainData` and whose completeness on every good input is
`Transducers.TwoWay.Chk.nonempty_chainData_of_good` (`SnakeChkRB.lean`, on top of
`SnakeChkPieceWin.lean`, `SnakeChkCross.lean`, `SnakeChkSlot.lean` and `SnakeChkSlotOK.lean`);
"guess and check" (`PartB/GuessCheck.lean`) and uniformisation (`PartB/UniformFun.lean`) turn that
language into the rational marking function.  `Transducers.twoWay_iff_regular`,
`Transducers.twoWay_isRegular`, `Transducers.boundedWidth_isRegular_step` and
`Transducers.TwoWay.Chk.nonempty_chainData_of_good` depend only on `propext`, `Classical.choice`,
`Quot.sound` (checked with `#print axioms` on a clean build). See *How Theorem
`thm:2dfa-decomposition-into-primes` is proved* above.  Claim `claim:conditional` is proved in a
corrected form: the statement as printed is false on the empty input, see *An error in Claim
`claim:conditional`* above.

Corollary `cor:2dfa-computes-all-regular-functions` is printed in the book as the inclusion
`regular ⊆ two-way`, and that is how it is formalised, as `Transducers.regularFun_isTwoWay`; it is
proved in full.  The converse inclusion is `Transducers.twoWay_isRegular`, the left-to-right
implication of `Transducers.twoWay_iff_regular` (Theorem `thm:2dfa-decomposition-into-primes`),
which is now proved as well.  See *Corollary `cor:2dfa-computes-all-regular-functions`: the typo is
gone from the book* above for the earlier edition in which the two were interchanged.

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
`Transducers.isFOTransduction_of_compClosure`,
`Transducers.boundedWidth_isRegular_step`,
`Transducers.TwoWay.Chk.nonempty_chainData_of_good`,
`Transducers.isRegularFun_of_isTwoWay`,
`Transducers.twoWay_isRegular`,
`Transducers.twoWay_iff_regular`,
`Transducers.sst_iff_regular` and
`Transducers.msoTransduction_iff_regular`
reports only `propext`, `Classical.choice`, `Quot.sound`.

No numbered result of the main text was changed by the formalisation of the
exercises of the introduction (`Exercises/Intro.lean`, indexed in
`EXERCISES.md`): the two of them that coincide with halves of Lemma
`lem:reversal-duplication-continuous` are deduced from that lemma
rather than reproved, and nothing outside `RequestProject/Exercises/`,
`RequestProject/Exercises.lean`, `RequestProject.lean` and
`RequestProject/Labels.lean` (which gained the eleven exercise aliases) was
touched.

### The audit of this index

The whole index was checked mechanically against the sources and against the
Lean files, and this section records what that check found.

* `lake build` from scratch succeeds, with no errors.  The only warnings are
  style warnings of the Lean linter: the `declaration uses sorry` warnings of
  `PartD/Statements.lean` — five of them when this audit was made — are all
  gone, now that Lemma `lemma:prenex-normal-form`, Lemma
  `lem:for-closed-under-composition`, Theorem
  `thm:for-transducers-are-polyregular`, Theorem `thm:pebble-are-continuous`
  and Theorem `thm:pebble-are-for` are proved.  No file of the project
  contains a `sorry`.
* `#print axioms` was run on every alias of `RequestProject/Labels.lean` — 157
  of them, one per label of the book that this formalisation covers — and on
  every Lean name named in a row of this file and of `EXERCISES.md`.  Exactly
  five depended on `sorryAx` when this audit was made:
  `thm:for-transducers-are-polyregular`, `lemma:prenex-normal-form`,
  `lem:for-closed-under-composition`, `thm:pebble-are-continuous` and
  `thm:pebble-are-for`.  All five have since been proved, and every alias of
  `Labels.lean` now carries `assert_no_sorry`.  Every result of the
  formalisation depends only on `propext`, `Classical.choice`, `Quot.sound`.
* The six results that are proved from an explicit hypothesis carry it as the
  first explicit argument of the theorem, which was confirmed by `#check`:
  `¬ ComputablePred Transducers.PCP.Solvable` for
  `thm:undecidable-equivalence-rational-relations`;
  `Transducers.EffectiveWeightedEvalEq` for
  `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`,
  `thm:zeroness-weighted-automata` and `thm:decide-if-mealy`; and both
  `Transducers.EffectiveTwoWayEvalEq` and `Transducers.EffectiveTwoWayBound`
  for `thm:decidable-equivalence-regular`.
* Every divergence between a Lean statement and the book that the audit found
  is listed under *Divergences from the book* above, including the ones that
  were already documented elsewhere in this file, and including three notes
  that had gone stale because the book has since been corrected
  (`cor:2dfa-computes-all-regular-functions`,
  `thm:sequential-function-independent`,
  `nolabel:thm-fo-transduction-into-primes`).
* Rows that claimed a result was not formalised were re-checked against
  `Labels.lean` rather than against their own history.  Six were wrong and are
  now corrected: Lemma `lem:output-of-snake-graph-is-regular` (the book's snake
  lemma, `Transducers.boundedWidth_isRegular`), Claim
  `claim:transition-formula`, Lemma `lem:logic-reduction-to-type-n`, Claim
  `claim:fo-composition-quantifier-rank`, and the two claims of Section
  *Subsequential functions* that had been folded into one row.  Two results
  that were formalised but had no row of their own gained one, and two that
  are genuinely not formalised and were passed over in silence — Definition
  `def:rational-recognisable-subsets` and Conjecture
  `conj:regular-via-weighted-automata` — gained a row saying so.
* The file list of *Layout* was compared with what is on disk; eleven files
  that existed but were not listed have been added, and no listed file is
  missing.  Two further discrepancies came out of that comparison: the row for
  `PartC/SnakeParts.lean` credited it with `TwoWay.pieceOutput`, which is
  declared in `PartC/SnakeBlock.lean` (the row now names it there), and a
  hidden file `.section.lean` sat in the root of the project — a draft of the
  last section of `PartC/SnakeBlock.lean`, imported by nothing and built by
  nothing, which has been deleted.
* The same check was then applied to the *headers of the Lean files*, which are
  where a "not formalised" claim rots least visibly, and six of them said
  something that is no longer true.  `PartC/Statements.lean` listed Lemma
  `lem:output-of-snake-graph-is-regular` among the results it does not
  formalise; `PartC/MSO.lean` and `PartC/MSOOpen.lean` said that Claim
  `claim:transition-formula`, Lemma `lem:logic-reduction-to-type-n` and Claim
  `claim:fo-composition-quantifier-rank` are not formalised, when all three
  are, inside the proofs they belong to;
  `PartB/WeightedStatements.lean` said the same of Claims
  `claim:bounded-extensions` to `claim:eliminating-negative-letters`; and
  `PartB/RationalStatements.lean`, `PartB/WeightedStatements.lean`,
  `PartC/Statements.lean` and `PartD/Statements.lean` still announced that the
  proofs of their results are left as `sorry`.  Each header now says what is
  actually the case; no statement and no proof was changed.  (Part D's header
  now names the five results that really are statements only.)
* `EXERCISES.md` was checked the same way: every exercise it calls proved has
  an alias in `Labels.lean` with `assert_no_sorry`, and none of them depends on
  `sorryAx`; the seven exercises it calls not formalised have no alias.
* The dictionary of `LABELS.md` was compared with the `\newlabel` entries of
  the book's `main.aux`: every theorem-like label of the book has a row, and
  the only tag of the dictionary that is not a label of the book is the
  placeholder `nolabel:thm-fo-transduction-into-primes`, for the unnumbered
  paragraph that carries none.
* The whole check was run a second time, on a clean build, after the headers
  above were corrected: `lake build` succeeds (8272 jobs, no errors), the same
  five `sorry`s and no others remain, `#print axioms` on the 157 aliases
  reports `sorryAx` for exactly those five, and the six conditional results
  still carry their hypotheses as explicit arguments.
* The three scripts that this file, `README.md` and `LABELS.md` promise now
  exist, in `tools/`.  `tools/gen_labels.py` checks `Labels.lean` against the
  index tables rather than regenerating it, because the tables do not carry the
  per-entry notes of its docstrings; `tools/tex_numbering.py` checks the number
  column of `LABELS.md` against the book's `main.aux`; `tools/relabel.py`
  finds, and with `--fix` rewrites, any reference to a result of the book by
  number.  All three report no problem.

### The exercises added since the last audit

This section is appended by the pass that closed the remaining gap between the
`\exer` entries of the sources and the index of `EXERCISES.md`.  **No numbered
result of the main text was touched by it**: the only files it changed outside
`RequestProject/Exercises/` are `RequestProject/Exercises.lean` (imports),
`RequestProject/Labels.lean` (one alias and one `assert_no_sorry` per new
exercise) and `EXERCISES.md`.

The exercise files of the project are now

```
RequestProject/Exercises/
  Intro.lean          IntroAux.lean
  PartA.lean          KrohnRhodes.lean
  PartBC.lean         PartBCAux.lean      PartBCPCP.lean   PartBCUnary.lean
  MyhillNerode.lean   RegularPrimes.lean
  TwoDFAEx.lean       TwoDFALoop.lean     TwoNFT.lean      TwoNFT2.lean
  SST.lean            SSTAux.lean         SSTPoly.lean
  LogicEx.lean        Compression.lean    ForFO.lean
```

(the exact list is the import list of `RequestProject/Exercises.lean`), and the
two files added last are

| file | contents |
| --- | --- |
| `Exercises/ForFO.lean` | Exercise `exer:for-transducers-simulate-fo`: the translation of a first-order sentence into a for-transducer that outputs `yes` or `no`, with the linear bound `10·fsize φ + 5` on the size of the program (`Transducers.Exercises.exists_forProg_of_isFO`) |
| `Exercises/TwoNFT2.lean` | the second half of Exercise `exer:2nft`: the relation `{(aⁿ, v v) : |v| = n}` is computed by the second nondeterministic two-way model and not by the first (`Transducers.Exercises.exists_isTwoNFT₂_not_isTwoNFT₁`) |

`#print axioms` on every declaration named above, and on every alias of
`RequestProject/Labels.lean`, reports only `propext`, `Classical.choice`,
`Quot.sound`; there is no `sorry` in `RequestProject/Exercises/`.  Fifty-eight
of the book's eighty-three exercises are formalised; the twenty-five that are
not are listed, with the reason for each, in `EXERCISES.md`.

## The exercises added after that (`exer:decide-unambiguous`)

This run continued the formalisation of the exercises, and again **no numbered result of the
main text was touched**: the only files it changed outside `RequestProject/Exercises/` are
`RequestProject/Exercises.lean` (two imports), `RequestProject/Labels.lean` (the two aliases of
`exer:decide-unambiguous`) and `EXERCISES.md`.

Every `\exer` of the book's sources whose solution is non-empty was re-extracted and compared
with the index of `EXERCISES.md`; the book has eighty-three exercises, eighty-two of them with a
solution, and every one of them already had a row in that index.  What this run added is one
more formalised exercise and one half of another:

| file | contents |
| --- | --- |
| `Exercises/NFAUnambig.lean` | Exercise `exer:decide-unambiguous`: runs of an nfa (Mathlib's `NFA`, whose transitions read one letter, which is the ε-free form the solution reduces to), the identification of its language with the inputs that have an accepting run (`Transducers.Exercises.mem_accepts_iff_exists_accRun`), the product automaton of the solution, the criterion for ambiguity (`Transducers.Exercises.ambiguous_iff_reach`) and the resulting decision procedure (`Transducers.Exercises.decidableUnambiguousNFA`), together with the auxiliary fact that reachability in a finite graph is decidable |
| `Exercises/RatInjective.lean` | the first step of the solution to `exer:rational-injectivity-decidable`: a rational function is injective exactly when it has a rational left inverse (`Transducers.Exercises.rationalFun_injective_iff_exists_inverse`), and the auxiliary closure of the rational relations under union (`Transducers.Exercises.isRationalRel_union`), proved by the disjoint union of two nfas with output.  The decision procedure itself is not formalised — it needs a *code* for the left inverse, which the project's uniformisation does not provide — so the exercise stays listed as not formalised in `EXERCISES.md` |

`#print axioms` on every declaration named above, and on the two new aliases of
`RequestProject/Labels.lean`, reports only `propext`, `Classical.choice`, `Quot.sound`; there is
still no `sorry` in `RequestProject/Exercises/`.  Fifty-nine of the book's eighty-three exercises
are now formalised; the twenty-four that are not are listed, with the reason for each, in
`EXERCISES.md`.  `lake build` succeeds with no errors.
