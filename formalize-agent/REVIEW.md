
## 2026-08-26 05:24:11Z — exercises-partA conflicts with local work

The run started from f0c656d6 and its result does not merge cleanly into what the repository holds now — the same files were changed on both sides. Nothing has been lost: the run is on branch `aristotle/fd9fa871`.

    git -C /Users/bojan/Documents/ksiazki/transducer-book-lean/transducer-lean merge aristotle/fd9fa871

## 2026-08-26 12:14:20Z — exercises-partBC conflicts with local work

The run started from a361636c and its result does not merge cleanly into what the repository holds now — the same files were changed on both sides. Nothing has been lost: the run is on branch `aristotle/b4fce171`.

    git -C /Users/bojan/Documents/ksiazki/transducer-book-lean/transducer-lean merge aristotle/b4fce171

## 2026-08-26 16:55:16Z — audit finished: audit-C

Aristotle's audit report follows. Divergences from the book and status corrections are what to look for.

The audit is finished; everything is committed and pushed, and `lake build` succeeds from scratch.

**1. Build.** `lake build` from scratch: 8272 jobs, no errors. The only `declaration uses sorry` warnings are five, all in `RequestProject/PartD/Statements.lean` (lines 182, 188, 194, 290, 298); the rest are Lean style warnings. The build was run twice, before and after the corrections below.

**2. Axioms.** `#print axioms` was run on all 157 aliases of `RequestProject/Labels.lean` (one per label the formalisation covers, main text and exercises). Exactly five depend on `sorryAx` — `thm:for-transducers-are-polyregular`, `lemma:prenex-normal-form`, `lem:for-closed-under-composition`, `thm:pebble-are-continuous`, `thm:pebble-are-for` — and these are exactly the five carrying `assert_uses_sorry` and marked "statement only". Every other result, and every formalised exercise of `EXERCISES.md`, depends only on `propext`, `Classical.choice`, `Quot.sound`. The six conditional results carry their hypothesis as an explicit first argument (confirmed with `#check`): `¬ ComputablePred Transducers.PCP.Solvable` for `thm:undecidable-equivalence-rational-relations`; `Transducers.EffectiveWeightedEvalEq` for `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata`, `thm:decide-if-mealy`; `Transducers.EffectiveTwoWayEvalEq` and `Transducers.EffectiveTwoWayBound` for `thm:decidable-equivalence-regular`.

**3. Divergences between the Lean statements and the book** (all now collected in one place, *Divergences from the book* in `THEOREMS.md`; none fixed, as instructed):
*Corrected because the printed version is false*: `def:aperiodic-mealy` (last letter eventually constant in `Option B`; the book's side conditions dropped); `lemma:derivatives` (the derivative drops the output produced while reading `w`); `claim:conditional` (false on the empty input — counterexample `not_sum_of_regular_nil`).
*Equivalent or restricted form*: `thm:equivalence-decidable-mealy` (finite check on inputs of bounded length rather than a `Decidable` instance); `thm:decide-if-mealy` (property relativised to strings over the alphabet of the code); `lem:aperiodicity-minimal-machine` ("some machine computing `f` satisfies (*)"; finiteness assumptions omitted); `lem:k-types-fo-equivalence` (sentences rather than formulas); `lem:output-of-snake-graph-is-regular` (stated for the width-`k` output function of a two-way transducer, for every `k`, rather than for an alphabet of snake letters); `claim:transition-formula` (index of a bimachine rather than an unambiguous transducer); Claims `claim:bounded-extensions`, `claim:computing-branching-part`, `claim:offsets-are-regular`, `claim:eliminating-negative-letters` (reorganised inside the proof of `thm:subsequential-functions`).
*Part of a statement not formalised*: the final sentence of `thm:aperiodic-mealy` ("moreover, this property can be decided"); `def:rational-recognisable-subsets`; `conj:regular-via-weighted-automata`, `lem:compute-configuration-graph`, `lem:check-if-output-string-of-configuration-graph-belongs-to-L` and the five pebble-configuration results of Part D.
*Added hypotheses*: the six conditional results listed above.
*Notes that had gone stale because the book has been corrected*: `cor:2dfa-computes-all-regular-functions` (inclusion no longer printed the wrong way round), `thm:sequential-function-independent` (item (c) is now in the sources, so the Lean statement is faithful), `nolabel:thm-fo-transduction-into-primes` (no longer a numbered environment).

**4. Statuses changed in `THEOREMS.md`.** Six rows that claimed a result was not formalised were wrong and are corrected: `lem:output-of-snake-graph-is-regular` (proved, `Transducers.boundedWidth_isRegular` in `SnakeReg.lean`, only the three standard axioms — it now has its own row and an alias with `assert_no_sorry`, and the accounting list of `Labels.lean` and `LABELS.md` agree), `claim:transition-formula`, `lem:logic-reduction-to-type-n`, `claim:fo-composition-quantifier-rank`, and the two claims of *Subsequential functions* that had been folded into one row. Two formalised results gained a row of their own; two genuinely unformalised items that were passed over in silence gained one — Definition `def:rational-recognisable-subsets` (kept as not formalised: nothing depends on it) and Conjecture `conj:regular-via-weighted-automata`. `C.2.3`/`C.2.4` remain genuinely not formalised. No result's proved/open status was found to be overstated: everything marked proved really is, and the five Part D results marked open really are.

In this final pass I also found and corrected rot of the same kind inside the Lean file headers: `PartC/Statements.lean` still listed the snake lemma among the results it does not formalise; `PartC/MSO.lean` and `PartC/MSOOpen.lean` said the same of `claim:transition-formula`, `lem:logic-reduction-to-type-n`, `claim:fo-composition-quantifier-rank`; `PartB/WeightedStatements.lean` of `claim:bounded-extensions`–`claim:eliminating-negative-letters`; and four statement files still announced that their proofs are left as `sorry`. Two file-list entries were wrong: `TwoWay.pieceOutput` is declared in `SnakeBlock.lean`, not `SnakeParts.lean`, and a hidden `.section.lean` — a dead draft of the last section of `SnakeBlock.lean`, imported and built by nothing — sat in the project root and has been deleted. No statement and no proof was touched.

**Labels.** Every result of the book is named by its LaTeX `\label` in docstrings, tables and prose; `tools/relabel.py` confirms no result is named by a number. All nineteen guessed placeholders were replaced by the real labels (including `item:fo-types-more-information` → `lem:k-types-properties`, and the conjecture's `conj:regular-via-weighted-automata`); the one correct placeholder, `nolabel:thm-fo-transduction-into-primes`, remains, and it is the only tag in `LABELS.md` that is not a label of the book. All 88 rows of the authoritative correspondence match the aliases in `Labels.lean`. Two formalised results are not in that table and keep their own labels, both of which do exist in the book: `def:polyregular-functions` and `thm:polyregular-functions-are-continuous` (Part D, the latter proved).

**The promised scripts.** I wrote them rather than dropping the documentation: `tools/gen_labels.py --check` (checks `Labels.lean` against `LABELS.md`, `THEOREMS.md` and `EXERCISES.md`; `--emit` writes a new entry), `tools/tex_numbering.py --check` (checks the number column of `LABELS.md` against the book's `main.aux`), `tools/relabel.py` (finds, and with `--fix` rewrites, references by number). All three report no problem. `gen_labels.py` checks rather than regenerates, because several entries carry docstring notes the tables do not hold; `README.md` says so.

**Current state of the formalisation.** Parts A, B and C are proved in full — outright, except `thm:undecidable-equivalence-rational-relations` (from the undecidability of PCP), `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata`, `thm:decide-if-mealy` (from `EffectiveWeightedEvalEq`) and `thm:decidable-equivalence-regular` (from `EffectiveTwoWayEvalEq` and `EffectiveTwoWayBound`). In Part D, `thm:polyregular-functions-are-continuous` is proved and the five results named above are statements only; `nolabel:thm-fo-transduction-into-primes` stays withdrawn.

## 2026-08-27 22:25:42Z — audit finished: audit-final

Aristotle's audit report follows. Divergences from the book and status corrections are what to look for.

Closing audit of the Lean formalisation of *Transducers* in `transducer-lean/`. No new numbered result was attempted; everything below is verification, reconciliation and documentation. All work is committed and pushed.

## 1. `lake build` from scratch

The build directory did not exist at the start of the run, so this was a genuine from-scratch build (Mathlib cache fetched, then everything compiled). Result: **`Build completed successfully (8336 jobs)`, 0 errors.**

A first from-scratch build reported **125 warnings**. I fixed 80 of them (see below) and rebuilt twice more from the changed files; the final build has **45 warnings**, of exactly two kinds and no others:

* 28 × `automatically included section variable(s) unused in theorem …`
* 17 × `unused variable …`

Every one of these sits on an auxiliary lemma where removing the variable would change the lemma's signature (and in the `section variable` cases the variable is genuinely needed by neighbouring lemmas sharing the binder). They are left in place deliberately and this is recorded in `THEOREMS.md`. The 80 warnings that were fixed were: 62 unused `simp` arguments removed, 8 resulting `simp []`/`simp_all []`/`simpa []` collapsed to bare form, 2 deprecated names updated (`List.take_succ` → `List.take_add_one`, `Fin.coe_castSucc` → `Fin.val_castSucc`), 3 `simpa` → `simp`, 5 `<;>` → `;`, plus a no-op `congr 1`, a dead `<;> omega`, two `intro` chains merged and two unmatched simp lemmas dropped.

## 2. Classification of every numbered result

The book has **100 theorem-like environments**. **90 are formalised** (20 definitions and 70 results); 10 are not.

* **64 results proved outright** — `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
* **6 results proved from an explicit hypothesis**, taken as an ordinary theorem argument (never an `axiom`), so `#print axioms` on them still reports only the three standard axioms:
  * `thm:undecidable-equivalence-rational-relations` — hypothesis `¬ ComputablePred Transducers.PCP.Solvable` (undecidability of Post correspondence), in `PartB/PCPRed.lean`;
  * `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata`, `thm:decide-if-mealy` — hypothesis `Transducers.EffectiveWeightedEvalEq`, in `PartB/Effective.lean`;
  * `thm:decidable-equivalence-regular` — hypotheses `Transducers.EffectiveTwoWayEvalEq` and `Transducers.EffectiveTwoWayBound`, in `PartC/EffectiveReg.lean`.

  In all six cases the mathematics is fully proved in the project; what is isolated as a hypothesis is only the effectivity step, which runs into the absence of arithmetic on `ℤ`/`ℚ` in Mathlib's `Primrec`/`Computable` API.
* **10 environments not formalised**, each with a reason in `THEOREMS.md`: `def:rational-recognisable-subsets`, `conj:regular-via-weighted-automata` (a conjecture), `lem:compute-configuration-graph`, `lem:check-if-output-string-of-configuration-graph-belongs-to-L`, `lem:reachability-pebble-automaton`, `claim:reachability-basic-run`, `lem:children-of-configuration-in-pebble-run`, `claim:from-configuration-to-child-configuration-graph`, `claim:from-child-configuration-graph-to-children`, and `nolabel:thm-fo-transduction-into-primes` (withdrawn by the author; it is *not* counted as missing). In addition, the final decidability sentence of `thm:aperiodic-mealy` is not formalised, though the characterisation it rests on is.

Rather than rely on a one-off `#print axioms` sweep, I **strengthened the project's `assert_no_sorry` command** in `RequestProject/Labels.lean` so that it now also fails if the declaration uses any axiom outside `propext`, `Classical.choice`, `Quot.sound`. All **180 label aliases** — the 90 formalised environments and the 59 formalised exercises among them — are followed by `assert_no_sorry`, so the claim above is re-checked by the kernel on every build. There is not a single `assert_uses_sorry` left.

## 3. `sorry` and `axiom`

**No live `sorry` anywhere in the project.** Four textual occurrences remain, all inside `/- … -/` block comments that preserve a superseded statement as a record: `PartB/WeightedStatements.lean` (two commented-out blocks), `PartC/MSOOpen.lean:95`, `PartC/Statements.lean:245` and `:361`. `THEOREMS.md` lists no declaration as open-with-`sorry`, and none exists. There is **no `axiom` declaration, no `@[implemented_by]`, and no `native_decide`** in the project; the six conditional results use theorem arguments, exactly as documented.

## 4. Divergences from the book (re-read against the LaTeX)

Still current, each documented in the docstring and collected in one section of `THEOREMS.md`:

* `def:aperiodic-mealy` — aperiodicity is stated in `Option B`; demanding an actual output letter makes the notion unsatisfiable on `u = v = w = ε`.
* `claim:conditional` — false on the empty input as printed; the corrected statement excludes ε, with the faithful version kept alongside.
* `lem:k-types-fo-equivalence` — stated for sentences, not arbitrary formulas, which is what the proof uses.
* `lem:aperiodicity-minimal-machine` — "some machine computing `f`" rather than "the minimal machine"; equivalent, and avoids constructing the minimal machine.
* `thm:aperiodic-mealy` — the decidability sentence is not formalised.
* `thm:equivalence-decidable-mealy` — rendered as an explicit finite check rather than an appeal to a decision procedure.
* `thm:decide-if-mealy` — relativised to the code alphabet, since codes are what the effectivity hypothesis speaks about.
* `lem:output-of-snake-graph-is-regular` — stated with `widthOut` and for all `k`, which is the form the proof needs.
* `claim:transition-formula` — indexed by the bimachine rather than left implicit.
* The four `claim:bounded-extensions` … `claim:eliminating-negative-letters` are formalised in reorganised form inside the proof of `thm:subsequential-functions`.

Three previously reported divergences have been **corrected in the author's sources** and the Lean is now literally faithful: `cor:2dfa-computes-all-regular-functions` (inclusion direction), `thm:sequential-function-independent` (the "ε ↦ ε" condition is now item (c)), and — newly found this run — **`lemma:derivatives`**: `krohn-rhodes.tex` now defines the derivative as "`v ↦ f(wv)` with the first `|w|` letters of the output removed", which is exactly the Lean `deriv`. I moved that entry out of the divergence list and rewrote the `deriv` docstring in `PartA/Statements.lean` accordingly. Spot-checks of `thm:krohn-rhodes`, `thm:bimachines`, `thm:mso-logic-languages`, `thm:for-transducers-are-polyregular`, `thm:pebble-are-for` and `thm:composition-of-two-way-transducers` against the tex turned up no new divergence.

Label↔number confirmations recorded: A.2.7 = `def:aperiodic-mealy`, A.2.10 = `lemma:derivatives`, B.4.6 = `thm:sequential-function-independent`, C.4.16 = `thm:fo-rational-functions` (so the withdrawn C.4.17 is the unnumbered closing paragraph of `logic.tex`, which has no label in the sources I have — it is referred to as `nolabel:thm-fo-transduction-into-primes`).

## 5. `THEOREMS.md`

Now a complete final index. Every one of the 95 index rows carries the result's **label, Lean name, status and — new this run — the file it lives in**; the `File` column was added to all five index tables and is machine-checked by a new script `tools/decl_files.py --check`. The `## Status` section was rewritten from ~386 lines of accreted history into: counts table, the six conditional results with their hypotheses, the ten unformalised environments with reasons, `sorry` and axioms, the build's warnings, the exercises, and how the index is kept honest. All divergences are collected in a single section. I also corrected two wrong numbers in `LABELS.md`.

Five self-checks now pass: `tools/gen_labels.py --check` (Labels.lean agrees with LABELS.md and the index tables, 180 aliases, 10 environments accounted for), `tools/decl_files.py --check`, `tools/tex_numbering.py --check` (every number agrees with `main.aux`), `tools/relabel.py` (no result is named by its number), `tools/extract_exercises.py` (83 exercises, 82 with a solution).

## 6. `FORMALISATION.md`

New, 215 lines, written for a reader of the book: how much is formalised; the conventions (strings as `List`, alphabets, how machines and transductions are modelled, how decidability statements are phrased); what the book gets wrong or states imprecisely and had to be adjusted, including the three items the author has since fixed; the six conditional results and why; what is not formalised and why; and why the index can be believed.

## Exercise audit

The book has **83 exercises, 82 with a written solution. 59 are formalised**, all aliased and hence checked free of `sorryAx` and of non-standard axioms on every build; there is no `sorry` in `RequestProject/Exercises/`. Three of the 59 carry an explicit hypothesis rather than being outright: `exer:function-that-is-not-rational`, `exer:rational-relations-intersection-undecidable`, and item (a) of `exer:decide-rational-colision`.

**24 are not formalised, and 23 of those have a written solution** — this is the list for the author:

`exer:2dfa-complexity`, `exer:2dfa-loop-elimination-sipser`, `exer:2dfa-unary-output`, `exer:2nft-uniformise`, `exer:all-ideals`, `exer:decide-same-ideal`, `exer:factoring-through-a-rational-function`, `exer:fo-non-elementary`, `exer:fo-suc`, `exer:for-transducer-continuity-nonelementary`, `exer:forward-for-transducer`, `exer:full-ideal`, `exer:minimal-bimachine-lexicographic`, `exer:non-minimal-automaton`, `exer:polynomial-ideals`, `exer:polyregular-unmarked-squaring`, `exer:rational-composition-finiteness-undecidable`, `exer:rational-compression`, `exer:rational-injectivity-decidable`, `exer:rational-outpus-of-exactly-linear-size`, `exer:rational-outpus-of-exactly-linear-size-rational-number`, `exer:regular-compression`, `exer:regular-outpus-of-exactly-linear-size`, plus the unlabelled exercise at `rational-functions.tex:440`. The single exercise with no solution is the commented-out one at `rational-functions.tex:311`. Each of the 23 is accounted for in `EXERCISES.md` with a reason, grouped as: complexity/state-count claims the project does not model; theory the project lacks (maximum cycle mean, Ehrenfeucht–Fraïssé games); reliance on the string encoding of the configuration graph, which is deliberately not formalised; two long case analyses in `myhill-nerode.tex`; and `exer:forward-for-transducer`, which would need both inclusions of `thm:for-transducers-are-polyregular` replayed with loop directions tracked. Following the rule about shared index files, I touched only the one `EXERCISES.md` bullet that was inconsistent (the two commented-out exercises of `rational-functions.tex`, now described by file and line since neither has a number in `main.aux`) and left every other chapter's entries exactly as I found them.

## Caveats

Theorem C.4.17 is absent from the sources and from the index, as instructed, and is not counted anywhere as missing. The withdrawn paragraph and the unlabelled exercise at `rational-functions.tex:440` have no `\label` in the copy of the book available here; they are identified by file and line rather than by an invented label.

## 2026-08-28 06:16:20Z — encoding-snake-alphabet was canceled

Task 6983a6d2-566a-4e33-94a0-45b8179f9aa0 was canceled, so nothing was integrated for encoding-snake-alphabet and the run has moved on to the next target.

If you cancelled it because you were doing the work yourself, that run is in a project of its own and this driver cannot see it. Bring it in with:

    driver.py integrate <project-id> --base <commit>

and then `driver.py requeue encoding-snake-alphabet` if more is still wanted from it.

## 2026-08-28 21:30:33Z — audit finished: audit-final

Aristotle's audit report follows. Divergences from the book and status corrections are what to look for.

Closing audit of the formalisation of *Transducers* in `transducer-lean/`. No new numbered result was attempted; the project was rebuilt from scratch, re-verified declaration by declaration, re-checked against the LaTeX sources, and the three index files were brought to their final state.

## 1. `lake build` from scratch

Run from `transducer-lean/` (the root of the Lean package) with an empty `.lake/build`: **succeeds, 8386 jobs, 0 errors**. The only diagnostics are **47** Lean linter warnings, all inside auxiliary proofs, never in the statement of a numbered result:

* **30 × `automatically included section variable(s) unused in theorem …`** — in `PartC/RunElts.lean` (3), `PartC/RunMark.lean` (3), `PartC/SnakeBlock.lean` (3), `PartC/SnakeChkAcc.lean` (1), `PartC/SnakeChkAnn.lean` (8), `PartC/SnakeChkStruct.lean` (6), `PartC/SnakeChkVerify.lean` (4), `PartD/CGSem.lean` (2).
* **17 × `unused variable …`** — in `PartB/SeqChar.lean` (1), `PartC/SnakeChkBuild.lean` (1), `PartC/SnakeChkCtx.lean` (1), `PartC/SnakeChkReadData.lean` (1), `PartC/SnakeChkStruct.lean` (2), `PartC/SnakeLocal.lean` (1), `PartC/SnakeWinRun.lean` (6), `PartD/ForPrenex.lean` (1), `PartD/PebbleSeq.lean` (2), `Exercises/Compression.lean` (1).

Acting on either kind would change the signature of a helper lemma, so they are left and inventoried in `THEOREMS.md`. The 13 remaining *mechanical* warnings (unused `simp` arguments in `Exercises/CompressionMapLift.lean`, added after the previous audit) were removed in this run.

## 2. `#print axioms` on every formalised numbered result

A new script, `tools/print_axioms.sh`, runs `#print axioms` on all **196** aliases of `RequestProject/Labels.lean` — **116** covering the 97 formalised theorem-like environments of the book, **80** covering the 65 formalised exercises. Result: *every one of the 196 depends only on `propext`, `Classical.choice`, `Quot.sound`*. No `sorryAx`, no other axiom.

Classification of the book's **100 theorem-like environments**:

* **20 definitions formalised** (Introduction 1, A 4, B 7, C 6, D 2).
* **71 results proved outright** — Part A 11, Part B 21, Part C 28, Part D 11. **Parts A, B and D are proved in full**, and so is Part C apart from the one conditional result below.
* **6 results proved from an explicit hypothesis**, taken as an ordinary theorem argument (so `#print axioms` still reports only the three standard axioms):
  * `thm:undecidable-equivalence-rational-relations` — `¬ ComputablePred Transducers.PCP.Solvable` (undecidability of Post correspondence);
  * `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata`, `thm:decide-if-mealy` — `Transducers.EffectiveWeightedEvalEq`;
  * `thm:decidable-equivalence-regular` — `Transducers.EffectiveTwoWayEvalEq` and `Transducers.EffectiveTwoWayBound`.
  These isolate the fact that Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℤ`/`ℚ`; the non-effective mathematics behind them (Schützenberger's bound, `Transducers.regularFun_eq_of_short`) is proved unconditionally.
* **3 environments not formalised, none of them an unfinished proof**: Definition `def:rational-recognisable-subsets` (used once, in a remark), Conjecture `conj:regular-via-weighted-automata` (an open conjecture, not a result), and `nolabel:thm-fo-transduction-into-primes` (withdrawn by the author; kept only as a comment in `PartC/MSOOpen.lean`, which declares nothing — its easy half survives as `Transducers.isFOTransduction_of_compClosure`). The result the author withdrew is not reinstated and is not counted as missing.

**Nothing formalised is left open.** One *part* of a formalised statement is not formalised: the closing sentence of `thm:aperiodic-mealy`, "moreover, this property can be decided given a Mealy machine that computes `f`".

Every label used above was found in the LaTeX sources; the only tag that is not a `\label` of the book is the placeholder `nolabel:thm-fo-transduction-into-primes`, for the unnumbered paragraph at the end of `logic.tex`, which carries none.

## 3. `sorry` and `axiom`

`RequestProject/` contains **no `sorry`, no `axiom`, no `@[implemented_by]`, no `native_decide`**. `lake build` emits not one `declaration uses 'sorry'`. The token `sorry` occurs ten times, every one inside a block comment preserving a statement the project does not make: six in `PartB/WeightedStatements.lean` (the unconditional forms of the four decidability theorems, the earlier unrelativised `thm:decide-if-mealy`, the earlier edition of `thm:sequential-function-independent`), two in `PartC/Statements.lean` (unconditional `thm:decidable-equivalence-regular`, the printed false form of `claim:conditional`), two in `PartC/MSOOpen.lean` (the withdrawn theorem and its open half). This was checked by a comment-aware scan, not by eye.

## 4. Divergences from the book (re-read against the LaTeX this run)

*Corrected because the printed statement is false*
* `def:aperiodic-mealy` — the last letter is taken in `Option B`; asking for a real output letter makes aperiodicity unsatisfiable (`u = v = w = ε`).
* `claim:conditional` — corrected on the empty input; as printed it is false there, with `Transducers.not_sum_of_regular_nil` as counterexample.

*Equivalent or restricted form*
* `thm:equivalence-decidable-mealy` — the finite check "agree on inputs of length ≤ |Q₁|·|Q₂|" rather than a `Decidable` instance.
* `thm:decide-if-mealy` — the decided property is relativised to the alphabet of the code (a code reads only finitely many letters).
* `lem:aperiodicity-minimal-machine` — "some machine computing `f` satisfies (*)" rather than "the minimal machine does"; equivalent, and avoids constructing the minimal machine.
* `lem:k-types-fo-equivalence` — quantifies over first-order *sentences*; "formulas" has no meaning without a valuation.
* `lem:output-of-snake-graph-is-regular` — the book's alphabet, but for every `k : ℕ`, not only `k ∈ {1,…,|Q|}` (more general).
* `claim:transition-formula` — stated for the index of a bimachine rather than for an unambiguous transducer.
* `lem:reachability-pebble-automaton`, `claim:reachability-basic-run` — the book's mso formula `φ(s,t)` is rendered as a regular language of encodings of configuration pairs (equivalent by `thm:mso-logic-languages`), required correct only on genuine encodings.
* `lem:children-of-configuration-in-pebble-run`, `claim:from-configuration-to-child-configuration-graph` — carry the hypothesis `st.length < k`, which is the case distinction the book's own proof opens with.
* `claim:bounded-extensions`, `claim:computing-branching-part`, `claim:offsets-are-regular`, `claim:eliminating-negative-letters` — the four steps are reorganised inside the Lean proof of `thm:subsequential-functions`.

*Added hypothesis*
* the six conditional results listed in §2, and `lem:check-if-output-string-of-configuration-graph-belongs-to-L`, which assumes the transducer computes a total function (the only way the book uses it).

*Not formalised* — the decidability sentence of `thm:aperiodic-mealy`; `def:rational-recognisable-subsets`; `conj:regular-via-weighted-automata`.

*Divergences the book has since removed* (the Lean statements are now faithful): `cor:2dfa-computes-all-regular-functions` (inclusion once printed backwards), `thm:sequential-function-independent` (missing condition, now item (c)), `lemma:derivatives` (the derivative now removes the first `|w|` output letters).

No divergence recorded in a Lean docstring is missing from that list, and every listed one still matches the current `.tex`.

## 5–6. `THEOREMS.md` and `FORMALISATION.md`

`THEOREMS.md` is the complete final index: every one of the 100 environments has a row giving its LaTeX label, Lean name, status and file; the divergences are collected in one section; the `## Status` section now carries the corrected alias counts (196 = 116 + 80), the exact warning inventory, the exact `sorry`-in-comment inventory, and the recounted exercise figures. `FORMALISATION.md` is the prose companion for a reader of the book (what is done, the conventions, what the book gets wrong or leaves imprecise, the six hypotheses, what is left out and why, and why the tables can be believed); it was updated with the same corrections. `README.md` documents the new script and where `lake build` is run.

All five bookkeeping checks pass: `tools/print_axioms.sh`, `gen_labels.py --check`, `tex_numbering.py --check`, `decl_files.py --check`, `relabel.py`.

## 7. The exercises

`EXERCISES.md` was audited the same way and a new `## Status (closing audit)` section was appended (nothing existing was rewritten). Correction to the earlier counts: the sources contain 83 `\exer` environments, but two of them (line 311 and the unlabelled one at line 440 of `rational-functions.tex`) are **commented out** and carry no number in `main.aux`, so **the book has 81 exercises, all with a written solution**. **65 are formalised and proved** (not 63) and **16 are not** (not 20). Every one of the 65 is free of `sorryAx`: each has an alias with `assert_no_sorry`, and the `#print axioms` sweep covers all 80 exercise aliases.

**Exercises of the book that have a written solution and no formalisation (16)**, with the reason:
`exer:rational-outpus-of-exactly-linear-size` and `exer:rational-outpus-of-exactly-linear-size-rational-number` (maximum cycle mean of a weighted graph); `exer:regular-outpus-of-exactly-linear-size` (reduces to those two); `exer:full-ideal`, `exer:polynomial-ideals`, `exer:all-ideals`, `exer:decide-same-ideal` (growth rates of regular languages); `exer:rational-injectivity-decidable` (its mathematical first step *is* proved, in `Exercises/RatInjective.lean`; the decision procedure needs a computable form of the Uniformisation Lemma); `exer:rational-composition-finiteness-undecidable` (undecidability reduction not carried out for codes); `exer:minimal-bimachine-lexicographic` and `exer:non-minimal-automaton` (a Myhill–Nerode theory for bimachines; a case analysis the solution only sketches); `exer:fo-non-elementary` and `exer:fo-suc` (non-elementary succinctness; Ehrenfeucht–Fraïssé games); `exer:polyregular-unmarked-squaring` (rests on the polynomial-*time* half of the compression exercises); `exer:for-transducer-continuity-nonelementary` (rests on `exer:fo-non-elementary`); `exer:forward-for-transducer` (needs both inclusions of `thm:for-transducers-are-polyregular` replayed with loop directions tracked). Item (b) of the otherwise formalised `exer:decide-rational-colision` is also left out.

Three of the 65 diverge from the literal exercise, each documented: `exer:rational-compression` and `exer:regular-compression` are proved in their *size* half (running time is not modelled), and `exer:2dfa-complexity` is proved by a construction the book does not give, the author's own construction giving only a superpolynomial bound (it is kept alongside, with the bound it really gives). Three carry an explicit hypothesis: `exer:function-that-is-not-rational`, `exer:rational-relations-intersection-undecidable`, item (a) of `exer:decide-rational-colision`.

## Housekeeping

Two leftover files were removed from the top of `transducer-lean/`: `Scratch.lean`, a byte-for-byte duplicate of `RequestProject/PartD/ChildGraphOfRun.lean`, and `--help`, a captured tool output. Neither was part of the Lean library. The LaTeX sources of the book were not touched.
