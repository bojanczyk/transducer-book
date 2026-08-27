# Summary of the audit of the index (Parts A, B and C)

Every numbered result that `THEOREMS.md` records as proved was re-checked mechanically, and the
index, `EXERCISES.md`, `LABELS.md` and `RequestProject/Labels.lean` were corrected where they were
wrong.  What the check consists of, and what it found, is written up in `THEOREMS.md`, in the
section *The audit of this index*.  In brief:

* `lake build` from scratch succeeds (8272 jobs, no errors).  The only `sorry`s in the project are
  the five statements of Part D that are still open, in `RequestProject/PartD/Statements.lean`.
* `#print axioms` on all 157 aliases of `RequestProject/Labels.lean` reports `sorryAx` for exactly
  those five results and for nothing else; every other result, and every formalised exercise,
  depends only on `propext`, `Classical.choice`, `Quot.sound`.
* The six deliberately conditional results carry their hypothesis as an explicit first argument,
  confirmed by `#check`.
* Every divergence between a Lean statement and the book is collected in one list, *Divergences
  from the book*.
* The results of the book are named by their LaTeX `\label` everywhere -- docstrings, tables and
  prose -- and `tools/` now holds the three scripts that `README.md`, `LABELS.md` and `THEOREMS.md`
  promise (`gen_labels.py`, `tex_numbering.py`, `relabel.py`), all of which report no problem.
* Stale claims of the form "not formalised" were re-checked against the Lean environment rather
  than against their own history, in the index and in the headers of the Lean files alike; the
  ones that were wrong are listed in *The audit of this index*.

# Summary of changes for the exercises of Parts B and C (continuation)

Continuing the formalisation of the exercises of Parts B and C, the one exercise of
`rational-relations.tex` that had been left out, Exercise `ex:recognisable-relations`, is now
formalised and proved in `RequestProject/Exercises/PartBC.lean`, at its place in the chapter (it is
the last exercise of that chapter).

* `Transducers.Exercises.IsRecognisableRel` renders the book's Definition
  `def:rational-recognisable-subsets` for the monoid `A* x B*` only -- the general notion, for an
  arbitrary monoid, is still not part of this formalisation -- in the form the author's solution
  uses: the inverse image of a subset of a finite monoid under a monoid homomorphism.
* `Transducers.Exercises.isRecognisableRel_iff_finite_union` is the exercise: a subset of
  `A* x B*` is recognisable if and only if it is a union of finitely many products of a regular
  language over the input alphabet with a regular language over the output alphabet.

Exercise `exer:rational-one-letter-input` is formalised and proved as well, at its place in
`rational-functions.tex`, as `Transducers.Exercises.rationalFun_unary_graph`: the graph of a
rational function whose input alphabet has one letter is a finite union of sets
`{ (a^(α+βk), x yᵏ z) | k ∈ ℕ }`.  The proof is the author's: a bimachine computing the function
exists by Theorem `thm:bimachines`, the runs of its prefix and suffix automata over a one-letter
alphabet are eventually periodic, and each further period inserts one more group of gaps in the
middle, producing the same piece of output as the other such groups.  The analysis of the gaps is
in the new file `RequestProject/Exercises/PartBCUnary.lean`.

The identification of the regular languages with the languages recognised by a homomorphism into a
finite monoid, which the solution recalls as standard, is proved in
`RequestProject/Exercises/PartBCAux.lean` (`isRegular_of_wordHom` for one direction, and
`exists_wordHom_of_isRegular`, through the transition monoid of a dfa, for the other).  The alias
for the label is in `RequestProject/Labels.lean`, followed by `assert_no_sorry`, and `EXERCISES.md`
records the exercise as proved.  No numbered result of the main text was touched; the whole project
builds and the new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

# Summary of changes for the exercises of Part A

The twelve exercises of Part A of the book — the seven of `mealy.tex` and the five of
`krohn-rhodes.tex` — are formalised and proved in the new file
`RequestProject/Exercises/PartA.lean` (rolled up by `RequestProject/Exercises.lean`), one section per
chapter, in the order in which the book states them.  Each proof follows the author's own solution,
which the printed edition does not typeset; the docstrings say where a proof deviates.

Every exercise of Part A carries a LaTeX `\label`, so all of them are referred to by their labels,
and all of them get an alias in `RequestProject/Labels.lean`, in a new *Exercises* section, each
followed by `assert_no_sorry`.  The exercises are indexed in the new `EXERCISES.md`, in the style of
`THEOREMS.md`, which is where they belong since an exercise is not a numbered result;
`THEOREMS.md` and `README.md` only record that the exercises live elsewhere.

Several exercises are not mathematical statements as they stand ("give an example of…", "is the
generated subgroup necessarily finite?", "give an algorithm which…").  For those, what is stated is
the concrete claim that the author's solution establishes — the example works, the answer is no, the
criterion of the solution is correct and decidable — and the choice is recorded in the docstring and
in `EXERCISES.md`.  No exercise was left out.

No numbered result of the main text was changed.  The Mealy machine of a dfa, which the solution to
`exer:regular-complete-mealy` uses, is reused from `PartC/FOMealy.lean` rather than restated.  The
whole project builds (`lake build`, no errors), the exercise file contains no `sorry`, and each of
the fifteen exercise declarations depends only on `propext`, `Classical.choice`, `Quot.sound`.

# Summary of changes for run c706a37d-d15c-4e09-a55b-368490936c99
I reorganised the Lean sources into a directory per part of the book, without changing any definition, statement or proof.

**New layout** (`RequestProject.lean` at the top imports everything):

```
RequestProject/
  Common.lean   Common/   -- Basic.lean, Aux.lean, RegularAux.lean
  PartA.lean    PartA/    -- MealyBasic, PrimeClosure, MapLift, FlipFlopClosure,
                          --  StateTrans, StateTransAperiodic, Statements
  PartB.lean    PartB/    -- LabAut, Atomize, OutLang, EpsElim, RatComp, RatCont,
                          --  HomComplement, MealyChar, Typing, LenNormalForm,
                          --  SeqChar, RationalStatements, WeightedStatements
  PartC.lean    PartC/    -- Statements, MSO
  PartD.lean    PartD/    -- Statements
  Main.lean               -- global options used by the project
```

Details:
- Each part has a roll-up file of the same name as its directory, importing that directory's contents; `RequestProject.lean` imports all parts, so `import RequestProject` now pulls in the whole development.
- Inside a part, the definitions and the statements of the numbered results live in `Statements.lean` (Part B, which has two statement files, uses `RationalStatements.lean` for Sections B.1–B.2 and `WeightedStatements.lean` for Sections B.3–B.4); the other files hold the constructions used in their proofs. The former `PartA.lean`, `PartB1.lean`, `PartB2.lean`, `PartC.lean`, `PartD.lean` became these statement files.
- Files shared across parts (the basic notions, the list/iteration lemmas, and the auxiliary regular-language facts) moved to `Common/`; `Common/RegularAux.lean` no longer depends on Part A, and the two Part B files that relied on that indirect dependency now import Mealy machines directly.
- All `import` lines and all file-path references in the file headers were updated accordingly; the lakefile glob was extended so the new root module is built as well.
- `THEOREMS.md` now has a "Layout" section describing the structure, and its file table was updated to the new paths; `README.md` summarises the structure too. The theorem index itself (names and statuses) is unchanged, and `ARISTOTLE_SUMMARY.md` was left untouched.

Verified with a full `lake build`: the build completes successfully, and the only warnings are the pre-existing `declaration uses 'sorry'` ones for the results that were already unproved (plus a few pre-existing linter hints). Everything is committed and pushed. Note that file names mentioned in the older parts of `ARISTOTLE_SUMMARY.md` refer to the previous flat layout.

# Summary of changes for run 7440d7c0-eda0-4913-a593-ba4ea19702b3
**Status of Part B (rational relations and rational functions)**

I re-checked the project as it now stands: the whole thing builds, and I verified each Part B result by tracing the axioms it actually depends on (not just by looking for `sorry` in the statement's own file). Of the 22 numbered Part B results that were formalised as statements, **2 are now proved outright** and the other 20 still rest on at least one `sorry` somewhere in their dependencies. Substantial supporting machinery has been built for several of the remaining ones.

**Proved with no `sorry` and no extra axioms** (only `propext`, `Classical.choice`, `Quot.sound`):
* **Theorem B.4.1** — characterisation of Mealy machines (`Transducers.isMealy_iff`, supporting file `RequestProject/MealyChar.lean`).
* **Claim B.4.4** — length preservation via typings (`Transducers.lengthPreserving_iff_typing`, supporting file `RequestProject/Typing.lean`).

**Reduced to a small number of remaining gaps** (statement and reduction complete; the named auxiliary steps are still `sorry`):
* **Theorem B.2.7** (Mealy machines inside the rational functions) — the full argument is written in `RequestProject/PartB1.lean` from Theorem B.4.1; the only thing missing is the step "rational ⇒ continuous", i.e. Theorem B.1.5 specialised to functions.
* **Theorem B.1.4** (closure under composition, `RequestProject/RatComp.lean`) — the product automaton is defined, its transition set is shown finite and the soundness direction is proved; the completeness direction (every pair of runs is matched by a run of the product) remains.
* **Theorem B.1.5** (continuity, `RequestProject/RatCont.lean`) — the translation of an atomic nfa with output into an ε-nfa is defined and the two directions of the run correspondence are proved; what remains is the language identity for that ε-nfa, regularity of ε-nfa languages, and the assembly.
* **Claim B.1.7** (complement of a homomorphism, `RequestProject/HomComplement.lean`) — the explicit 4-state automaton is defined and the basic reachability lemmas are proved; soundness and completeness remain.
* Atomisation of nfas with output (`RequestProject/Atomize.lean`, an auxiliary normal form used by B.1.4/B.1.5/B.2.4) — the construction and its main chaining lemma are proved; soundness and completeness remain.
* **Theorem B.4.6** (sequential functions, `RequestProject/SeqChar.lean`) — the intended proof is laid out in full: regularity of the length-mod and suffix languages, sequential transducers and their composition with a dfa, the derivative/state construction and the transducer built from it. Most of these steps are still `sorry`, so this file is currently a skeleton rather than a proof.

**Still statements only** (no proof work yet): B.1.6, B.2.3, B.2.4, B.2.5, B.2.6, B.3.3–B.3.7, B.4.2, B.4.3, B.4.5, B.4.8, B.4.13. As before, Claims B.4.9–B.4.12 are deliberately not formalised (they are internal steps of the proof of B.4.8).

For context: Part A remains proved in full, and Parts C and D are still statements only. No files were changed in this session — I only inspected and verified the current state, and the repository is committed and up to date.


# Summary of changes for run 6cd41a55-956b-4b84-bd16-32e830e07542
I continued the induction step of Lemma A.2.5 — no help was needed, and it is now complete, together with the two results that depended on it. Part A of the book is now proved in full, with no `sorry` and no extra axioms (only `propext`, `Classical.choice`, `Quot.sound`).

**Lemma A.2.5** (`Transducers.stateTransTransducer_prime_decomposition` in the new file `RequestProject/StateTrans.lean`): for every pre-automaton, the state transformation transducer is a composition of prime Mealy machines.

The proof follows the book, with one deviation that keeps the input alphabet fixed: instead of deleting the letter `a` from the alphabet, the pre-automaton in which `a` acts as the identity is used, so the two induction parameters are the number of states and the number of letters that do not act as a permutation, ordered lexicographically. The induction step is organised as a chain of stages, each adding one component to an enriched letter `(letter, seen, L, prev, fp, mid)`:

* `L` — the state transformation of the maximal `a`-free suffix of the current prefix, obtained from the map lifting (Lemma A.2.4) of the induction hypothesis for the pre-automaton where `a` acts as the identity;
* `seen`, `prev`, `fp` — flip-flop machines: whether `a` has occurred before, the delayed value of `L`, and the value stored at the first `a`-position (the first part of the tripartite decomposition);
* `mid` — the middle part, computed by the induction hypothesis for the smaller state space `P` (the image of the state transformation of `a`);
* a final letter-to-letter homomorphism recombines the three parts of the tripartite decomposition.

Correctness of the chain (`krStages_eq`) is proved against a specification machine, stage by stage; that the chain consists of primes is `krStages_compClosure`. Theorem A.2.2 (Krohn–Rhodes) was already reduced to Lemma A.2.5, so it is now proved outright.

**Theorem A.2.8** (`Transducers.aperiodic_iff_flipflop_composition`), whose remaining implication "aperiodic ⇒ composition of flip-flops" also depended on this construction, is now proved as well. This needed two additions:

* `RequestProject/FlipFlopClosure.lean` — the flip-flop analogues of the closure properties of compositions of primes (pairing the output with the input, acting on the second component, and the map lifting).
* `RequestProject/StateTransAperiodic.lean` — the same construction run inside the class of flip-flops. To make the book's remark that "every new machine only uses state transformations that arise from the original machine" precise, the middle pre-automaton is defined to apply only *realisable* transformations (those of the form `strTrans δ w`); this restriction is invisible in the correctness proof, and it is what makes condition (*) of Lemma A.2.11 inherited by both smaller pre-automata. In the induction basis, a pre-automaton that satisfies (*) and all of whose letters are permutations has only identity letters, so its state transformation transducer is a flip-flop.

Also updated: `RequestProject/PartA.lean` now imports the new files (the duplicated definitions were removed from it), and `THEOREMS.md` records the new status — Part A proved in full, Parts B, C, D still statements only.

# Summary of changes for run 68198e05-8a1a-4840-9a79-f65e77faeb5e
**Status: Part A is proved except for one remaining gap.**

Of the 11 numbered results of Part A (Mealy machines), 10 are now proved in Lean with no `sorry` and no extra axioms (only `propext`, `Classical.choice`, `Quot.sound`). What is left is a single item:

* **the induction step of Lemma A.2.5** (the state transformation transducer of a pre-automaton is a composition of primes). Its induction basis — the case where every letter acts as a permutation — is proved (`stateTransTransducer_prime_of_reversible`); the remaining step is the book's tripartite decomposition of the input into `a`-blocks.
* Two further statements are reduced to that gap: **Theorem A.2.2 (Krohn–Rhodes)** is proved *from* Lemma A.2.5 (the reduction itself is complete), and of **Theorem A.2.8** the implication "composition of flip-flops ⇒ aperiodic" is proved while the converse, which the book also derives from the Krohn–Rhodes construction, is left open.

So there are exactly two `sorry`s left in Part A (`RequestProject/PartA.lean`): the induction step of Lemma A.2.5 and the forward implication of Theorem A.2.8. Parts B, C, D remain statements only, as before.

**Proved in this session**

* A.1.2 (equivalence of Mealy machines is settled by inputs of bounded length), A.1.3 (closure under composition), A.1.4 (continuity), A.2.4 (map lifting of a decomposition into primes), A.2.6 (reversible machines compose), A.2.9 (pumping characterisation of aperiodicity), A.2.10 (Myhill–Nerode, both directions, via an explicit minimal machine), A.2.11 (aperiodic ⟺ the state transformations stabilise).

**New supporting files**

* `RequestProject/Aux.lean` — list and finite-iteration lemmas.
* `RequestProject/MealyBasic.lean` — Mealy definitions moved out of `PartA.lean`, plus runs, state transformations, the product machine and the dfa reading a machine's output.
* `RequestProject/PrimeClosure.lean` — a decomposition into primes can carry a copy of the input in its output (`compClosure_zipInput`, `compClosure_liftSnd`).
* `RequestProject/MapLift.lean` — the map lifting described position by position, its compatibility with composition, and Lemma A.2.4 (including the reversible case with the cancellation law, realised as a reversible machine, a flip-flop machine and a homomorphism).

**Two corrections to earlier definitions** (documented in the docstrings and in `THEOREMS.md`): `Aperiodic` now says the last letter of `f (u vⁿ w)` is eventually constant as an element of `Option B` (the earlier version was unsatisfiable for letter-to-letter functions), and the derivative used in Myhill–Nerode drops the output produced while reading `w` (otherwise even the identity would have infinitely many derivatives and Lemma A.2.10 would be false).

`THEOREMS.md` now carries a status column for every Part A result. The whole project builds; all work is committed and pushed.

# Summary of changes for run f0cde0fd-974e-4487-bd04-6c7b0abe48bd
I read the uploaded book (`main.pdf`, *Transducers* by M. Bojańczyk) and produced a Lean 4 formalisation of its numbered results — statements only, with every proof left as `sorry`, as requested (theorems, lemmas, corollaries and claims; exercises and examples excluded).

**What was added**

- `RequestProject/Basic.lean` — shared notions: continuity (Definition .0.1, plus partial and relational variants), prefix/length preservation, aperiodicity, the map lifting (Definition A.2.3), left distance (Definition B.4.7), aperiodic transition functions, and `CompClosure`, the closure of a family of functions under composition (used for all "decomposition into primes" results).
- `RequestProject/PartA.lean` — Mealy machines, reversible/flip-flop primes, and Theorems A.1.2–A.1.4, A.2.2 (Krohn–Rhodes), A.2.8, Lemmas A.2.4–A.2.6, A.2.10, A.2.11, Claim A.2.9.
- `RequestProject/PartB1.lean` — nfa with output, rational relations and functions, bimachines; Theorems B.1.4–B.1.6, B.2.3, B.2.6, B.2.7, Lemmas B.2.4, B.2.5, Claim B.1.7.
- `RequestProject/PartB2.lean` — weighted automata over a semiring; Theorems B.3.3, B.3.4, B.3.6, B.3.7, B.4.1, B.4.2, B.4.6, B.4.8, B.4.13, Lemmas B.3.5, B.4.3, B.4.5, Claim B.4.4, plus sequential and subsequential transducers.
- `RequestProject/PartC.lean` — regular functions (Definition C.0.14), two-way transducers, streaming string transducers; Theorems C.1.1, C.1.4, C.2.2, C.2.5, C.2.9, C.3.2, Corollaries C.2.7, C.2.8, Lemmas C.1.2, C.1.3, C.2.6, C.2.10, Claim C.2.11.
- `RequestProject/MSO.lean` — monadic second-order logic over strings (syntax, semantics, first-order fragment, quantifier rank), mso relabellings, mso transductions, k-types; Theorems C.4.1, C.4.4, C.4.8, C.4.11, C.4.16, C.4.17, Lemmas C.4.2, C.4.10, C.4.13, C.4.15, Claim C.4.6.
- `RequestProject/PartD.lean` — polyregular functions and marked squaring, for-transducers (syntax and semantics) and pebble transducers; Theorems D.0.19, D.1.1, D.2.1, D.2.4, Lemmas D.1.3, D.1.4.
- `THEOREMS.md` — an index mapping every numbered result of the book to its Lean name, together with the conventions used.

**Conventions and choices** (also documented in the files): strings are `List A` and regularity is Mathlib's `Language.IsRegular`; "problem X is decidable" is stated as the existence of a computable decision procedure on finite descriptions under an explicit promise (`DecidableUnderPromise`), undecidability as `¬ ComputablePred`, and Theorem A.1.2 in the equivalent form of a finite check on inputs of bounded length; the book's extended mso syntax with polynomial types is presented equivalently by families of ordinary mso formulas indexed by the variants of the linear type.

A small number of statements are deliberately not formalised, and each file says so in its header: the internal claims B.4.9–B.4.12, C.2.3, C.2.4, C.2.12, C.4.5, C.4.9, C.4.14, D.2.2, D.2.3, D.2.5–D.2.7, which talk about auxiliary encodings (configuration graphs, branching parts) used only inside the corresponding proofs.

The whole project builds; the only warnings are the expected `declaration uses 'sorry'` for the 64 statements. I also checked the definitions computationally on small examples (Mealy machines, bimachines, sst, two-way and pebble transducers, for-transducers, map lifting, marked squaring) to confirm they behave as the book describes. All work is committed and pushed.
# Summary of changes for Lemma `lem:for-closed-under-composition` (Part D)

Lemma `lemma:prenex-normal-form` (`Transducers.forTransducer_prenex`) was already proved, in
`RequestProject/PartD/ForPrenexTop.lean`, and is left unchanged.  Lemma
`lem:for-closed-under-composition` (`Transducers.forTransducer_comp`) is now proved as well, so
`RequestProject/PartD/Statements.lean` contains three `sorry`s instead of four, and
`RequestProject/Labels.lean` records the new status with `assert_no_sorry`.

The proof of the composition follows the book: the inner for-transducer is put into the form of a
single nest of loops (`Transducers.for_nest_form`), a position of its output is represented by the
tuple of positions at which the nest produces the corresponding letter, and the outer
for-transducer is translated over those tuples (`Transducers.tr`, whose correctness
`Transducers.tr_spec` was already proved).  What this run added is:

* `RequestProject/PartD/ForFree.lean` -- the free position variables of a program
  (`Transducers.ForProg.freePos`) and the transformation `Transducers.closeProg` making a program
  closed: every free position variable is bound by an extra loop that runs only at the first
  position of the input, and the empty input is dealt with by a constant program.  This is what
  makes the translation applicable at the top level: only a *bound* position variable of the outer
  program can be represented by a tuple of positions of the inner input.
* The hypotheses of `Transducers.tr_spec` were correspondingly weakened from all the position
  variables of the translated program to its free ones, which is what the induction actually
  needs.
* `RequestProject/PartD/ForCompTop.lean` -- the assembly.  The composed program first computes two
  flags saying whether the input has at least one and at least two letters
  (`Transducers.lenProg`).  On the inputs of length at least two it runs the translation; on the
  inputs of length at most one, where a nest of loops is of no use, it runs the loop-free
  simulation `Transducers.shortSim` of the inner transducer in continuation-passing style
  (`Transducers.cpsFree`), replacing each of its finitely many possible outputs `v` by the constant
  string that the outer transducer produces on `v`.

`lake build` succeeds with no errors, and `#print axioms` on `Transducers.forTransducer_prenex` and
on `Transducers.forTransducer_comp` reports only `propext`, `Classical.choice`, `Quot.sound`.
# Summary of changes for Theorem `thm:pebble-are-for` (Part D)

Theorem `thm:pebble-are-for` (`Transducers.pebble_iff_forTransducer`) -- pebble transducers and
for-transducers compute the same string-to-string functions -- is now proved.  It was the last
numbered result of the book left open, so `RequestProject/PartD/Statements.lean` no longer
contains a `sorry`, no file of the project does, and every alias of `RequestProject/Labels.lean`
carries `assert_no_sorry`.

From a for-transducer to a pebble transducer, the program is put in prenex form and the nest of
loops is run with one pebble per loop; that direction was already in the project
(`Transducers.PebFor.isPebbleTransducer_of_isForTransducer`).  The other direction is proved by
showing that a pebble transducer computes a polyregular function
(`Transducers.isPolyregular_of_isPebbleTransducer`), which is a for-transducer by Theorem
`thm:for-transducers-are-polyregular`.  The book obtains it from the reachability analysis of a
pebble automaton (Lemma `lem:reachability-pebble-automaton` and the claims inside its proof, which
are internal steps and are not formalised); here it is proved by induction on the number of
pebbles, which uses the same idea -- the run above the bottom pebble is a run of a machine with
one pebble fewer -- but keeps it inside the vocabulary of pebble transducers.  What this run
added is:

* `RequestProject/PartD/TwoWayTotal.lean` and `RequestProject/PartD/PebbleTwoWay.lean` -- the base
  case: a one-pebble transducer is a two-way transducer, so it computes a regular function on the
  inputs on which it halts (`Transducers.PebOne.exists_regularFun_of_pebble_one`).
* `RequestProject/PartD/SqPad.lean` -- the padded input (a blank on each side), its letters and
  its polyregularity, and the coordinates of the marked square of a string.
* `RequestProject/PartD/PebbleSquareIdx.lean`, `PebbleSquareDef.lean`, `PebbleSquareRun.lean`,
  `PebbleSquareSim.lean` -- the induction step: a `(k+2)`-pebble transducer on `w` is simulated by
  a `(k+1)`-pebble transducer on the marked square of the padded input
  (`Transducers.PebSq.sim_computes`).  A stack `[p_1, ..., p_l]` is encoded inside the block
  `p_1` of the square, so the bottom pebble is remembered by the block and one pebble is saved;
  the two letters adjacent to it are kept in the state, and the auxiliary phases of the
  simulating machine walk its topmost pebble to the gap that the encoding requires, using three
  tests that a pebble transducer can perform on the square (is the gap the marked one of its
  block, is it the start of a block, does it carry a lower pebble).
* `RequestProject/PartD/PebblePoly.lean` -- the induction itself, and the conclusion that a
  pebble transducer computes a polyregular function, marked squaring and padding being
  polyregular.

`lake build` succeeds with no errors (8321 jobs), and `#print axioms` on
`Transducers.pebble_iff_forTransducer`, on `Transducers.isPolyregular_of_isPebbleTransducer` and
on `Transducers.PebSq.sim_computes` reports only `propext`, `Classical.choice`, `Quot.sound`.

## The remaining exercises of the book

This pass closed the gap between the `\exer` entries of the sources and the
index of `EXERCISES.md`.  No numbered result of the main text was touched: the
only files changed outside `RequestProject/Exercises/` are
`RequestProject/Exercises.lean`, `RequestProject/Labels.lean`, `EXERCISES.md`
and `THEOREMS.md`.

Newly formalised:

* `exer:so-logic` (`Exercises/LogicEx.lean`) -- a language definable in
  second-order logic and not regular, for the syntax the solution uses.
* `exer:polyregular-marked-squaring-compression` (`Exercises/Compression.lean`)
  -- the purely combinatorial statement the solution establishes: `a^(2^n)` has
  a compression with `n+1` rules and every compression of its marked square has
  at least `2^n - 1` rules.
* `exer:2nft`, both halves (`Exercises/TwoNFT.lean`, `Exercises/TwoNFT2.lean`)
  -- the two nondeterministic two-way models are incomparable
  (`Transducers.Exercises.exists_isTwoNFT₁_not_isTwoNFT₂` and
  `Transducers.Exercises.exists_isTwoNFT₂_not_isTwoNFT₁`).
* `exer:for-transducers-simulate-fo` (`Exercises/ForFO.lean`) -- every
  first-order sentence is decided by a for-transducer of size linear in the
  size of the sentence (`Transducers.Exercises.exists_forProg_of_isFO`).

Fifty-eight of the book's eighty-three exercises are now formalised.  The
twenty-five that are not are listed in `EXERCISES.md`, each with the reason;
they are the ones about running time or the number of states of a construction,
the ones resting on theory the project does not have (the maximum cycle mean of
a weighted graph, Ehrenfeucht-Fraisse games, the growth rates of regular
languages), the ones going through the string encoding of the configuration
graph of a two-way transducer, `exer:factoring-through-a-rational-function`
(whose solution is empty in the sources) and the exercise at
`rational-functions.tex` line 440 (commented out in the sources).
`EXERCISES.md` also records a divergence in the solution to
`exer:2dfa-complexity`: the prime-divisibility construction it proposes gives a
superpolynomial, not an exponential, lower bound on the length of the shortest
accepted string in terms of the number of states.

`lake build` succeeds with no errors, there is no `sorry` in
`RequestProject/Exercises/`, and `#print axioms` on each new declaration
reports only `propext`, `Classical.choice`, `Quot.sound`.
