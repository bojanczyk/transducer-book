# exercises-encoding — COMPLETE

task: ad990dab-11f4-4cb2-ba4c-2cc67e716ebd
created: 2026-08-28 19:14:43.411875

All four exercises that the missing string encoding of the configuration graph had blocked are now formalised and proved, and the repository builds cleanly.

**Proved outright** (each checked with `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`):

* `exer:2dfa-unary-output` — `Transducers.Exercises.isRegularFun_iff_isRationalFun_of_unary_output` (`RequestProject/Exercises/TwoDFAUnary.lean`). Regular = rational over a unary output alphabet, the alphabet condition rendered as `Subsingleton B`. This one was already proved before this run; only the index prose was stale.
* `exer:2dfa-loop-elimination-sipser` — `Transducers.Exercises.exists_terminating_twoDFA_halts` (`RequestProject/Exercises/TwoDFASipser.lean`, on top of the `TwoDFASipser{Def,Run,Tree,Explore,Scan,Sound}` files). The book's solution: the configurations reaching the accepting configuration form a tree, explored by a depth-first search carried out by a two-way automaton of quadratic size.
* `exer:regular-compression` — `Transducers.Exercises.compatCompression_of_isRegularFun`, and the exercise it rests on, `exer:rational-compression` — `Transducers.Exercises.compatCompression_of_isRationalFun` (`RequestProject/Exercises/CompressionReg.lean`, with `CompressionSLP/Rat/MapLift`).
* `exer:2dfa-complexity` — `Transducers.Exercises.exists_twoDFA_shortest_exponential` (`RequestProject/Exercises/TwoDFAExp.lean`, with the new `TwoDFAPass.lean` and `TwoDFARuler.lean`): for every n a deterministic two-way automaton with `4·(n+1)` states whose shortest accepted string has length `2^(n+1)−1`.

**No result was proved from an added hypothesis in this run.**

**Divergences, all documented in the docstrings, `EXERCISES.md`, `THEOREMS.md` and `FORMALISATION.md`:**

* The note in `EXERCISES.md` about `exer:2dfa-complexity` still stands and has not been papered over: the author's construction (inputs whose length is divisible by the first n primes) yields only a superpolynomial, not exponential, lower bound. That construction is kept beside the exercise in `Exercises/TwoDFAComplexity.lean` with the discrepancy spelled out, and the exponential claim is proved instead by a construction the book does not give — the ruler word `0 1 0 2 0 1 0 …` over `{0,…,n}`, singled out by `n+1` alternation conditions, each checked by a three-state left-to-right pass.
* The two compression exercises are proved in their *size* half only (`CompatCompression`: the image of a string with a grammar compression of n rules has one of at most `C·nᵏ` rules). The book also asks for a polynomial-time algorithm; this project has no model of running time, the same convention already used for `exer:polyregular-marked-squaring-compression`.

**On the encoding itself:** the string representation of the configuration graph is a real object in the project (the alphabet `Transducers.CLet`, the representation `Transducers.TwoWay.enc`), and the results of the book about it are proved rather than restated — `RequestProject/Labels.lean` no longer lists any result as unformalised for that reason; the only remaining "not formalised" entry there is Definition `def:rational-recognisable-subsets`.

**Still unformalised (20 exercises), none of them blocked by the encoding any more:** `exer:full-ideal`, `exer:polynomial-ideals`, `exer:all-ideals`, `exer:decide-same-ideal`, `exer:rational-injectivity-decidable` (only the decision procedure), `exer:rational-composition-finiteness-undecidable`, `exer:minimal-bimachine-lexicographic`, `exer:non-minimal-automaton`, `exer:regular-outpus-of-exactly-linear-size`, `exer:rational-outpus-of-exactly-linear-size(-rational-number)`, `exer:fo-non-elementary`, `exer:fo-suc`, `exer:polyregular-unmarked-squaring`, `exer:for-transducer-continuity-nonelementary`, `exer:forward-for-transducer`, and two commented-out non-exercises in `rational-functions.tex`. Their obstacles are unmodelled polynomial time, missing theory (maximum cycle mean, Ehrenfeucht–Fraïssé games) or long case analyses; each has its reason recorded in `EXERCISES.md`.

**Bookkeeping.** `lake build` succeeds with no errors (8386 jobs) and there is no `sorry` in `RequestProject/Exercises/`; the only `sorry` occurrences in the project remain the pre-existing ones inside block comments. All four consistency scripts pass: `tools/gen_labels.py --check` (196 aliases), `tools/tex_numbering.py --check`, `tools/decl_files.py --check`, `tools/relabel.py`. `EXERCISES.md`, `THEOREMS.md` (file table, exercise section, axiom record) and `FORMALISATION.md` now read 63 exercises formalised / 20 not, and `ARISTOTLE_SUMMARY.md` records the run. Everything is committed and pushed.
