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
    NFAUnambig.lean             -- unambiguity of an nfa is decidable
    RatInjective.lean           -- injectivity of a rational function
    KrohnRhodes.lean            -- further exercises of krohn-rhodes.tex
    MyhillNerode.lean           -- the exercises of myhill-nerode.tex
    RegularPrimes.lean          -- further exercises of regular-primes.tex
    TwoDFAEx.lean               -- the exercises of 2dfa.tex
    TwoDFALoop.lean             -- loop elimination for two-way transducers
    TwoDFAPass.lean             -- a two-way automaton that performs a sequence of one-way passes
    TwoDFARuler.lean            -- the ruler word and the conditions that characterise it
    TwoDFAExp.lean              -- an exponentially long shortest accepted string
    TwoDFASipser*.lean          -- the polynomial-size two-way automaton for loop elimination
    SSTAux.lean                 -- the auxiliary facts of the sst exercises
    SST.lean                    -- the exercises of sst.tex
    SSTPoly.lean                -- copyful ssts and polynomial automata
    LogicEx.lean                -- second-order logic (logic.tex)
    Compression.lean            -- grammar compression (polyregular-intro.tex)
    CompressionSLP.lean         -- combining grammar compressions
    CompressionRat.lean         -- the rational case of compatibility with compression
    CompressionMapLift.lean     -- compatibility with compression is preserved by map lifting
    CompressionReg.lean         -- regular functions are compatible with compression
    TwoNFT.lean                 -- the two nondeterministic two-way models, first half
    TwoNFT2.lean                -- the two nondeterministic two-way models, second half
    ForFO.lean                  -- first-order logic into for-transducers (polyregular-for.tex)
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
| `Exercises/TwoDFAPass.lean` | a two-way deterministic automaton that performs a fixed sequence of left-to-right passes, one one-way automaton after another, rewinding between two passes: the transition function, the count of its states (the *sum* of the numbers of states of the passes, plus one rewinding state per pass) and the characterisation of its language as the non-empty inputs on which every pass accepts |
| `Exercises/TwoDFARuler.lean` | the combinatorial core of `exer:2dfa-complexity`: the ruler word `rul 0 n` (`0 1 0 2 0 1 0` for `n = 2`, of length `2^(n+1)-1`), the `n+1` alternation conditions `Cond j`, the fact that the ruler word is the unique word over `{0,…,n}` satisfying all of them, and the three-state one-way automaton that checks one condition |
| `Exercises/TwoDFAExp.lean` | the exercise `exer:2dfa-complexity` itself: the two-way automaton with `4*(n+1)` states whose language is the singleton of the ruler word, so that its shortest accepted string has length `2^(n+1)-1` |
| `Exercises/TwoDFASipserDef.lean`, `TwoDFASipserRun.lean`, `TwoDFASipserTree.lean`, `TwoDFASipserExplore.lean`, `TwoDFASipserScan.lean`, `TwoDFASipserSound.lean`, `TwoDFASipser.lean` | the polynomial-size two-way automaton of `exer:2dfa-loop-elimination-sipser`: the depth-first search, performed by a two-way automaton, of the tree of the configurations that reach the accepting configuration — its definition and macro steps, the tree, the termination of the exploration and the discovery of the initial configuration, the sweep over the root candidates, the soundness invariant, and the exercise |
| `Exercises/SSTAux.lean` | the auxiliary facts the sst exercises take for granted |
| `Exercises/SST.lean` | the exercises of `sst.tex`: sorting by an sst, the continuity of the functions of copyful ssts, the exponential bound on their output length and its attainment, the failure of closure under composition, and the two polynomial automata (single and doubly exponential) |
| `Exercises/SSTPoly.lean` | the reduction of equivalence of copyful ssts to equivalence of polynomial automata |
| `Exercises/LogicEx.lean` | the exercise of `logic.tex` on second-order logic: the fragment `SO` of second-order logic used by the solution (first-order logic with variables for binary relations on positions), its satisfaction relation and its languages, and a sentence of `SO` whose language `{falseⁿ trueⁿ}` is not regular |
| `Exercises/Compression.lean` | grammar compression in binary (straight-line programme) form, and the exercise of `polyregular-intro.tex` on marked squaring: the set of distances between consecutive marked letters, the bound on it by the number of rules of a compression, and the resulting exponential gap between a compression of `a^(2ⁿ)` and any compression of its marked square |
| `Exercises/CompressionSLP.lean` | the operations on grammar compressions that the two compression exercises build with: relocating a compression inside a longer list of rules, concatenating two compressions, a compression of linear size for a fixed string, and the concatenation of a list of compressions at the cost of one extra rule per piece |
| `Exercises/CompressionRat.lean` | the rational case: the output of a bimachine at the gaps of a factor, its compositionality, and the resulting compression of linear size for the image of a compressed string under a rational function |
| `Exercises/CompressionMapLift.lean` | Claim `claim:map-compression`: the first and last blocks of a string over the extended alphabet and the part of the image strictly between them, their compositionality, and the two-pass construction of a compression for the image under a map lifting |
| `Exercises/CompressionReg.lean` | the exercise `exer:regular-compression`: compatibility with compression in the size sense, its closure under composition, the two easy prime functions (reverse and duplicate), and the induction over the composition tree of a regular function |
| `Exercises/TwoNFT.lean` | the first half of the exercise of `2dfa.tex` on the two nondeterministic two-way models: the two models `IsTwoNFT₁` and `IsTwoNFT₂`, the finiteness of the set of outputs of the second one, and a relation of the first one with infinitely many outputs on one input |
| `Exercises/TwoNFT2.lean` | the second half of that exercise: the relation `{(aⁿ, v v)}` is in the second model (through the two-way transducer for the map lifting of duplication) and not in the first (the cut-and-paste argument, with the cut lemma `TwoWayN.reachesN_cut` that replaces the solution's cut after exactly `n` output letters) |
| `Exercises/ForFO.lean` | the exercise of `polyregular-for.tex` on simulating first-order logic: the translation `trans` of a formula into a for-transducer program that stores the truth value of every subformula in a Boolean variable, its correctness `trans_spec`, and the linear bound `10·|φ|+5` on the size of the resulting program |
| `Exercises/PartBCUnary.lean` | bimachines over a one-letter input alphabet, used by the solution to `exer:rational-one-letter-input`: the eventual periodicity of the runs of the prefix and of the suffix automaton, the output of the bimachine as the concatenation of the pieces of its gaps, and the resulting form `x yᵏ z` of the output on the inputs of a fixed length modulo the period |
| `Exercises/NFAUnambig.lean` | unambiguity of an nfa, for Exercise `exer:decide-unambiguous`: runs of an nfa and the fact that its language is the set of inputs with an accepting run, the product automaton of the solution, the criterion for ambiguity, the decision procedure, and the auxiliary fact that reachability in a finite graph is decidable |
| `Exercises/RatInjective.lean` | the first step of the solution to `exer:rational-injectivity-decidable`: a rational function is injective exactly when it has a rational left inverse, together with the auxiliary facts it needs — the closure of the rational relations under union, by the disjoint union of two nfas with output, and the rationality of the relation that maps every string of a regular language to the empty string |

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
| Exercise `exer:simple-decomposition-example` (the first-letter function as a composition of flip-flops) | `Transducers.firstConst_flipflop_decomposition` | proved |
| Exercise `exer:simple-decomposition-example-2` (the first-letter function is not a composition of reversible Mealy machines) | `Transducers.firstConst_not_reversible_composition` | proved |

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
| Exercise `exer:decide-unambiguous` (unambiguity of an nfa is decidable) | `ambiguous_iff_reach`, `decidableUnambiguousNFA` (with `RunFrom`, `AccRun`, `Ambiguous`, `UnambiguousNFA`, `prodStep`) | proved |
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
| Exercise `exer:rational-injectivity-decidable` (injectivity is decidable) | `rationalFun_injective_iff_exists_inverse`, `exists_rationalFun_inverse_of_injective` (the criterion of the solution only) | the decision procedure is not formalised (see below) |
| Exercise `exer:rational-composition-finiteness-undecidable` (finiteness of the iterates is undecidable) | — | not formalised |
| Exercise `exer:rational-compression` (rational functions are compatible with compression) | `compatCompression_of_isRationalFun` (with `CompatCompression`, `bimGaps`, `exists_slp_of_bimachine`) | proved in the size sense of `CompatCompression` (polynomial time is not modelled; see the divergence below) |

### Regular functions (`regular-primes.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:two-letter-alphabet-suffices` (a two-letter alphabet suffices for map reverse and map duplicate) | `RegularFam2`, `isRegularFun_iff_compClosure2` | proved |
| Exercise `exer:not-semiring-continuous` (a regular function that is not obtained by precomposing a weighted function) | `exists_isRegularFun_not_weighted_precomp` | proved |

### Machine independent characterisations (`myhill-nerode.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:minimal-sequential` (minimal sequential transducers are unique up to isomorphism) | `minimal_sequential_unique` (with `residOf`, `canonSeq`, `MinimalFor`, `SeqIso`) | proved |
| Exercise `exer:minimal-subsequential` (minimal subsequential transducers are not unique) | `minimal_subsequential_not_unique` | proved |
| Exercise `exer:non-minimal-bimachine` (minimal bimachines are not unique) | `minimal_bimachine_not_unique` | proved |
| Exercise `exer:minimal-bimachine-lexicographic` (the lexicographically least minimal bimachine) | — | not formalised |
| Exercise `exer:non-minimal-automaton` (a rational function with two non-isomorphic minimal unambiguous transducers) | — | not formalised |

### Regular functions, introduction (`regular-intro.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:regular-compression` (regular functions are compatible with compression) | `compatCompression_of_isRegularFun` (with `CompatCompression.mapLift` for Claim `claim:map-compression`, `compatCompression_reverse`, `compatCompression_dup`) | proved in the size sense of `CompatCompression` (polynomial time is not modelled; see the divergence below) |

### Two-way transducers (`2dfa.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:2dfa-unary-output` (over a unary output alphabet, regular = rational) | `isRegularFun_iff_isRationalFun_of_unary_output` | proved |
| Exercise `exer:2dfa-boolean` (two-way deterministic languages are closed under Boolean combinations) | `isTwoDFALang_boolean` | proved |
| Exercise `exer:2dfa-complexity` (the shortest accepted string can be exponential in the number of states) | `exists_twoDFA_shortest_exponential` (with `rulerAut`, `rulerAut_accepts`, `card_rulerSt`, `rulWord`; the author's own construction, and the bound it really gives, are `divAut`, `divAut_accepts`, `card_divSt`, `divAut_shortest`, `divAut_shortest_le`) | proved, but *not* by the author's construction, which does not prove the claim; see the divergence below |
| Exercise `exer:2dfa-loop-elimination` (the inputs on which a two-way transducer terminates form a regular language) | `halts_isRegular` | proved |
| Exercise `exer:2dfa-loop-elimination-sipser` (a polynomial-size two-way automaton for it) | `exists_terminating_twoDFA_halts` (with `dfsAut`, `dfsAut_accepts`, `dfsAut_terminates`, `exists_terminating_twoDFA`) | proved |
| Exercise `exer:regular-outpus-of-exactly-linear-size` (a regular function of unbounded output size has exactly linear output size) | — | not formalised |
| Exercise `exer:2nft` (the two nondeterministic two-way models are incomparable) | `exists_isTwoNFT₁_not_isTwoNFT₂`, `exists_isTwoNFT₂_not_isTwoNFT₁` (with `TwoWayN`, `IsTwoNFT₁`, `IsTwoNFT₂`, `dupRel`) | proved |
| Exercise `exer:2nft-uniformise` (both nondeterministic models can be uniformised) | `exists_isRegularFun_uniformising_isTwoNFT₁`, `exists_isRegularFun_uniformising_isTwoNFT₂` | proved |

### Streaming string transducers (`sst.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:sst-sorting` (sorting the letters of a string is computed by an sst) | `isSST_sort` | proved |
| Exercise `exer:sst-copyful-sst` (copyful ssts compute continuous functions) | `continuous_of_isCopyfulSST` | proved |
| Exercise `exer:sst-copyful-sst-output-size` (the output of a copyful sst is at most exponential, and this is attained) | `CopyfulSST.output_length_exp_bound`, `exists_isCopyfulSST_exponential` | proved |
| Exercise `exer:sst-copyful-sst-no-composition` (copyful ssts are not closed under composition) | `exists_isCopyfulSST_comp_not_isCopyfulSST` | proved |
| Exercise `exer:sst-polynomial-automaton` (a polynomial automaton computing `2^n`) | `isPolyAut_two_pow` | proved |
| Exercise `exer:sst-polynomial-automaton-doubly-exponential` (a polynomial automaton computing `2^{2^n}`) | `isPolyAut_two_pow_two_pow` | proved |
| Exercise `exer:copyful-sst-decidable` (equivalence of copyful ssts reduces to equivalence of polynomial automata) | `copyfulSST_equivalence_reduces_to_polyAut` | proved |

### Logic (`logic.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:mealy-as-restricted-mso-relabelling` (Mealy machines are the restricted mso relabellings) | `RestrictedRelabelling`, `isMealy_iff_restrictedRelabelling` | proved |
| Exercise `exer:fo-non-elementary` (first-order sentences of non-elementary succinctness) | — | not formalised |
| Exercise `exer:so-logic` (second-order logic defines a non-regular language) | `exists_SO_lang_not_isRegular` (with `SO`, `SO.Sat`, `SO.lang`) | proved |
| Exercise `exer:fo-suc` (first-order logic with successor only is strictly weaker) | — | not formalised |

### Polyregular functions, introduction (`polyregular-intro.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:polyregular-marked-squaring-compression` (marked squaring is not compatible with compression) | `markedSquare_not_compatible_with_compression` (with `Rule`, `slpVal`, `Generates`) | proved |
| Exercise `exer:polyregular-unmarked-squaring` (unmarked squaring gives a strictly smaller class) | — | not formalised |

### For-transducers (`polyregular-for.tex`)

| Book | Lean | Status |
| --- | --- | --- |
| Exercise `exer:for-transducers-simulate-fo` (a first-order sentence is computed by a for-transducer of linear size) | `exists_forProg_of_isFO` (with `trans`, `fsize`, `progSize`, `foProg`) | proved |
| Exercise `exer:for-transducer-continuity-nonelementary` (the preimage nfa can be non-elementary) | — | not formalised |
| Exercise `exer:forward-for-transducer` (forward for-transducers = marked squaring and rational functions) | — | not formalised |

Every exercise of these chapters carries a `\label` in the sources, so every
formalised one is aliased in `RequestProject/Labels.lean`.

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
  functions: item (b) of
  `exer:decide-rational-colision`, `exer:decide-same-ideal`,
  `exer:rational-injectivity-decidable`,
  `exer:rational-composition-finiteness-undecidable`.  In this project such a
  statement is about *codes* of automata (`Transducers.RelCode`) and about
  `ComputablePred`, and the corresponding reductions are not carried out.  Of
  `exer:rational-injectivity-decidable` the *first* step of the solution, which
  is a mathematical statement, is nevertheless proved, in
  `Exercises/RatInjective.lean`: a rational function is injective exactly when
  it has a rational left inverse, obtained as the solution obtains it, by
  uniformising the inverse relation made total with a default output outside
  the range.  What is missing is the second step, the decision procedure:
  it applies Theorem `thm:equivalence-rational-functions` to the left inverse
  composed with the function, and that theorem is stated here for *codes* of
  automata, whereas the Uniformisation Lemma is available in this project only
  in the form `Transducers.exists_rationalFun_of_total_rel`, which asserts that
  a rational function exists and not that a code for one can be computed.  The
  exercise is therefore still counted as not formalised.
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

## Notes on the statements (the exercises of `logic.tex`, `polyregular-intro.tex`, `2dfa.tex` and `polyregular-for.tex`)

* **`exer:so-logic`.**  The exercise asks for a language that is definable in
  second-order logic and is not regular.  The book does not fix a syntax for
  second-order logic, so `Transducers.Exercises.SO` fixes the one the solution
  uses: first-order logic over strings extended with variables for *binary*
  relations on positions, which may be quantified over and tested for
  membership.  The language is the author's, `{falseⁿ trueⁿ}`; the sentence says
  that there is a relation which is a bijection between the positions labelled
  `false` and the positions labelled `true` and which is monotone, and its
  non-regularity is the pumping argument already in `Exercises/PartBCAux.lean`.
* **`exer:polyregular-marked-squaring-compression`.**  Polynomial time is not
  part of this formalisation, so what is proved is the stronger, purely
  combinatorial statement that the solution establishes: the input `a^(2ⁿ)` has
  a compression with `n+1` rules and *every* compression of its marked square
  has at least `2ⁿ-1` rules, so no algorithm at all can compute one in
  polynomial time.  A grammar generating a single string is taken in binary
  (straight-line programme) form, which is the form the solution argues about.
* **`exer:2nft`.**  Both halves are proved.  The second model is formalised with
  the correction the solution itself makes: the guessed labelling has to satisfy
  a regular condition, so that the model can produce no output at all.  For the
  first half the relation is the author's `bounce`, which on a nonempty input
  produces every string over a one-letter output alphabet.  For the second half
  the relation is the author's `{(aⁿ, v v) : |v| = n}`; the membership in the
  second model reuses the two-way transducer for the map lifting of duplication
  of `PartC/TwoWayRegular.lean`.  One point that the solution passes over had to
  be dealt with: a single transition may produce several output letters, so a
  run cannot be cut after *exactly* `n` output letters.  It is cut instead at the
  first moment when at least `n` letters have been produced, and the pigeonhole
  is applied to the configuration together with the at most `K` extra letters,
  where `K` is the length of the longest output of a transition; the splicing
  then goes through unchanged.
* **`exer:for-transducers-simulate-fo`.**  The outputs `yes` and `no` are `true`
  and `false` over the output alphabet `Bool`.  The size of a program is the
  number of nodes of its syntax tree (`progSize`) and the size of a formula is
  the number of nodes of its syntax tree (`fsize`); the bound proved is
  `10·fsize φ + 5`, which is linear, as the solution says.  The translation is
  the author's: each quantifier becomes a for loop, the truth value of each
  subformula is kept in a Boolean variable, and the epilogue outputs `yes` or
  `no`.  The satisfaction of the sentence is stated with the default valuation
  of the variables, on which it does not depend.

* **`exer:decide-unambiguous`.**  The exercise asks for a decision procedure, so,
  as for the two decidability exercises of Part A, both the criterion of the
  solution and the resulting `Decidable` instance are stated.  The automaton is
  Mathlib's `NFA`, whose transitions read exactly one letter, which is the
  ε-free form that the solution reduces to in its first sentence; a run is the
  list of the states it visits, and `mem_accepts_iff_exists_accRun` checks
  against Mathlib's semantics of an nfa that the language of the automaton is
  the set of inputs that have an accepting run.  Two accepting runs on the same
  input use different transitions somewhere exactly when they are distinct
  lists, since a transition is determined by its source, its letter and its
  target, so ambiguity is stated as the existence of two distinct accepting
  runs.  The polynomial running time claimed by the solution is not formalised:
  the project has no model of running time, and reachability in the product
  automaton is decided here by saturating the set of reachable states.

## A divergence: `exer:2dfa-complexity`

The exercise asks for a deterministic two-way automaton whose shortest accepted
string is *exponential* in the number of states, and the solution proposes to
check divisibility of the input length by each of the primes `p₁, …, pₙ`, using
about `p₁ + ⋯ + pₙ` states, so that the shortest accepted string has length
`p₁ ⋯ pₙ`.  That construction does not prove the claim.  For *distinct* primes
`p₁ < ⋯ < pₙ` — and repeated primes contribute nothing — the number of states is
`s = Θ(pₙ² / log pₙ)` while `log (p₁ ⋯ pₙ) = Θ(pₙ)`, so the shortest accepted
string has length `exp(Θ(√(s log s)))`.  That is superpolynomial in the number of
states, but it is not exponential in it.

The statement of the exercise is nevertheless true, by a construction that the
book does not give, so nothing here is a counterexample to the exercise: what is
recorded is that the argument of the solution establishes a superpolynomial and
not an exponential lower bound.  The author's construction is kept, in
`Exercises/TwoDFAComplexity.lean`, beside a construction that *does* prove the
claim, in `Exercises/TwoDFAExp.lean`.  That construction is the following.  Over
the alphabet `{0, 1, …, n}`, the *ruler word*

  `rul 0 0 = 0`,   `rul 0 (h+1) = rul 0 h · (h+1) · rul 0 h`,

so `rul 0 2 = 0 1 0 2 0 1 0`, has length `2^(n+1) - 1`, and it is the *unique*
word over that alphabet satisfying, for every level `j ≤ n`, the condition that
among the letters at least `j`, those equal to `j` and those larger than `j`
alternate, beginning and ending with `j`.  Each of these `n+1` conditions is
checked by a one-way automaton with three states, so a two-way automaton can
check all of them by performing the `n+1` passes one after another, rewinding
between two passes — this is exactly the sum-of-states intersection that the
author's solution appeals to, and it is `Exercises/TwoDFAPass.lean`.  The
resulting automaton has `4*(n+1)` states and its language is the singleton
`{rul 0 n}`, so its shortest accepted string has length `2^(n+1) - 1`,
exponential in its number of states.  The alphabet grows with `n`, which the
author's construction avoids; the measure of the exercise is the number of
states.

## Exercises that are not formalised (continued)

Besides the seven exercises of *Rational functions* already listed above, the
following are not formalised, and each is left out rather than replaced by a
statement the book does not make.

* Statements about polynomial time, which this project does not model:
  `exer:polyregular-unmarked-squaring` and
  `exer:for-transducer-continuity-nonelementary` (which rests on
  `exer:fo-non-elementary`).  Two further exercises of this kind,
  `exer:rational-compression` and `exer:regular-compression`, are now
  formalised in their *size* half — for a rational, resp. regular, `f` there are
  `C` and `k` such that every string with a compression of `n` rules has an
  image with a compression of at most `C·nᵏ` rules
  (`Transducers.Exercises.CompatCompression`) — exactly as
  `exer:polyregular-marked-squaring-compression` is; the algorithm that computes
  that compression in polynomial time is not formalised, only its output size.
  `exer:polyregular-unmarked-squaring` rests on the polynomial time half of
  those two, so it is still left out.
* Statements resting on theory that the project does not have:
  `exer:rational-outpus-of-exactly-linear-size` and
  `exer:rational-outpus-of-exactly-linear-size-rational-number` (the maximum
  cycle mean of a weighted graph), `exer:regular-outpus-of-exactly-linear-size`
  (which reduces to them through `exer:2dfa-unary-output`), `exer:fo-suc`
  (Ehrenfeucht–Fraïssé games) and `exer:fo-non-elementary`.
* Two exercises of `myhill-nerode.tex` whose solutions are long case analyses
  over arbitrary machines: `exer:minimal-bimachine-lexicographic` (a
  Myhill–Nerode theory for bimachines) and `exer:non-minimal-automaton` (the
  example is easy, but the claim that three states are necessary is a case
  analysis over all two-state unambiguous transducers with arbitrary output
  strings on the transitions, which the solution itself only sketches).
* The two exercises of `rational-functions.tex` that are commented out in the
  sources and so are not exercises of the book: the one at line 311 (when one
  rational function factors through another), whose statement is commented out
  and whose solution is empty, and the unlabelled one at line 440, whose
  statement and solution are both commented out.  Neither carries a number in
  `main.aux`, so neither is named here by a label.  (The content of the second —
  that a rational relation all of whose outputs have the length of the input is
  computed by an nfa with output whose transitions are length-preserving — is
  Lemma `lem:characterisation-length-preserving` of the main text, which is
  formalised in `RequestProject/PartB/LenNormalForm.lean`.)
* `exer:forward-for-transducer`, the last exercise of the book, which asks for
  the functions computed by *forward* for-transducers — those all of whose loops
  run first-to-last — to be exactly the composition closure of marked squaring
  and the *rational* functions.  Loop directions are modelled in this project
  (`Transducers.ForProg.loop` carries a `Bool`), but the solution asks for both
  inclusions of Theorem `thm:for-transducers-are-polyregular` to be replayed
  with the direction of every loop tracked, and this project's proof of that
  theorem does not have the shape the solution refines.  In particular the
  right-to-left inclusion goes through the enumeration of the tuples of
  positions followed by a *scan* which is shown regular because it is computed
  by a streaming string transducer (`Transducers.PolyEnum.scan_enum` and
  `isRegularFun_scanFun` in `RequestProject/PartD/PolyFor.lean`), whereas the
  exercise needs that scan to be *rational* in the forward case; and the
  left-to-right inclusion needs a forward bimachine program — the program of
  `RequestProject/PartD/ForPrimes.lean` runs the suffix automaton in a backward
  inner loop (`MProg.loop false`) — together with the fact that the composition
  construction of Lemma `lem:for-closed-under-composition` multiplies the
  directions.  Each of these is a development of the size of the theorem it
  refines, so the exercise is left out rather than stated in a weaker form that
  the book does not make.

## Status (current)

This section supersedes the counts of the two `## Status` sections above, which
were written when fewer chapters had been done.

**Sixty-three** exercises are formalised and **twenty** are not; the book has
eighty-three exercises, eighty-two of them with a solution.  The four added
last are `exer:2dfa-complexity`, `exer:2dfa-loop-elimination-sipser`,
`exer:regular-compression` and `exer:rational-compression`.  Every formalised
exercise carries a `\label` in the sources and has an alias in
`RequestProject/Labels.lean` followed by `assert_no_sorry`, and none of the
unformalised ones has an alias, which is what makes this index self-checking.
There is no `sorry` anywhere in `RequestProject/Exercises/`, and `#print axioms`
on each of the sixty-three reports only `propext`, `Classical.choice`,
`Quot.sound`.

Three of the sixty-three diverge from the literal statement of the exercise, and
each divergence is spelled out above and in the docstring of the Lean statement:
`exer:rational-compression` and `exer:regular-compression` are proved in their
size half only, polynomial time not being modelled by this project, and
`exer:2dfa-complexity` is proved by a construction that the book does not give,
the author's own construction not establishing the claim.

Three statements carry an explicit hypothesis rather than being proved outright:
`exer:function-that-is-not-rational` (the non-rationality of string reversal, an
*example* of the main text and not a numbered result),
`exer:rational-relations-intersection-undecidable` and item (a) of
`exer:decide-rational-colision` (the undecidability of the Post correspondence
problem, exactly as the numbered undecidability results of the book do).

## Status (closing audit)

This section is the final recount of the exercises; it supersedes the counts of
the `## Status` sections above, which were written when fewer chapters had been
done.  Nothing else in this file is changed by it: the index tables above are
correct and are what the recount is based on.

**The book has 81 exercises.**  The sources contain 83 `\exer` environments, but
two of them are commented out and carry no number in `main.aux`, so they are not
exercises of the book: the one at line 311 of `rational-functions.tex` (whose
solution is empty as well, so it is the one exercise-shaped environment with no
written solution) and the unlabelled one at line 440 of the same file.  Both were already
described under *Exercises that are not formalised (continued)*.  Every one of
the 81 has a written solution.

**Sixty-five are formalised and proved**, and **sixteen are not**.  Each of the
65 has an alias in `RequestProject/Labels.lean` followed by `assert_no_sorry`,
and none of the 16 has an alias, which is what makes this index self-checking.
There is no `sorry` anywhere in `RequestProject/Exercises/`, and `#print axioms`,
run in the closing audit on all 196 aliases of `RequestProject/Labels.lean` —
the 80 that belong to exercises included — reports only `propext`,
`Classical.choice`, `Quot.sound` for every one of them: no exercise that this
file calls proved depends on `sorryAx`.

### The sixteen exercises of the book that have a written solution and no formalisation

All sixteen have a solution written out in the book; the reason each is left out
is given in the two *Exercises that are not formalised* sections above, and is
summarised here so that the list can be read in one place.

| Exercise | chapter | why it is left out |
| --- | --- | --- |
| `exer:rational-outpus-of-exactly-linear-size` | `rational-functions.tex` | the maximum cycle mean of a weighted graph, which the project does not have |
| `exer:rational-outpus-of-exactly-linear-size-rational-number` | `rational-functions.tex` | same |
| `exer:regular-outpus-of-exactly-linear-size` | `2dfa.tex` | reduces to the two above through `exer:2dfa-unary-output` |
| `exer:full-ideal` | `rational-functions.tex` | the growth rates of regular languages, and the pattern analysis of `exer:polynomial-image-growth-decidable` |
| `exer:polynomial-ideals` | `rational-functions.tex` | same |
| `exer:all-ideals` | `rational-functions.tex` | same |
| `exer:decide-same-ideal` | `rational-functions.tex` | same, plus a decision procedure about codes of automata |
| `exer:rational-injectivity-decidable` | `rational-functions.tex` | the *first* step of the solution is proved (`Exercises/RatInjective.lean`); the decision procedure needs a *computable* form of the Uniformisation Lemma, which the project does not have |
| `exer:rational-composition-finiteness-undecidable` | `rational-functions.tex` | the undecidability reduction is not carried out for codes of automata |
| `exer:minimal-bimachine-lexicographic` | `myhill-nerode.tex` | a Myhill–Nerode theory for bimachines, which the project does not have |
| `exer:non-minimal-automaton` | `myhill-nerode.tex` | the hard half is a case analysis over all two-state unambiguous transducers that the solution itself only sketches |
| `exer:fo-non-elementary` | `logic.tex` | non-elementary succinctness of first-order sentences |
| `exer:fo-suc` | `logic.tex` | Ehrenfeucht–Fraïssé games, which the project does not have |
| `exer:polyregular-unmarked-squaring` | `polyregular-intro.tex` | rests on the polynomial *time* half of the two compression exercises, and running time is not modelled |
| `exer:for-transducer-continuity-nonelementary` | `polyregular-for.tex` | rests on `exer:fo-non-elementary` |
| `exer:forward-for-transducer` | `polyregular-for.tex` | asks for both inclusions of Theorem `thm:for-transducers-are-polyregular` to be replayed with the direction of every loop tracked; the project's proof of that theorem does not have the shape the solution refines |

Item (b) of `exer:decide-rational-colision` is left out for the same reason as
`exer:rational-composition-finiteness-undecidable`; item (a) is proved, from the
undecidability of the Post correspondence problem, so the exercise itself counts
among the 65.
