# What has been formalised, for a reader of the book

This note is addressed to someone who is reading *Transducers* (M. Bojańczyk)
and wants to know what the Lean development in this directory says about it: how
much of the book is machine-checked, what the formal statements mean, where they
had to depart from the printed text, and what is left undone.  It is deliberately
short; the exhaustive tables are in `THEOREMS.md` (numbered results) and
`EXERCISES.md` (exercises), and the file-by-file map is in `README.md`.

Everything below was checked on a `lake build` of the whole project from
scratch, which succeeds with no errors and no warnings at all (8463 jobs): no
`sorry`, and no Lean linter diagnostic.

## 1. How much is done

The book has **100 theorem-like environments** — definitions, theorems, lemmas,
corollaries, claims, one conjecture and one unnumbered paragraph.  Of these:

| | count |
| --- | --- |
| definitions formalised | 20 |
| results proved outright | 77 |
| results proved from an explicit, documented hypothesis | 0 |
| not formalised (see §5) | 3 |

"Proved outright" means: the Lean proof is complete, no file it depends on
contains a `sorry`, and `#print axioms` on it reports only `propext`,
`Classical.choice` and `Quot.sound`.  **Parts A, B, C and D are proved in
full**, and no numbered result takes a hypothesis: the last one that did,
Theorem `thm:decidable-equivalence-regular`, became unconditional when
`Transducers.EffectiveTwoWayBound` was proved (see §4).

Of the book's **81 exercises**, **all 81 are formalised**, in
`RequestProject/Exercises/`: 77 proved outright, 3 proved from an explicit
hypothesis of the kind described in §4 — a step that the book's own solution
takes for granted or only sketches, stated as a `Prop` and taken as a theorem
argument — and one, `exer:minimal-bimachine-lexicographic`, formalised but *not*
proved, because the hypothesis its solution needs turned out to be false (it is
refuted in the project).  Those hypotheses are listed with a reason in
`EXERCISES.md`.
(The sources contain 83 `\exer` environments, but two of them, in
`rational-functions.tex`, are commented out and carry no number, so they are not
exercises of the book.)

## 2. Conventions

Reading a Lean statement in this project only needs the following dictionary.

* A **string** over an alphabet `A` is a `List A`; the empty string is `[]`, and
  concatenation is `++`.  A **language** is `Language A = Set (List A)`, and
  *regular* is Mathlib's `Language.IsRegular`.
* An alphabet or a state space being **finite** is the instance argument
  `[Finite A]`.  Where the book says "there is a machine", the Lean statement
  says `∃ (Q : Type) (_ : Finite Q) (M : …), …`.
* **Continuity, prefix preservation, length preservation** and **aperiodicity**
  are the predicates `Transducers.Continuous`, `PrefixPreserving`,
  `LengthPreserving`, `Aperiodic` of `RequestProject/Common/Basic.lean`, and say
  exactly what the book's definitions say (with the one correction of §3).
* "*`f` is a composition of prime functions from the family `P`*" is
  `CompClosure P`, the closure of `P` under composition, so that the
  Krohn–Rhodes-style decomposition theorems are statements about a closure and
  not about a syntactic list of factors.
* **Decidability.**  "Problem `P` is decidable" is `DecidableUnderPromise
  promise P`: a `Computable` `Bool`-valued function that answers `P` correctly on
  every finite description (code) satisfying `promise`.  A code mentions only
  finitely many letters, so the promises and the decided properties are
  relativised to the alphabet of the code; `Transducers.not_codeTotalFunctional`
  shows that asking for totality over all of `ℕ*` instead would make the
  statement vacuous.  Undecidability is `¬ ComputablePred …`.
* Results of the book are named by their **LaTeX label**, not by their number,
  because numbers move when the sources are edited.  `LABELS.md` is the
  dictionary, and its number column is checked against the book's `main.aux`.

## 3. What the book gets wrong, or leaves imprecise

These are the places where the printed statement could not be formalised as
written.  In each case the faithful rendering is kept (commented out where it is
false) next to the corrected one, and the reason is in the docstring.  The full
list, including the merely presentational departures, is the section
*Divergences from the book* of `THEOREMS.md`.

* **Definition `def:aperiodic-mealy` (aperiodicity) is unsatisfiable as
  printed.**  It asks, for all `u, v, w` with `uvw` nonempty, for an *output
  letter* `b` that is the last letter of `f(u vⁿ w)` for all large `n`.  Taking
  `u = v = w = ε` — which is allowed, since the condition "`uvw` nonempty"
  constrains the *input*, and a length-preserving `f` maps `ε` to `ε` — there is
  no such letter, so no function is aperiodic.  The Lean definition asks for the
  last letter *as an element of `Option B`*, so that "no letter" is an allowed
  stable value.  With that reading the whole of Section *Aperiodic functions*,
  including Theorem `thm:aperiodic-mealy`, goes through.
* **Claim `claim:conditional` is false on the empty input.**  The empty string
  uses only letters of `A₁` and, at the same time, only letters of `A₂`, so the
  first two clauses of the definition of `f₁ + f₂` conflict unless `f₁(ε)` and
  `f₂(ε)` are both empty.  `Transducers.not_sum_of_regular_nil` is an explicit
  counterexample.  The Lean statement imposes the two clauses on *nonempty*
  inputs only and leaves the value at `ε` unspecified; this is harmless for the
  use the book makes of the claim, where the blocks are always nonempty.
* **Lemma `lem:k-types-fo-equivalence` says "formulas" where it means
  "sentences".**  "Two strings satisfy the same first-order formulas of
  quantifier rank at most `k`" has no meaning without a valuation for the free
  variables; the Lean statement quantifies over sentences (`φ.freeFO = ∅`),
  which is what the proof uses.
* **Lemma `lem:aperiodicity-minimal-machine` is stated about the minimal
  machine.**  Lean states, equivalently, that *some* machine computing `f`
  satisfies condition (*); the minimal machine inherits (*) from any machine
  that has it, and this way the minimal machine need not be constructed.  The
  book's finiteness hypotheses on the alphabets are not used and are dropped.
* **Theorem `thm:aperiodic-mealy` also claims decidability.**  The final
  sentence, "moreover, this property can be decided given a Mealy machine that
  computes `f`", is *not* formalised.  What is formalised is the
  characterisation, Lemma `lem:aperiodicity-minimal-machine`, on which the
  book's procedure rests; the enumeration of state transformations that turns it
  into an algorithm is not written down.
* **The mso formula of Lemma `lem:reachability-pebble-automaton` is a regular
  language here.**  The book asks for a formula `φ(s, t)` whose two free
  variables range over configurations of a pebble automaton.  Lean encodes the
  pair of configurations into the input string instead, one letter per gap of
  the input, and states that the set of encodings of reachable pairs is a
  regular language — which, by Theorem `thm:mso-logic-languages`, is the same
  thing.  The same applies to Claim `claim:reachability-basic-run`.  Because a
  formula is only ever evaluated on a genuine structure, the Lean statements ask
  for the language to be correct only on genuine encodings.

Two further discrepancies that earlier passes of this formalisation reported
have since been **corrected in the sources**, and the Lean statements now follow
the book exactly:

* Corollary `cor:2dfa-computes-all-regular-functions` used to print the
  inclusion the wrong way round; it now reads "every regular function is
  computed by a two-way transducer".
* Theorem `thm:sequential-function-independent` used to omit the condition
  "outputs `ε` on input `ε`", without which it is false (`aⁿ ↦ aⁿ⁺¹` satisfies
  the other three conditions and is not sequential).  The condition is now item
  (c).
* The derivative of Lemma `lemma:derivatives` is now defined in the sources as
  "`f(wv)` with the first `|w|` letters of the output removed", which is what
  Lean uses.  With the earlier reading `f⁽ʷ⁾(v) = f(wv)` even the identity has
  infinitely many derivatives and the Myhill–Nerode lemma is false.

## 4. What the formalisation assumes

The project asserts no `axiom` of its own.  Where a step is missing, the theorem
that needs it takes it as an explicit argument — a `Prop`-valued definition — so
that the dependency is visible in the statement and `#print axioms` still reports
only `propext`, `Classical.choice` and `Quot.sound`.  **Three such assumptions
are left in the whole project**, all of them in the exercises; no numbered result
takes one.

| result | hypothesis | what is missing |
| --- | --- | --- |
| `exer:fo-suc` | `Transducers.Exercises.EFSuccSeparation` | the Ehrenfeucht–Fraïssé argument |
| `exer:rational-composition-finiteness-undecidable` | `Transducers.Exercises.IteratesReduction` | the reduction from the halting problem for this particular problem |
| `exer:decide-rational-colision`, item (b) | `Transducers.Exercises.EffectiveLengthPairsSemilinear` | the effective form of Parikh's theorem; semilinear sets are not developed here |

One exercise, `exer:minimal-bimachine-lexicographic`, is also stated from a
hypothesis, `Transducers.Exercises.CanonicalSuffixBimachineExists`; that
hypothesis is *false* and is refuted in the project, so the exercise is counted
as not proved rather than as conditional.

The undecidability of the Post correspondence problem, which the book takes as
given and which this formalisation used to assume, is now proved here —
`Transducers.PCP.solvable_not_computablePred` — from a formalisation of Turing
machines, of the acceptance problem and of the reduction to Post correspondence
(`RequestProject/Acceptance/`, `RequestProject/Sim/`, `RequestProject/PCP/`).  So
is Example `ex:string-reversal-not-rational`, that string reversal is not
rational, which two exercises used to assume
(`Transducers.Exercises.not_isRationalFun_reverse`).

`EffectiveTwoWayBound` (`PartC/EffectiveReg.lean`) used to be the one assumption
of a numbered result: it says that an equivalence bound for two coded two-way
transducers can be *computed* from the two codes.  That such a bound exists was
already proved (`Transducers.exists_twoWayCode_bound`); what was missing was only
its computability, and the reason was structural rather than a missing Mathlib
lemma.  The chain that produces the bound passes through existentials over
abstract finite types — `IsRegularFun` is an existential over compositions of
prime functions, `IsWeighted f` is `∃ (Q : Type) (_ : Finite Q), …` — which carry
no size information, so the bound is not a function of the codes at all.

It is now **proved**, as `Transducers.effectiveTwoWayBound` of
`PartC/RegEffBound.lean`, not by making that chain effective but by a direct
construction of an explicit bound: the value of the output of a two-way
transducer on `u ++ v` decomposes as a finite sum `∑ ι, g ι u * h ι v` indexed by
the crossing data of the run at the cut, that index set has an explicit size, and
Schützenberger's rank criterion (`Common/HankelRank.lean`) then gives a length
bound which is an arithmetic expression in the number of states and the size of
the alphabet.  Counting the letters and the states occurring in a code turns it
into the primitive recursive `Transducers.RegDec.codeBound`.  `THEOREMS.md` sets
this out in detail, as does the docstring of `EffectiveTwoWayBound`.

The effective form of the book's *own* reduction is still only written out as a
Lean statement, `Transducers.EffectiveTwoWayWeighted` of `PartC/RegBoundGap.lean`,
together with a proof that it too would imply the bound
(`Transducers.effectiveTwoWayBound_of_effectiveTwoWayWeighted`); that statement
is assumed nowhere and nothing depends on it.

Four further results — `thm:equivalence-weighted-automata`,
`thm:equivalence-rational-functions`, `thm:zeroness-weighted-automata` and
`thm:decide-if-mealy` — used to be conditional too, together with a second
hypothesis of `thm:decidable-equivalence-regular`.  Their last step, "and this
can be computed", ran into a gap in Mathlib rather than in the mathematics:
Mathlib's `Primrec`/`Computable` API had no arithmetic on `ℤ` or `ℚ`, so a
linear representation over `ℚ` could not be manipulated by a *provably
computable* function.  That arithmetic is now developed here, as a
general-purpose library independent of transducers
(`Common/PrimrecArith.lean`, `Common/PrimrecList.lean`), and both hypotheses are
now theorems: `Transducers.EffectiveWeightedEvalEq` in
`PartB/WCodePrimrec.lean` and `Transducers.EffectiveTwoWayEvalEq` in
`PartC/TwoWaySimPrimrec.lean`.  The four results of Part B are proved outright.

## 5. What is not formalised, and why

Three theorem-like environments of the book have no Lean counterpart.  None of
them is a gap in a proof: none of the three is a mathematical result that this
formalisation is meant to establish.

* **Definition `def:rational-recognisable-subsets`** (rational and recognisable
  subsets of a monoid).  The book uses it once, in the remark explaining the
  name *Kleene theorem*; nothing else depends on it.  The recognisable subsets
  of `A* × B*` are formalised, for that monoid, as part of the exercises.
* **Conjecture `conj:regular-via-weighted-automata`** — an open conjecture, not
  a result.
* **The unnumbered paragraph at the end of `logic.tex`** (first-order
  transductions are exactly the compositions of map reverse, map duplicate and
  first-order rational functions).  The book states it without proof and leaves
  the proof to a future edition; it was withdrawn from this formalisation at the
  author's request.  Its easy half survives, proved, as
  `Transducers.isFOTransduction_of_compClosure`.

Every exercise of the book is formalised.  The two that were left open the
longest are now in: **`exer:polyregular-unmarked-squaring`** is proved in full,
strictness of the inclusion included, in the size sense of compatibility with
compression that the project uses throughout (the exercise's own phrasing is
about polynomial *running time*, which this project does not model, and the size
reading is the stronger of the two); and **`exer:forward-for-transducer`**, the
last exercise of the book, is proved as an equivalence between the functions
computed by forward for-transducers and the composition closure of marked
squaring and the *rational* functions; it used to rest on three explicit
hypotheses, and all three are now theorems.  Those
three are the steps of the author's solution that replay both inclusions of
Theorem `thm:for-transducers-are-polyregular` with the direction of every loop
tracked: closure of forward for-transducers under composition, a forward prenex
normal form, and rationality of the one-step transducer of the enumeration.
The fourth step of that solution, rationality of the *scan*, is proved here:
the scanning machine has a single register and only ever appends to it, and an
append-only one-register streaming string transducer computes a rational
function (`Transducers.Exercises.isRationalFun_of_appendOnlySST`).  Everything
else of that exercise is proved outright, including
that marked squaring is computed by a forward for-transducer and that every
rational function is — the latter by running the suffix automaton of a bimachine
*forwards*, as the author suggests, its state being the transition map of the
automaton on the part of the suffix already read.

Item (b) of `exer:decide-rational-colision` — is there an input on which the two
outputs have the same length? — is formalised as well, from one hypothesis: an
effective form of Parikh's theorem (semilinear sets are not developed here).  It
used to carry a second, a `Computable` label for the concrete decision
procedure, which Mathlib's computability API could not express because it had no
arithmetic on the integers, the same gap as in §4; that arithmetic is now
developed here and the label is a theorem.  What the book's solution ends with, and what
this project proves outright, is the test itself: whether a semilinear set of
pairs contains a pair with two equal coordinates, which reduces to membership in
the sub-semigroup of `ℤ` generated by a finite list of integers — the multiples
of the gcd when the list has both signs, and a bounded search otherwise.

Three exercises in all are proved from an explicit hypothesis rather than
outright, and they are the three listed in §4; a fourth,
`exer:minimal-bimachine-lexicographic`, is formalised but not proved, its
hypothesis being false.  Eighteen exercises were conditional at one time or
another, for the reasons that recur throughout — running time and computability,
and theory the project did not have (the growth rates of regular languages, the
maximum cycle mean of a weighted graph, Ehrenfeucht–Fraïssé games, Parikh
images).  All but the three have since been discharged: the missing theory was
built here.

Three of the exercises that are formalised diverge from the literal statement
of the exercise, and each divergence is recorded on the Lean statement and in
`EXERCISES.md`.  `exer:rational-compression` and `exer:regular-compression` ask
for a polynomial time algorithm turning a grammar compression of the input into
a grammar compression of the output; what is proved is the size half, that the
output has a compression polynomially larger than the input's, which is also the
form in which `exer:polyregular-marked-squaring-compression` is stated.
`exer:2dfa-complexity` asks for a deterministic two-way automaton whose shortest
accepted string is exponential in the number of states; that is proved, but by a
construction that the book does not give, because the author's own construction
gives only a superpolynomial bound.  The author's construction is kept beside
it, with the bound it really gives.

## 6. Why you can believe the table

The bookkeeping is checked by machine rather than by hand.

* `RequestProject/Labels.lean` declares, for every formalised result, an alias
  whose Lean name *is* the LaTeX label of the result, followed by
  `assert_no_sorry`.  That command fails at compile time if the declaration
  depends on `sorryAx`, or on any axiom other than `propext`,
  `Classical.choice`, `Quot.sound`.  So the whole "proved outright" column of
  `THEOREMS.md` is re-verified on every build, and a result cannot silently
  regress.
* `tools/gen_labels.py --check` verifies that the aliases, the index tables and
  the label dictionary agree: every formalised row has an alias, every alias
  points at a declaration the row names, every environment of the book is either
  aliased or explicitly accounted for, and every label the project mentions is a
  label of the book.
* `tools/tex_numbering.py --check` compares the number column of `LABELS.md`
  with the book's `main.aux`, and `tools/decl_files.py --check` compares the
  `File` column of the index of `THEOREMS.md` with where the declarations
  actually live.
* `tools/print_axioms.sh` runs `#print axioms` on all 213 aliases and reports
  any that depends on `sorryAx` or on a non-standard axiom.  It finds nothing:
  every alias depends only on `propext`, `Classical.choice`, `Quot.sound`.
* `tools/relabel.py` finds any place where a result is still referred to by
  number instead of by label.  Its 28 hits are all references to the numbering
  of Sipser's *Introduction to the Theory of Computation*, in the files that
  formalise Turing machines and the Post correspondence problem; no result of
  *Transducers* is referred to by number.
