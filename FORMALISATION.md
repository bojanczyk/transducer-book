# What has been formalised, for a reader of the book

This note is addressed to someone who is reading *Transducers* (M. Bojańczyk)
and wants to know what the Lean development in this directory says about it: how
much of the book is machine-checked, what the formal statements mean, where they
had to depart from the printed text, and what is left undone.  It is deliberately
short; the exhaustive tables are in `THEOREMS.md` (numbered results) and
`EXERCISES.md` (exercises), and the file-by-file map is in `README.md`.

Everything below was checked on a `lake build` of the whole project from
scratch, which succeeds with no errors (8386 jobs).  Its only diagnostics are 47
Lean linter warnings about unused variables inside auxiliary proofs; they are
inventoried in `THEOREMS.md`, and none of them touches a statement.

## 1. How much is done

The book has **100 theorem-like environments** — definitions, theorems, lemmas,
corollaries, claims, one conjecture and one unnumbered paragraph.  Of these:

| | count |
| --- | --- |
| definitions formalised | 20 |
| results proved outright | 71 |
| results proved from an explicit, documented hypothesis | 6 |
| not formalised (see §5) | 3 |

"Proved outright" means: the Lean proof is complete, no file it depends on
contains a `sorry`, and `#print axioms` on it reports only `propext`,
`Classical.choice` and `Quot.sound`.  **Parts A, B and D are proved in full.**
In Part C every numbered result is proved as well; the one qualification is
Theorem `thm:decidable-equivalence-regular`, which is conditional in the sense
of §4.

Of the book's **81 exercises**, **65 are formalised and proved**, in
`RequestProject/Exercises/`; the remaining 16 are listed with a reason in
`EXERCISES.md`, and every one of them has a written solution in the book.  (The
sources contain 83 `\exer` environments, but two of them, in
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

## 4. The six results that are proved from a hypothesis

Six statements of the book are decidability statements whose mathematical
content is fully proved here, but whose last step — "and this can be computed" —
runs into a gap in Mathlib rather than in the mathematics: Mathlib's
`Primrec`/`Computable` API has no arithmetic on `ℤ` or `ℚ`, so a linear
representation over `ℚ` cannot yet be manipulated by a *provably computable*
function.  Rather than assert the missing ingredient as an axiom, each theorem
takes it as an explicit argument, so that the dependency is visible in the
statement and `#print axioms` still reports only the three standard axioms.

| result | hypothesis |
| --- | --- |
| `thm:undecidable-equivalence-rational-relations` | `¬ ComputablePred Transducers.PCP.Solvable` (undecidability of Post correspondence) |
| `thm:equivalence-weighted-automata` | `Transducers.EffectiveWeightedEvalEq` |
| `thm:equivalence-rational-functions` | `Transducers.EffectiveWeightedEvalEq` |
| `thm:zeroness-weighted-automata` | `Transducers.EffectiveWeightedEvalEq` |
| `thm:decide-if-mealy` | `Transducers.EffectiveWeightedEvalEq` |
| `thm:decidable-equivalence-regular` | `Transducers.EffectiveTwoWayEvalEq` and `Transducers.EffectiveTwoWayBound` |

`EffectiveWeightedEvalEq` (`PartB/Effective.lean`) says that the values of two
coded weighted automata on a given input can be compared effectively;
`EffectiveTwoWayEvalEq` and `EffectiveTwoWayBound` (`PartC/EffectiveReg.lean`)
say the same for two coded two-way transducers, and that an equivalence bound
can be computed from the codes.  All three are true, and the *non-effective*
content behind them — Schützenberger's bound, the reduction of equivalence of
regular functions to a finite check (`Transducers.regularFun_eq_of_short`) — is
proved unconditionally in this project.

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

Of the exercises, 16 are not formalised; `EXERCISES.md` groups them by reason.
The recurring ones are statements about running time (which this project does
not model), decidability statements whose reduction would have to be carried out
for *codes* of automata, and statements that rest on theory the project does not
have (the growth rates of regular languages, the maximum cycle mean of a
weighted graph, Ehrenfeucht–Fraïssé games).  In full, they are
`exer:rational-outpus-of-exactly-linear-size`,
`exer:rational-outpus-of-exactly-linear-size-rational-number`,
`exer:regular-outpus-of-exactly-linear-size`, `exer:full-ideal`,
`exer:polynomial-ideals`, `exer:all-ideals`, `exer:decide-same-ideal`,
`exer:rational-injectivity-decidable`,
`exer:rational-composition-finiteness-undecidable`,
`exer:minimal-bimachine-lexicographic`, `exer:non-minimal-automaton`,
`exer:fo-non-elementary`, `exer:fo-suc`, `exer:polyregular-unmarked-squaring`,
`exer:for-transducer-continuity-nonelementary` and
`exer:forward-for-transducer`, together with item (b) of the otherwise
formalised `exer:decide-rational-colision`.

Three of the 65 that *are* formalised diverge from the literal statement of the
exercise, and each divergence is recorded on the Lean statement and in
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
* `tools/relabel.py` finds any place where a result is still referred to by
  number instead of by label, and `tools/print_axioms.sh` runs `#print axioms`
  on all 196 aliases and reports any that depends on `sorryAx` or on a
  non-standard axiom.  Neither finds anything.
