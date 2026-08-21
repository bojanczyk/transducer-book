/-
The effectivity hypotheses used by the decidability results of Section B.3 of
*Transducers* (M. Bojańczyk).

Theorems B.3.3, B.3.4, B.3.7 and B.4.2 are decidability statements about
weighted automata over the field `ℚ` and about rational functions.  Their
mathematical content is developed in full in this project (Schützenberger's
zeroness criterion in `RequestProject/PartB/WeightedZero.lean`, the reduction of
equivalence of rational functions to equivalence of weighted automata in
`RequestProject/PartB/RatWeighted.lean`), but their *formal* statements ask for
a `Computable` decision procedure in the sense of Mathlib's
`Mathlib.Computability.Partrec`, and there the development runs into a gap in
the library rather than into a gap in the mathematics: Mathlib's `Primrec` and
`Computable` API contains **no arithmetic on `ℤ` or on `ℚ`**.  There is no lemma
saying that addition, multiplication or comparison of integers or of rationals
is primitive recursive, and no `Primcodable`-level machinery from which such
lemmas could be obtained cheaply; every procedure that manipulates rational
weights therefore cannot be shown `Computable` without first developing that
API.

Rather than developing it, the two facts that are needed are isolated here as
named hypotheses, in the style already used in this project for Theorem B.1.6
(`Transducers.rationalRel_equivalence_undecidable`, which takes the
undecidability of the Post correspondence problem as an explicit hypothesis).
Both hypotheses are *true statements* about ordinary computability -- the
justification is spelled out in the docstrings -- and the results of Sections
B.3 and B.4 that depend on them are proved from them, with everything else
discharged in full.  When Mathlib gains arithmetic on `ℚ` in its `Primrec` API,
the hypotheses can be proved and the four results become unconditional.
-/
import RequestProject.PartB.WCodes

namespace Transducers

/-- **Effectivity hypothesis 1: evaluating coded weighted automata over `ℚ`.**

There is a computable procedure which, given two codes `c₁, c₂` of weighted
automata over `ℚ` and a string `v`, decides whether the two automata take the
same value on `v` -- correctly at least when both codes are *valid*, i.e. when
every input string has only finitely many accepting runs (`WCodeValid`).

*Why this is true.*  Let `c` be a valid code, with `n` states occurring in it,
and let `v` be an input string.  Every accepting run of `c` over `v` may be
assumed to have at most `(|v| + 1) * n + |v|` transitions: a longer run contains
a factor which starts and ends in the same state and reads no input, and such a
factor can be repeated, which would produce infinitely many accepting runs over
`v` and contradict the validity of `c`; removing it yields a shorter accepting
run over `v`, but here one has to be slightly more careful, since removing it
also changes the weight.  In fact validity implies outright that no accepting
run has such a factor, so *all* accepting runs over `v` are shorter than the
bound.  Consequently `wcodeEval c v` is the sum of the weights of the finitely
many accepting transition sequences of length at most that bound, a finite sum
of rational numbers each of which is a product of the rational weights read off
the code.  Rational numbers are exactly representable, and their arithmetic and
their equality test are computable, so the whole procedure is computable.

*Why it is not available here.*  The sum above is a sum of rational numbers, and
Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℚ` (nor on `ℤ`), so
no such procedure can currently be shown to be `Computable` inside Mathlib.  The
hypothesis is stated as a test of *equality of two values* rather than as the
computability of the value itself, because the latter would in addition require
the type `ℚ` to be handled by the `Computable` API on the output side; the
weaker equality test is all that the decision procedures below need. -/
def EffectiveWeightedEvalEq : Prop :=
  ∃ D : WCode × WCode × List ℕ → Bool, Computable D ∧
    ∀ c₁ c₂ (v : List ℕ), WCodeValid c₁ → WCodeValid c₂ →
      (D (c₁, c₂, v) = true ↔ wcodeEval c₁ v = wcodeEval c₂ v)

/-- **Effectivity hypothesis 2: an effective Schützenberger bound.**

There is a computable function `N` which, given two codes of weighted automata
over `ℚ`, returns a length bound with the following property: two valid coded
weighted automata that agree on all strings of length at most `N c₁ c₂` compute
the same function.

*Why this is true.*  This is the effective form of Schützenberger's criterion,
whose mathematical content is proved in this project:
`Transducers.weighted_eq_of_short` produces, for any two functions computed by
weighted automata over a field, a length bound with exactly this property, and
`Transducers.linRep_zero_of_short` shows that for a linear representation the
bound may be taken to be the dimension of the representation -- the row vectors
`u₀ · μ(v)` for `|v| ≤ k` span an increasing chain of subspaces, which must
stabilise after at most `dim` steps, and the final vector annihilates the
stabilised subspace.  For a *coded* automaton the dimension in question is
bounded by an explicit function of the code: the normal form of
`RequestProject/PartB/WeightedNF.lean` turns a code with `t` transitions whose
input strings have total length `s` into an automaton with at most
`t + s + |states| + 1` states, and the linear representation of that automaton
has one dimension per state, so `N c₁ c₂` may be taken to be the sum of the two
resulting numbers.  Nothing here is uncomputable; the bound is a simple
arithmetic function of the sizes of the two codes.

*Why it is not available here.*  The constructions of `WeightedNF.lean` and
`WeightedLinRep.lean` are carried out over abstract state types and use
`Classical.choice` (the state space of the normal form is described by a
subtype, and the linear representation is built from `finsum`s over path sets),
so the resulting dimension is not presented as an explicit function of the code;
extracting it would mean redoing those constructions with explicit state
counts.  Since the weights involved are rational numbers, that redevelopment
runs into the same missing `Primrec` arithmetic on `ℚ` as hypothesis 1 above as
soon as one wants the bound to be *computed*. -/
def EffectiveWeightedBound : Prop :=
  ∃ N : WCode → WCode → ℕ, Computable₂ N ∧
    ∀ c₁ c₂, WCodeValid c₁ → WCodeValid c₂ →
      ((∀ v : List ℕ, v.length ≤ N c₁ c₂ → wcodeEval c₁ v = wcodeEval c₂ v) →
        wcodeEval c₁ = wcodeEval c₂)

end Transducers
