/- The effectivity hypothesis used by the decidability results of Section *Rational relations and
weighted automata* of *Transducers* (M. Bojańczyk).

Theorems `thm:equivalence-weighted-automata`, `thm:equivalence-rational-functions`,
`thm:zeroness-weighted-automata` and `thm:decide-if-mealy` are decidability statements about
weighted automata over the field `ℚ` and about rational functions.  Their mathematical content is
developed in full in this project (Schützenberger's zeroness criterion in
`RequestProject/PartB/WeightedZero.lean`, its effective form in
`RequestProject/PartB/WeightedBound.lean`, the reduction of equivalence of rational functions to
equivalence of weighted automata in `RequestProject/PartB/PairWeighted.lean`,
`RequestProject/PartB/PairWeightedEval.lean` and `RequestProject/PartB/RatEqDec.lean`), but their
*formal* statements ask for a `Computable` decision procedure in the sense of Mathlib's
`Mathlib.Computability.Partrec`, and there the development runs into a gap in the library rather
than into a gap in the mathematics: Mathlib's `Primrec` and `Computable` API contains **no
arithmetic on `ℤ` or on `ℚ`**.  There is no lemma saying that addition, multiplication or comparison
of integers or of rationals is primitive recursive, and no `Primcodable`-level machinery from which
such lemmas could be obtained cheaply; every procedure that manipulates rational weights therefore
cannot be shown `Computable` without first developing that API.

Rather than developing it, the one fact that is needed is isolated here as a named hypothesis, in
the style already used in this project for Theorem `thm:undecidable-equivalence-rational-relations`
(`Transducers.rationalRel_equivalence_undecidable`, which takes the undecidability of the Post
correspondence problem as an explicit hypothesis). The hypothesis is a *true statement* about
ordinary computability -- the justification is spelled out in the docstring -- and the results of
Sections *Rational relations and weighted automata* and *Machine independent characterisations* that
depend on it are proved from it, with everything else discharged in full.  When Mathlib gains
arithmetic on `ℚ` in its `Primrec` API, the hypothesis can be proved and the four results become
unconditional.

The second hypothesis that these results used to take, an effective form of the
Schützenberger bound, is no longer assumed: it is stated below as
`EffectiveWeightedBound` and *proved* in
`RequestProject/PartB/WeightedBound.lean`
(`Transducers.effectiveWeightedBound`), since the bound is a bound on the
dimension of a linear representation and is therefore a function of the sizes of
the two codes only, involving no arithmetic on the weights.
-/
import RequestProject.PartB.WCodes

namespace Transducers

/-- **Effectivity hypothesis: evaluating coded weighted automata over `ℚ`.**

There is a computable procedure which, given two codes `c₁, c₂` of weighted
automata over `ℚ` and a string `v`, decides whether the two automata take the
same value on `v` -- correctly at least when both codes are *valid*, i.e. when
every input string has only finitely many accepting runs (`WCodeValid`).

*Why this is true.*  Let `c` be a valid code, with `n` states occurring in it,
and let `v` be an input string.  Every accepting run of `c` over `v` may be
assumed to have at most `(|v| + 1) * n + |v|` transitions: a longer run contains
a factor which starts and ends in the same state and reads no input, and such a
factor can be repeated, which would produce infinitely many accepting runs over
`v` and contradict the validity of `c`.  In fact validity implies outright that
no accepting run has such a factor, so *all* accepting runs over `v` are shorter
than the bound.  Consequently `wcodeEval c v` is the sum of the weights of the
finitely many accepting transition sequences of length at most that bound, a
finite sum of rational numbers each of which is a product of the rational
weights read off the code.  Rational numbers are exactly representable, and
their arithmetic and their equality test are computable, so the whole procedure
is computable.

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

/-- **An effective Schützenberger bound.**

There is a computable function `N` which, given two codes of weighted automata
over `ℚ`, returns a length bound with the following property: two valid coded
weighted automata that agree on all strings of length at most `N c₁ c₂` compute
the same function.

This is *not* a hypothesis: it is proved in `RequestProject/PartB/WeightedBound.lean`
(`Transducers.effectiveWeightedBound`), with the explicit bound `Transducers.wcodeBound`.  The
statement is kept here, next to the hypothesis above, because that is where the decision procedures
of Section *Rational relations and weighted automata* look for it.

The proof is the effective form of Schützenberger's criterion.
`Transducers.linRep_eq_of_short` (in `RequestProject/PartB/WeightedZero.lean`)
shows that two functions given by linear representations of dimensions `d₁` and
`d₂` agree everywhere as soon as they agree on the strings of length at most
`d₁ + d₂`, and `Transducers.WBound.exists_linRep_bounded` produces a linear
representation whose dimension is bounded by an explicit function of the code:
the representation has one dimension per useful state of the normalised
automaton, and a useful state is either an initial state or the target of a
transition, hence one of the `1 + |initial states|` initial states of the
normalised automaton or one of the states `cfg t x` where `t` is a lifted or
copied transition and `x` a suffix of its input string.  Nothing here involves
arithmetic on the weights, so the bound is a primitive recursive function of the
two codes. -/
def EffectiveWeightedBound : Prop :=
  ∃ N : WCode → WCode → ℕ, Computable₂ N ∧
    ∀ c₁ c₂, WCodeValid c₁ → WCodeValid c₂ →
      ((∀ v : List ℕ, v.length ≤ N c₁ c₂ → wcodeEval c₁ v = wcodeEval c₂ v) →
        wcodeEval c₁ = wcodeEval c₂)

end Transducers
