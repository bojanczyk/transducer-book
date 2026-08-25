/-
The effectivity hypotheses used by Theorem C.1.4 of *Transducers*
(M. Bojańczyk): equivalence is decidable for regular functions.

The mathematical content of the book's proof is developed in full in this
project: the reduction of the equality of two regular functions to the
equivalence of two weighted automata over `ℚ`, through the prime decomposition
and the constructions for map reverse and map duplicate, is in
`RequestProject/PartC/WeightedRegClosure.lean`, and its conclusion
`Transducers.regularFun_eq_of_short` is exactly the decision procedure in
semantic form: two regular functions over a finite input alphabet are equal as
soon as they agree on the finitely many inputs of length at most a bound coming
from Schützenberger's criterion.

The *formal* statement of Theorem C.1.4, however, asks for a `Computable`
decision procedure on finite descriptions of two-way transducers, and there --
exactly as for Theorems B.3.3 and B.3.7 of Part B, see
`RequestProject/PartB/Effective.lean` -- the development runs into a gap in
Mathlib rather than into a gap in the mathematics: Mathlib's `Primrec` and
`Computable` API contains **no arithmetic on `ℤ` or on `ℚ`**, while both steps
of the chain above manipulate rational weights (the bound is read off a linear
representation over `ℚ` built from the code, and the values compared along the
way are rational numbers).

The two facts that are needed are therefore isolated here as named hypotheses,
in the style already used in this project for Theorem B.1.6 (which takes the
undecidability of the Post correspondence problem as an explicit hypothesis) and
for Theorems B.3.3, B.3.4, B.3.7 and B.4.2 (which take
`Transducers.EffectiveWeightedEvalEq` as an explicit hypothesis).  Both are
*true statements* about ordinary computability, and everything else -- that the
finitely many strings to be tested may be taken over the letters of the two
codes together with one fresh letter (`RequestProject/PartC/RegCodeSan.lean`),
and the assembly of the decision procedure -- is discharged in full in
`RequestProject/PartC/RegEqDec.lean`.
-/
import RequestProject.PartC.RegCodeSan
import RequestProject.PartB.Codes

namespace Transducers

/-- **Effectivity hypothesis: comparing coded two-way transducers on a given
input.**

There is a computable procedure which, given two codes `c₁, c₂` of two-way
transducers and an input string `w`, decides whether the two transducers have
the same outputs on `w` -- correctly at least when both codes are *total*, i.e.
when every input has at least one output (`TwoWayCodeTotal`).

*Why this is true.*  A two-way transducer is deterministic, so its run on `w` is
a uniquely determined sequence of configurations; the promise says that this run
reaches the halting vertex, and then the output is the concatenation of the
strings produced along it.  Simulating the run and comparing the two outputs is
an ordinary computation on finite objects.

*Why it is not available here.*  Simulating the run is an unbounded search: the
promise guarantees termination, but a `Computable` (as opposed to `Partrec`)
procedure has to be given a bound in advance, and the natural bound -- the run
of a halting deterministic two-way transducer visits each position at most once
per state, cf. `Transducers.TwoWay.widthLe_card` -- has to be extracted from the
code, which is precisely the kind of effective bookkeeping on codes that the
missing `Primrec` API for the arithmetic used by the equivalence test makes
unavailable here.  The hypothesis is stated as a test of *equality of the two
behaviours* rather than as the computability of the output itself, because the
latter is all that the decision procedure needs. -/
def EffectiveTwoWayEvalEq : Prop :=
  ∃ D : TwoWayCode × TwoWayCode × List ℕ → Bool, Computable D ∧
    ∀ c₁ c₂ (w : List ℕ), TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      (D (c₁, c₂, w) = true ↔ twoWayCodeRel c₁ w = twoWayCodeRel c₂ w)

/-- **Effectivity hypothesis: a computable equivalence bound.**

There is a computable function `N` which, given two codes of two-way
transducers, returns a length bound with the following property: two total coded
two-way transducers that agree on all inputs of length at most `N c₁ c₂`
compute the same relation.

*Why this is true.*  The *mathematical* content of the statement -- that such a
bound exists for every pair of codes -- is **proved** in
`RequestProject/PartC/RegCodeBound.lean`
(`Transducers.exists_twoWayCode_bound`), from the conclusion
`Transducers.regularFun_eq_of_short` of the book's proof of Theorem C.1.4 in
`RequestProject/PartC/WeightedRegClosure.lean`: a
coded two-way transducer computes a regular function (Theorem C.2.9,
`Transducers.twoWay_isRegular`), the equality of two regular functions is the
zeroness of a weighted automaton over `ℚ` obtained from them, and
Schützenberger's criterion bounds the length of a witness of non-zeroness by the
dimension of a linear representation of that automaton, which is a function of
the two codes.  What is assumed here is only that this bound can be *computed*
from the two codes; it is the same missing ingredient as in Theorems B.3.3 and
B.3.7, namely arithmetic on `ℤ` and `ℚ` in Mathlib's `Primrec`/`Computable` API,
which the construction of the linear representation from the code needs. -/
def EffectiveTwoWayBound : Prop :=
  ∃ N : TwoWayCode → TwoWayCode → ℕ, Computable₂ N ∧
    ∀ c₁ c₂, TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      ((∀ w : List ℕ, w.length ≤ N c₁ c₂ → twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) →
        twoWayCodeRel c₁ = twoWayCodeRel c₂)

end Transducers
