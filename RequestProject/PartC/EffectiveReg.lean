/-
The effectivity statements used by Theorem `thm:decidable-equivalence-regular` of *Transducers*
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

The *formal* statement of Theorem `thm:decidable-equivalence-regular`, however, asks for a
`Computable` decision procedure on finite descriptions of two-way transducers.  Two effectivity
statements are needed for that.

* Two coded two-way transducers can be compared effectively on a given input.  This is **proved**:
  it is `Transducers.EffectiveTwoWayEvalEq` in `RequestProject/PartC/TwoWaySimPrimrec.lean`, from
  the fuel-bounded simulation of `RequestProject/PartC/TwoWaySim.lean`.  It used to be assumed,
  because Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℤ` or on `ℚ`; that arithmetic,
  and the operations on lists that go with it, are now developed as a general-purpose library in
  `RequestProject/Common/PrimrecArith.lean` and `RequestProject/Common/PrimrecList.lean`, and it
  turned out that the comparison of two coded two-way transducers needs no rational arithmetic at
  all -- only a bound on the length of a halting run, which is
  `Transducers.RegDec.halt_time_lt_fuel`.

* An equivalence bound can be *computed* from the two codes.  This one is still assumed, as
  `Transducers.EffectiveTwoWayBound` below; the docstring of that statement says precisely what is
  missing.  That such a bound *exists* is proved (`Transducers.exists_twoWayCode_bound`,
  `RequestProject/PartC/RegCodeBound.lean`).

Everything else -- that the finitely many strings to be tested may be taken over the letters of the
two codes together with one fresh letter (`RequestProject/PartC/RegCodeSan.lean`), and the assembly
of the decision procedure -- is discharged in full in `RequestProject/PartC/RegEqDec.lean`. -/
import RequestProject.PartC.TwoWaySimPrimrec
import RequestProject.PartB.Codes

namespace Transducers

/-- **Effectivity hypothesis: a computable equivalence bound.**

There is a computable function `N` which, given two codes of two-way
transducers, returns a length bound with the following property: two total coded
two-way transducers that agree on all inputs of length at most `N c₁ c₂`
compute the same relation.

*Why this is true.*  The *mathematical* content of the statement -- that such a bound exists for
every pair of codes -- is **proved** in `RequestProject/PartC/RegCodeBound.lean`
(`Transducers.exists_twoWayCode_bound`), from the conclusion `Transducers.regularFun_eq_of_short` of
the book's proof of Theorem `thm:decidable-equivalence-regular` in
`RequestProject/PartC/WeightedRegClosure.lean`: a coded two-way transducer computes a regular
function (Theorem `thm:2dfa-decomposition-into-primes`, `Transducers.twoWay_isRegular`), the
equality of two regular functions is the zeroness of a weighted automaton over `ℚ` obtained from
them, and Schützenberger's criterion bounds the length of a witness of non-zeroness by the dimension
of a linear representation of that automaton.

*What is missing, precisely.*  Not a `Primrec` lemma: the obstacle is not in Mathlib but in the
shape of the chain above, and no amount of arithmetic on `ℤ` or `ℚ` in Mathlib's `Primrec` API
would remove it.  What the hypothesis asks for is a bound that is a *computable function of the two
codes*, and the bound produced by the chain is obtained from three existential statements over
abstract finite types, none of which carries any size information:

* `Transducers.isRegularFun_of_isTwoWay` (`RequestProject/PartC/SnakeReg.lean`) turns a two-way
  transducer into a decomposition into prime functions; `IsRegularFun` is an existential over
  compositions of primes, and the snake induction that produces it recurses on the width of the run,
  so the number and the size of the primes obtained are not read off the transducer anywhere in the
  proof.
* `Transducers.isWeighted_comp_regular` and `Transducers.exists_injective_weighted`
  (`RequestProject/PartC/WeightedRegClosure.lean`) turn such a
  decomposition into a weighted automaton over `ℚ`; `IsWeighted f` is
  `∃ (Q : Type) (_ : Finite Q), …`, so the state space -- and hence the dimension that
  Schützenberger's criterion turns into the bound -- exists only as an abstract finite type.
* `Transducers.weighted_eq_of_short` (`RequestProject/PartB/WeightedZero.lean`) then supplies the
  bound as `d₁ + d₂`, the sum of the dimensions of two linear representations obtained from those
  abstract types.

For the analogous statement about *weighted* automata the same chain is effective, and there the
bound is proved computable: `Transducers.effectiveWeightedBound` in
`RequestProject/PartB/WeightedBound.lean` computes it with the explicit `Transducers.wcodeBound`,
because a `WCode` *is* a linear representation, up to normalisation.  What would have to exist here
is the corresponding effective form of the book's reduction: a computable map `TwoWayCode → WCode`,
together with a proof that a valid code is produced and that `Transducers.wcodeEval` of the image
decides the equality of the coded relations.  The bound would then be
`Transducers.wcodeBound` of the two images, and this hypothesis would follow from
`Transducers.effectiveWeightedBound`.  Producing that map means re-proving the prime decomposition
(Theorem `thm:2dfa-decomposition-into-primes`, the snake lemma of `RequestProject/PartC/Snake*.lean`)
and the closure properties of weighted automata used in `WeightedRegClosure.lean` in a size-explicit,
code-to-code form; that is a large piece of work, and it is the only thing standing between this
hypothesis and a theorem. -/
def EffectiveTwoWayBound : Prop :=
  ∃ N : TwoWayCode → TwoWayCode → ℕ, Computable₂ N ∧
    ∀ c₁ c₂, TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      ((∀ w : List ℕ, w.length ≤ N c₁ c₂ → twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) →
        twoWayCodeRel c₁ = twoWayCodeRel c₂)

end Transducers
