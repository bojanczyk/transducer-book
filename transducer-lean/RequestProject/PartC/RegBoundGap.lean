/- An alternative route to the last effectivity statement of Theorem
`thm:decidable-equivalence-regular` of *Transducers* (M. Bojańczyk).

This file was written when `Transducers.EffectiveTwoWayBound` of
`RequestProject/PartC/EffectiveReg.lean` -- that an equivalence bound can be *computed* from two
codes of two-way transducers -- was still a hypothesis of Theorem
`thm:decidable-equivalence-regular`.  It is one no longer: it is proved as
`Transducers.effectiveTwoWayBound` in `RequestProject/PartC/RegEffBound.lean`, with the explicit
bound `Transducers.RegDec.codeBound`, and the theorem is unconditional.  That proof does not go
through weighted automata at all; it applies an explicit-rank form of Schützenberger's criterion
(`Transducers.HankelRank.zero_of_short`) directly to the crossing-sequence decomposition of a
two-way run.

What remains here is the *effective form of the book's own reduction* to weighted automata,
`Transducers.EffectiveTwoWayWeighted` -- a computable map sending two codes of two-way transducers
to two codes of weighted automata over `ℚ` whose values agree on an input exactly when the two
coded transducers do -- together with the proof that this one statement implies
`Transducers.EffectiveTwoWayBound`
(`Transducers.effectiveTwoWayBound_of_effectiveTwoWayWeighted`).  It is *not* assumed anywhere, and
nothing in the project depends on it; it is kept because it records, in the language of the
project's own codes, what a code-to-code form of the book's argument would have to produce, and
because everything downstream of it is already proved (`Transducers.wcodeBound`,
`Transducers.wcodeEval_eq_of_short` and `Transducers.effectiveWeightedBound` in
`RequestProject/PartB/WeightedBound.lean`).

Producing such a map is the size-explicit form of the two steps of the book's proof that are
formalised only semantically: the decomposition of a two-way transducer into prime functions
(Theorem `thm:2dfa-decomposition-into-primes`, `Transducers.isRegularFun_of_isTwoWay` of
`RequestProject/PartC/SnakeReg.lean`, whose conclusion `IsRegularFun` is an existential over
compositions of primes), and the passage from a regular function to a weighted automaton over `ℚ`
(`Transducers.isWeighted_comp_regular` and `Transducers.exists_injective_weighted` of
`RequestProject/PartC/WeightedRegClosure.lean`, whose conclusion `IsWeighted` is an existential over
an abstract finite state space).  Each would have to be redone as a construction on codes, with a
proof that the code produced is valid and computes what it should. -/
import RequestProject.PartC.EffectiveReg
import RequestProject.PartB.WeightedBound

namespace Transducers

/-- **The effective form of the book's reduction of equivalence to weighted automata.**

There is a computable map sending two codes of two-way transducers to two codes
of weighted automata over `ℚ` which are valid and which, on every input, take
equal values exactly when the two coded transducers compute the same output.

This is the effective form of the book's own reduction, and it implies
`Transducers.EffectiveTwoWayBound` (`Transducers.effectiveTwoWayBound_of_effectiveTwoWayWeighted`
below).  It is *not* assumed anywhere in the project, and it is not needed for Theorem
`thm:decidable-equivalence-regular`, which is proved unconditionally in
`RequestProject/PartC/RegEffBound.lean` by a different route; it is stated in order to say
precisely what a code-to-code form of the book's argument would produce.

The statement asks less than the book's construction provides -- the two weighted automata are not
required to compute the rational encodings of the two outputs, only to separate the same inputs --
so that it isolates the gap rather than a particular way of filling it. -/
def EffectiveTwoWayWeighted : Prop :=
  ∃ W : TwoWayCode → TwoWayCode → WCode × WCode, Computable₂ W ∧
    ∀ c₁ c₂, TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      WCodeValid (W c₁ c₂).1 ∧ WCodeValid (W c₁ c₂).2 ∧
        ∀ w : List ℕ, (wcodeEval (W c₁ c₂).1 w = wcodeEval (W c₁ c₂).2 w ↔
          twoWayCodeRel c₁ w = twoWayCodeRel c₂ w)

/-- **`Transducers.EffectiveTwoWayBound` follows from the effective form of the book's
reduction.**  Given a computable map from two codes of two-way
transducers to two codes of weighted automata separating the same inputs, the equivalence bound is
computable: it is the sum of the two Schützenberger bounds `Transducers.wcodeBound` of the images,
which is primitive recursive in the codes. -/
theorem effectiveTwoWayBound_of_effectiveTwoWayWeighted
    (h : EffectiveTwoWayWeighted) : EffectiveTwoWayBound := by
  obtain ⟨W, hWcomp, hW⟩ := h
  refine ⟨fun c₁ c₂ => wcodeBound (W c₁ c₂).1 + wcodeBound (W c₁ c₂).2, ?_, ?_⟩
  · have hpair : Computable fun p : TwoWayCode × TwoWayCode => W p.1 p.2 := hWcomp
    exact Primrec.nat_add.to_comp.comp
      (primrec_wcodeBound.to_comp.comp (Computable.fst.comp hpair))
      (primrec_wcodeBound.to_comp.comp (Computable.snd.comp hpair))
  · intro c₁ c₂ h₁ h₂ hshort
    obtain ⟨hv₁, hv₂, hiff⟩ := hW c₁ c₂ h₁ h₂
    have heval : wcodeEval (W c₁ c₂).1 = wcodeEval (W c₁ c₂).2 :=
      wcodeEval_eq_of_short hv₁ hv₂ fun v hv => (hiff v).2 (hshort v hv)
    funext w
    exact (hiff w).1 (congrFun heval w)

end Transducers
