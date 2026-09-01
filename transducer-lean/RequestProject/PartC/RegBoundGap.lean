/- What exactly is missing for the last effectivity hypothesis of Theorem
`thm:decidable-equivalence-regular` of *Transducers* (M. Bojańczyk).

Theorem `thm:decidable-equivalence-regular` is proved in
`RequestProject/PartC/RegEqDec.lean` from one hypothesis,
`Transducers.EffectiveTwoWayBound` of `RequestProject/PartC/EffectiveReg.lean`:
that an equivalence bound can be *computed* from two codes of two-way
transducers.  That such a bound *exists* is proved
(`Transducers.exists_twoWayCode_bound`, `RequestProject/PartC/RegCodeBound.lean`);
what is missing is that it is a computable function of the codes, because the
book's chain of constructions produces the bound from existentials over abstract
finite types and so carries no size information.

This file makes that account precise, and machine-checked: it states the *effective form of the
book's reduction* to weighted automata, `Transducers.EffectiveTwoWayWeighted` -- a computable map
sending two codes of two-way transducers to two codes of weighted automata over `ℚ` whose values
agree on an input exactly when the two coded transducers do -- and proves that this one statement
implies the remaining hypothesis
(`Transducers.effectiveTwoWayBound_of_effectiveTwoWayWeighted`).  Nothing here is used in the proof
of a numbered result: the hypothesis of Theorem `thm:decidable-equivalence-regular` is unchanged,
and `EffectiveTwoWayWeighted` is *not* assumed anywhere.  The point of the file is that the gap is
exactly one construction, stated in the language of the project's own codes, and that everything
downstream of it -- the Schützenberger bound as an explicit arithmetic function of a code, its
primitive recursiveness, and the assembly of the decision procedure -- is already proved
(`Transducers.wcodeBound`, `Transducers.wcodeEval_eq_of_short` and
`Transducers.effectiveWeightedBound` in `RequestProject/PartB/WeightedBound.lean`).

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

This is what is missing for `Transducers.EffectiveTwoWayBound`, and it is all that is missing:
`Transducers.effectiveTwoWayBound_of_effectiveTwoWayWeighted` below derives that hypothesis from
it.  It is *not* assumed anywhere in the project; it is stated in order to say precisely what a
proof of Theorem `thm:decidable-equivalence-regular` without hypotheses would need.

The statement asks less than the book's construction provides -- the two weighted automata are not
required to compute the rational encodings of the two outputs, only to separate the same inputs --
so that it isolates the gap rather than a particular way of filling it. -/
def EffectiveTwoWayWeighted : Prop :=
  ∃ W : TwoWayCode → TwoWayCode → WCode × WCode, Computable₂ W ∧
    ∀ c₁ c₂, TwoWayCodeTotal c₁ → TwoWayCodeTotal c₂ →
      WCodeValid (W c₁ c₂).1 ∧ WCodeValid (W c₁ c₂).2 ∧
        ∀ w : List ℕ, (wcodeEval (W c₁ c₂).1 w = wcodeEval (W c₁ c₂).2 w ↔
          twoWayCodeRel c₁ w = twoWayCodeRel c₂ w)

/-- **The remaining hypothesis of Theorem `thm:decidable-equivalence-regular` follows from the
effective form of the book's reduction.**  Given a computable map from two codes of two-way
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
