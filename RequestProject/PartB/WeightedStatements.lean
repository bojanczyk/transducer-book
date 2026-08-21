/-
Part B: Weighted automata and machine independent characterisations
  (Sections B.3 and B.4) from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections B.3-B.4 and the statements of
their theorems, lemmas and claims.  The proofs are in the supporting files
(`MealyChar.lean`, `Typing.lean`, `LenNormalForm.lean`, `SeqChar.lean`); the
results that are not proved yet are left as `sorry` and are listed in
`THEOREMS.md`.

Not formalised here: Claims B.4.9-B.4.12, which are internal steps of the proof
of Theorem B.4.8.  They speak about the branching and non-branching parts of the
outputs of a subsequential function, auxiliary notions used only inside that
proof.
-/
import RequestProject.PartB.RationalStatements
import RequestProject.PartB.Typing
import RequestProject.PartB.SeqChar
import RequestProject.PartB.LenNormalForm
import RequestProject.PartB.WeightedPrecomp
import RequestProject.PartB.WeightedRegular
import RequestProject.PartB.SubseqChar
import RequestProject.PartB.RatIndex
import RequestProject.PartB.RatAnnot
import RequestProject.PartB.LenDec
import RequestProject.PartB.WeightedDec
import RequestProject.PartB.RatEqDec
import RequestProject.PartB.MealyDec

namespace Transducers

/-! ## B.3 Rational relations and weighted automata

**Definition B.3.1 (Semiring)** is Mathlib's `Semiring`. -/

/-! **Definition B.3.2 (Weighted automaton).**  The weight of a path
(`LabAut.weightOf`), the semantics of a weighted automaton (`LabAut.wEval`),
the requirement that every input has finitely many accepting runs
(`LabAut.FinitelyManyRuns`) and the functions computed by weighted automata
(`IsWeighted`) are defined in `RequestProject/PartB/LabAut.lean`, so that the
constructions used in the proofs below can be developed before the statements of
the numbered results. -/

/-! ### B.3.2 Decidable equivalence

As in Section B.1.2, decidability statements are formalised through computable
functions on finite descriptions (codes).  A weighted automaton over the field
of rationals is coded by a list of transitions whose weights are given by a pair
`(p, q) : ℤ × ℕ` representing the rational number `p / q`. -/

/-! The code of a weighted automaton over `ℚ` (`WCode`), the automaton that it
describes (`wcodeAut`), the function that it computes (`wcodeEval`) and the
promise that it is a genuine weighted automaton (`WCodeValid`) are defined in
`RequestProject/PartB/WCodes.lean`, so that the decision procedures used below
can be developed before the statements of the numbered results. -/

/-  The unconditional form of Theorem B.3.3 is

theorem weighted_equivalence_decidable :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2) := by
  sorry

Its mathematical content is proved in this project (Schützenberger's criterion,
`weighted_eq_of_short` in `RequestProject/PartB/WeightedZero.lean`), but the
statement asks for a `Computable` procedure manipulating rational weights, and
Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℤ` or `ℚ`.  The
missing effectivity is isolated in `RequestProject/PartB/Effective.lean` as the
two hypotheses `EffectiveWeightedEvalEq` (evaluation of a coded weighted
automaton over `ℚ` can be compared effectively) and `EffectiveWeightedBound` (a
Schützenberger bound can be computed from the codes); the version below takes
them as explicit assumptions, exactly as Theorem B.1.6 takes the undecidability
of the Post correspondence problem as an explicit assumption.  When Mathlib
gains the missing arithmetic, the two hypotheses become provable and the
unconditional statement above can be reinstated. -/

/-- **Theorem B.3.3.**  Given two weighted automata over the field of rationals,
it is decidable whether they compute the same function.

Proved from the two effectivity hypotheses of
`RequestProject/PartB/Effective.lean`; see the comment above. -/
theorem weighted_equivalence_decidable
    (hEval : EffectiveWeightedEvalEq) (hBound : EffectiveWeightedBound) :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2) :=
  weighted_equivalence_decidable_aux hEval hBound

/-  The unconditional form of Theorem B.3.4 is

theorem rationalFun_equivalence_decidable :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2) := by
  sorry

As in the book, it is proved by a reduction to Theorem B.3.3 (the reduction is
carried out in full in `RequestProject/PartB/PairWeighted.lean`,
`RequestProject/PartB/PairWeightedEval.lean` and
`RequestProject/PartB/RatEqDec.lean`), so it inherits the two effectivity
hypotheses of `RequestProject/PartB/Effective.lean` and nothing else.  The
version below takes them as explicit assumptions. -/

/-- **Theorem B.3.4.**  The equivalence problem `f = g` is decidable for rational
functions.

Proved from the two effectivity hypotheses of
`RequestProject/PartB/Effective.lean`, by the reduction of the book to
Theorem B.3.3: the two coded functions are turned into two weighted automata
over `ℚ` whose values are the numerical encodings of the outputs, multiplied by
the numbers of accepting runs of the two automata, which are the same for both.
See the comment above. -/
theorem rationalFun_equivalence_decidable
    (hEval : EffectiveWeightedEvalEq) (hBound : EffectiveWeightedBound) :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2) :=
  rationalFun_equivalence_decidable_aux hEval hBound

/-- **Lemma B.3.5.**  Weighted automata (over any semiring) are closed under
pre-composition with rational functions. -/
theorem weighted_precomp_rational {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S}
    (hf : IsRationalFun f) (hh : IsWeighted h) : IsWeighted (h ∘ f) :=
  weighted_precomp_rational_aux hf hh

/-- **Theorem B.3.6.**  A string-to-string function is rational if and only if
weighted automata are closed under pre-composition with it. -/
theorem rational_iff_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔
      ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f) :=
  rational_iff_weighted_precomp_aux f

/-  The unconditional form of Theorem B.3.7 is

theorem weighted_zeroness_decidable :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0) := by
  sorry

As for Theorem B.3.3, what is missing is not mathematics but the effectivity of
arithmetic on `ℚ` inside Mathlib's `Primrec`/`Computable` API; the version below
takes the two hypotheses of `RequestProject/PartB/Effective.lean` as explicit
assumptions. -/

/-- **Theorem B.3.7.**  The zeroness problem is decidable for weighted automata
over the field of rationals.  (The same proof works for any computable field.)

Proved from the two effectivity hypotheses of
`RequestProject/PartB/Effective.lean`, as the special case of Theorem B.3.3 in
which the second automaton is the empty one. -/
theorem weighted_zeroness_decidable
    (hEval : EffectiveWeightedEvalEq) (hBound : EffectiveWeightedBound) :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0) :=
  weighted_zeroness_decidable_aux hEval hBound

/-! ## B.4 Machine independent characterisations -/

/-! ### B.4.1 Mealy machines -/

/-- **Theorem B.4.1.**  A function is computed by a Mealy machine if and only if
it is continuous, prefix preserving and length preserving. -/
theorem isMealy_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ (Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f) :=
  isMealy_iff_aux f

/-  The original formalisation of Theorem B.4.2 was

theorem rationalFun_isMealy_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ, (∀ w v, codeRel c w v ↔ v = f w) ∧ IsMealy f) := by
  sorry

It is *degenerate*: the ambient alphabet is `ℕ`, while a code has only finitely
many transitions and therefore reads only finitely many letters, so no code can
satisfy `∀ w v, codeRel c w v ↔ v = f w` for a total `f` (compare
`Transducers.not_codeTotalFunctional`).  The property inside the promise is
therefore false for every code, and the statement would be provable with the
constant procedure `fun _ => false`.  The statement below relativises both the
promise and the property to strings over the alphabet of the code. -/

/-  The relativised statement of Theorem B.4.2 without the effectivity
hypotheses is

theorem rationalFun_isMealy_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) := by
  sorry

Its proof reduces prefix preservation to the equality of two rational functions
(`RequestProject/PartB/PrefixCodes.lean`), which is decided by Theorem B.3.4, so
it inherits the two effectivity hypotheses of
`RequestProject/PartB/Effective.lean` and nothing else; everything else -- the
characterisation of the Mealy fragment, the decision of length preservation
(Lemma B.4.3) and the two code constructions -- is discharged in full. -/

/-- **Theorem B.4.2.**  One can decide if a rational function is computed by a
Mealy machine.

The relation described by the code and the Mealy machine are compared on the
strings over the alphabet of the code (`CodeWord`); see the comment above the
original statement for why the unrelativised statement is degenerate, and the
comment just above for the two effectivity hypotheses. -/
theorem rationalFun_isMealy_decidable
    (hEval : EffectiveWeightedEvalEq) (hBound : EffectiveWeightedBound) :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) :=
  rationalFun_isMealy_decidable_aux hEval hBound

/-- **Lemma B.4.3.**  One can decide if a rational function is
length-preserving.

The decision procedure (in `RequestProject/PartB/LenDec.lean`) is correct for
*every* code, so the promise that the coded relation is a function is not
needed.  It enumerates all transition sequences of length at most `3n`, where
`n` bounds the number of states of the coded automaton, and checks that the
accepting ones read and write strings of the same length; a pumping argument
shows that this bound is sufficient. -/
theorem rationalFun_lengthPreserving_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∀ w v, codeRel c w v → v.length = w.length) :=
  ⟨LenDec.lenDec, LenDec.computable_lenDec, fun c _ => LenDec.lenDec_iff c⟩

/-! The notion of a *productive* state (a state that appears in some accepting
run) is defined in `RequestProject/PartB/LabAut.lean`. -/

/-- **Claim B.4.4.**  For an nfa with output whose states are all productive,
the computed function is length-preserving if and only if a typing
`τ : Q → ℤ` exists (i.e. every run from an initial state to `q` satisfies
`|output| = |input| + τ q`) and all accepting states are mapped to zero. -/
theorem lengthPreserving_iff_typing {A B Q : Type} (M : NFAO A B Q)
    (hprod : ∀ q, Productive M q) {f : List A → List B} (hM : ∀ w v, M.rel w v ↔ v = f w) :
    LengthPreserving f ↔
      ∃ τ : Q → ℤ,
        (∀ q ∈ M.init, ∀ ts p, M.Path q ts p →
          ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + τ p) ∧
        ∀ p ∈ M.final, τ p = 0 :=
  lengthPreserving_iff_typing_aux M hprod hM

/-- **Lemma B.4.5.**  If a rational function is length-preserving, then it is
computed by an nfa with output in which the input and output strings of every
transition have the same length. -/
theorem lengthPreserving_rational_normal_form {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hlen : LengthPreserving f) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
      (∀ t ∈ M.δ, t.2.1.length = t.2.2.1.length) ∧ ∀ w v, M.rel w v ↔ v = f w :=
  lengthPreserving_rational_normal_form_aux hf hlen

/-! ### B.4.2 Sequential functions -/

/-! The definition of a sequential transducer (`Sequential`) and of the
functions that they compute (`IsSequential`) is in
`RequestProject/PartB/SeqChar.lean`, together with the proof of Theorem B.4.6. -/

/-  **Theorem B.4.6** as stated in the book is *false*: a sequential transducer
produces no output before reading any input, so a sequential function satisfies
`f [] = []`, while the three conditions on the right hand side are satisfied for
instance by the function `aⁿ ↦ aⁿ⁺¹`.  The original statement is kept here,
commented out, and the corrected statement follows it.

theorem isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      (Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K) := by
  sorry
-/

/-- **Theorem B.4.6.**  A function is sequential if and only if it maps the
empty input to the empty output and it is continuous, prefix preserving, and has
the bounded increase property: the increase in output length caused by extending
the input by one letter is bounded.

The condition `f [] = []` is missing from the statement in the book; without it
the statement is false, since a sequential transducer produces no output before
reading any input. -/
theorem isSequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSequential f ↔
      (f [] = [] ∧ Continuous f ∧ PrefixPreserving f ∧
        ∃ K : ℕ, ∀ (w : List A) (a : A), (f (w ++ [a])).length ≤ (f w).length + K) :=
  isSequential_iff_aux f

/-! ### B.4.3 Subsequential functions -/

/-! The definition of a subsequential transducer (`Subsequential`) and of the
partial functions that they compute (`IsSubsequential`) is in
`RequestProject/PartB/SubseqDef.lean`, together with the easy implication of
Theorem B.4.8; the construction proving the other implication is in
`SubseqAlpha.lean`, `SubseqState.lean`, `SubseqBound.lean` and
`SubseqChar.lean`. -/

/-- **Theorem B.4.8.**  A partial function is subsequential if and only if it is
continuous and has bounded variation: for all `w₁, w₂` the left distances
`‖f (w w₁), f (w w₂)‖` are bounded, where `w` ranges over strings for which both
outputs are defined. -/
theorem isSubsequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → Option (List B)) :
    IsSubsequential f ↔
      (PartialContinuous f ∧
        ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
          f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K) :=
  isSubsequential_iff_aux f

/-! ### B.4.4 Rational functions -/

/-! The equivalence relation `BoundedVarRel` on input strings used in
Theorem B.4.13 (`w₁ ∼ w₂` if the left distances `‖f (w w₁), f (w w₂)‖` are bounded
uniformly in `w`) is defined in `RequestProject/PartB/RatIndex.lean`, together
with the proof that it is an equivalence relation and a left congruence and the
easy implication of the theorem; the converse implication is proved in
`RequestProject/PartB/RatAnnot.lean`. -/

/-- **Theorem B.4.13.**  A function is rational if and only if it is continuous
and the equivalence relation `BoundedVarRel f` has finite index. -/
theorem isRationalFun_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsRationalFun f ↔
      (Continuous f ∧
        {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite) :=
  isRationalFun_iff_aux f

end Transducers
