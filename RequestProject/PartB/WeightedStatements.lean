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

namespace Transducers

/-! ## B.3 Rational relations and weighted automata

**Definition B.3.1 (Semiring)** is Mathlib's `Semiring`. -/

namespace LabAut

variable {A S Q : Type} [Semiring S]

/-- The weight of a path: the product of the weights of its transitions, taken
in the order in which they occur. -/
def weightOf (ts : List (Q × List A × S × Q)) : S := (labelsOf ts).prod

/-- **Definition B.3.2 (Weighted automaton), semantics.**  The output on an
input string `w` is the sum of the weights of the accepting runs over `w`. -/
noncomputable def wEval (M : LabAut A S Q) (w : List A) : S :=
  ∑ᶠ ts ∈ M.acceptingOn w, weightOf ts

/-- The requirement, part of Definition B.3.2, that every input string has only
finitely many accepting runs. -/
def FinitelyManyRuns (M : LabAut A S Q) : Prop := ∀ w : List A, (M.acceptingOn w).Finite

end LabAut

/-- A function `A* → S` computed by a weighted automaton over the semiring
`S`. -/
def IsWeighted {A S : Type} [Semiring S] (f : List A → S) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : LabAut A S Q),
    M.FinitelyManyRuns ∧ M.wEval = f

/-! ### B.3.2 Decidable equivalence

As in Section B.1.2, decidability statements are formalised through computable
functions on finite descriptions (codes).  A weighted automaton over the field
of rationals is coded by a list of transitions whose weights are given by a pair
`(p, q) : ℤ × ℕ` representing the rational number `p / q`. -/

/-- A finite description of a weighted automaton over `ℚ` with states and
input letters coded by natural numbers. -/
abbrev WCode := List (ℕ × List ℕ × (ℤ × ℕ) × ℕ) × List ℕ × List ℕ

/-- The weighted automaton described by a code. -/
def wcodeAut (c : WCode) : LabAut ℕ ℚ ℕ where
  init := {q | q ∈ c.2.1}
  final := {q | q ∈ c.2.2}
  δ := {t | ∃ s ∈ c.1, t = (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)}
  δ_finite := Set.Finite.ofFinset
    (c.1.toFinset.image (fun s => (s.1, s.2.1, (s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ), s.2.2.2)))
    (by intro t; simp [eq_comm])

/-- The function computed by the weighted automaton described by a code. -/
noncomputable def wcodeEval (c : WCode) : List ℕ → ℚ := (wcodeAut c).wEval

/-- The promise that a code describes a genuine weighted automaton, i.e. that
every input string has finitely many accepting runs. -/
def WCodeValid (c : WCode) : Prop := (wcodeAut c).FinitelyManyRuns

/-- **Theorem B.3.3.**  Given two weighted automata over the field of rationals,
it is decidable whether they compute the same function. -/
theorem weighted_equivalence_decidable :
    DecidableUnderPromise (fun p : WCode × WCode => WCodeValid p.1 ∧ WCodeValid p.2)
      (fun p => wcodeEval p.1 = wcodeEval p.2) := by
  sorry

/-- **Theorem B.3.4.**  The equivalence problem `f = g` is decidable for rational
functions. -/
theorem rationalFun_equivalence_decidable :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => codeRel p.1 = codeRel p.2) := by
  sorry

/-- **Lemma B.3.5.**  Weighted automata (over any semiring) are closed under
pre-composition with rational functions. -/
theorem weighted_precomp_rational {A B S : Type} [Finite A] [Finite B] [Semiring S]
    {f : List A → List B} {h : List B → S}
    (hf : IsRationalFun f) (hh : IsWeighted h) : IsWeighted (h ∘ f) := by
  sorry

/-- **Theorem B.3.6.**  A string-to-string function is rational if and only if
weighted automata are closed under pre-composition with it. -/
theorem rational_iff_weighted_precomp {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔
      ∀ (S : Type) (_ : Semiring S) (h : List B → S), IsWeighted h → IsWeighted (h ∘ f) := by
  sorry

/-- **Theorem B.3.7.**  The zeroness problem is decidable for weighted automata
over the field of rationals.  (The same proof works for any computable field.) -/
theorem weighted_zeroness_decidable :
    DecidableUnderPromise WCodeValid (fun c => wcodeEval c = 0) := by
  sorry

/-! ## B.4 Machine independent characterisations -/

/-! ### B.4.1 Mealy machines -/

/-- **Theorem B.4.1.**  A function is computed by a Mealy machine if and only if
it is continuous, prefix preserving and length preserving. -/
theorem isMealy_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsMealy f ↔ (Continuous f ∧ PrefixPreserving f ∧ LengthPreserving f) :=
  isMealy_iff_aux f

/-- **Theorem B.4.2.**  One can decide if a rational function is computed by a
Mealy machine. -/
theorem rationalFun_isMealy_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ, (∀ w v, codeRel c w v ↔ v = f w) ∧ IsMealy f) := by
  sorry

/-- **Lemma B.4.3.**  One can decide if a rational function is
length-preserving. -/
theorem rationalFun_lengthPreserving_decidable :
    DecidableUnderPromise CodeFunctional
      (fun c => ∀ w v, codeRel c w v → v.length = w.length) := by
  sorry

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

/-- A subsequential transducer: a sequential transducer with a partial
end-of-input function, which is applied to the last state of the computation. -/
structure Subsequential (A B Q : Type) extends Sequential A B Q where
  /-- The partial end-of-input function. -/
  endOfInput : Q → Option (List B)

namespace Subsequential

variable {A B Q : Type}

/-- The semantics of a subsequential transducer: a partial function. -/
def eval (T : Subsequential A B Q) (w : List A) : Option (List B) :=
  (T.endOfInput (strTrans T.toSequential.transFun w T.toSequential.init)).map
    (fun u => T.toSequential.eval w ++ u)

end Subsequential

/-- A partial function computed by a subsequential transducer. -/
def IsSubsequential {A B : Type} (f : List A → Option (List B)) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (T : Subsequential A B Q), T.eval = f

/-- **Theorem B.4.8.**  A partial function is subsequential if and only if it is
continuous and has bounded variation: for all `w₁, w₂` the left distances
`‖f (w w₁), f (w w₂)‖` are bounded, where `w` ranges over strings for which both
outputs are defined. -/
theorem isSubsequential_iff {A B : Type} [Finite A] [Finite B] (f : List A → Option (List B)) :
    IsSubsequential f ↔
      (PartialContinuous f ∧
        ∀ w₁ w₂ : List A, ∃ K : ℕ, ∀ (w : List A) (v₁ v₂ : List B),
          f (w ++ w₁) = some v₁ → f (w ++ w₂) = some v₂ → leftDist v₁ v₂ ≤ K) := by
  sorry

/-! ### B.4.4 Rational functions -/

/-- The equivalence relation on input strings used in Theorem B.4.13:
`w₁ ∼ w₂` if the left distances `‖f (w w₁), f (w w₂)‖` are bounded uniformly
in `w`. -/
def BoundedVarRel {A B : Type} (f : List A → List B) (w₁ w₂ : List A) : Prop :=
  ∃ K : ℕ, ∀ w : List A, leftDist (f (w ++ w₁)) (f (w ++ w₂)) ≤ K

/-- **Theorem B.4.13.**  A function is rational if and only if it is continuous
and the equivalence relation `BoundedVarRel f` has finite index. -/
theorem isRationalFun_iff {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsRationalFun f ↔
      (Continuous f ∧
        {C : Set (List A) | ∃ w₁, C = {w₂ | BoundedVarRel f w₁ w₂}}.Finite) := by
  sorry

end Transducers
