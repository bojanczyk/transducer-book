/-
Part B: Rational relations and rational functions (Sections B.1 and B.2)
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections B.1-B.2 and the statements of
their theorems, lemmas and claims.  The proofs are in the supporting files
(`RatComp.lean`, `RatCont.lean`, `HomComplement.lean`, `EpsElim.lean`, ...);
the results that are not proved yet are left as `sorry` and are listed in
`THEOREMS.md`.
-/
import RequestProject.PartA.Statements
import RequestProject.PartB.RatComp
import RequestProject.PartB.RatCont
import RequestProject.PartB.HomComplement
import RequestProject.PartB.MealyChar
import RequestProject.PartB.EpsElim

namespace Transducers

/-! ## Automata with labelled transitions

The definitions of automata with labelled transitions (`LabAut`), of
nondeterministic automata with output (Definition B.1.1, `NFAO`), of rational
relations (Definition B.1.2) and of rational functions (Definition B.2.1) are in
`RequestProject/PartB/LabAut.lean`, so that the constructions used in the proofs below
can be developed before the statements of the numbered results. -/

/-! ### B.1.1 Composition and continuity -/

/-- **Theorem B.1.4.**  Rational relations are closed under relational
composition. -/
theorem rationalRel_comp {A B C : Type}
    {R : List A → List B → Prop} {S : List B → List C → Prop}
    (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => ∃ u, R w u ∧ S u v) :=
  rationalRel_comp_aux hR hS

/-- **Theorem B.1.5.**  The inverse image of a regular language under a rational
relation is regular; that is, rational relations are continuous. -/
theorem rationalRel_continuous {A B : Type}
    {R : List A → List B → Prop} (hR : IsRationalRel R) : RelContinuous R :=
  rationalRel_continuous_aux hR

/-! ### B.1.2 Undecidable equivalence

Decidability statements are formalised by means of Mathlib's notion of a
computable function.  A rational relation over the alphabet `ℕ` (every relation
over a finite alphabet can be presented this way) is described by a *code*: a
finite list of transitions together with the lists of initial and final
states. -/

/-- A finite description of a nondeterministic automaton with output whose
states are natural numbers and whose input and output alphabets are `ℕ`. -/
abbrev RelCode := List (ℕ × List ℕ × List ℕ × ℕ) × List ℕ × List ℕ

/-- The automaton described by a code. -/
def codeAut (c : RelCode) : NFAO ℕ ℕ ℕ where
  init := {q | q ∈ c.2.1}
  final := {q | q ∈ c.2.2}
  δ := {t | t ∈ c.1}
  δ_finite := c.1.finite_toSet

/-- The rational relation described by a code. -/
def codeRel (c : RelCode) : List ℕ → List ℕ → Prop := (codeAut c).rel

/-- The predicate saying that the relation described by a code is a total
function. -/
def CodeFunctional (c : RelCode) : Prop := ∀ w, ∃! v, codeRel c w v

/-- A predicate `P` is decidable under a promise if there is a computable
`Bool`-valued function that answers `P` correctly on all inputs satisfying the
promise. -/
def DecidableUnderPromise {α : Type} [Primcodable α] (promise P : α → Prop) : Prop :=
  ∃ D : α → Bool, Computable D ∧ ∀ a, promise a → (D a = true ↔ P a)

/-- **Theorem B.1.6.**  The equivalence problem `R = S` is undecidable for
rational relations. -/
theorem rationalRel_equivalence_undecidable :
    ¬ ComputablePred (fun p : RelCode × RelCode => codeRel p.1 = codeRel p.2) := by
  sorry

/-- **Claim B.1.7.**  If `h : A* → B*` is a homomorphism, then its complement
`{(w, v) | v ≠ h w}` is a rational relation. -/
theorem hom_complement_rational {A B : Type} [Finite A] [Finite B] (φ : A → List B) :
    IsRationalRel (fun (w : List A) (v : List B) => v ≠ homOf φ w) :=
  hom_complement_rational_aux φ

/-! ## B.2 Rational functions -/

/-! ### B.2.1 Bimachines -/

/-- **Definition B.2.2 (Bimachine).**  A bimachine consists of a deterministic
prefix automaton, a deterministic suffix automaton (which is run on the reverse
of the suffix) and an output function on pairs of states. -/
structure Bimachine (A B P S : Type) where
  /-- Initial state of the prefix automaton. -/
  prefixInit : P
  /-- Transition function of the prefix automaton. -/
  prefixStep : P → A → P
  /-- Initial state of the suffix automaton. -/
  suffixInit : S
  /-- Transition function of the suffix automaton. -/
  suffixStep : S → A → S
  /-- The output function. -/
  out : P → S → List B

namespace Bimachine

variable {A B P S : Type}

/-- The semantics of a bimachine: for every gap of the input string, the prefix
automaton is run on the prefix, the suffix automaton on the reverse of the
suffix, and the corresponding pieces of output are concatenated. -/
def eval (M : Bimachine A B P S) (w : List A) : List B :=
  ((List.range (w.length + 1)).map (fun i =>
    M.out (strTrans M.prefixStep (w.take i) M.prefixInit)
          (strTrans M.suffixStep (w.drop i).reverse M.suffixInit))).flatten

end Bimachine

/-- A string-to-string function computed by a bimachine. -/
def IsBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S), M.eval = f

/-- A function computed by an *aperiodic* bimachine: both the prefix and the
suffix automaton are aperiodic (Section C.4.4). -/
def IsAperiodicBimachine {A B : Type} (f : List A → List B) : Prop :=
  ∃ (P S : Type) (_ : Finite P) (_ : Finite S) (M : Bimachine A B P S),
    M.eval = f ∧ TransAperiodic M.prefixStep ∧ TransAperiodic M.suffixStep

/-- **Theorem B.2.3.**  For a string-to-string function the following are
equivalent: (1) it is a rational relation which happens to be functional;
(2) it is computed by an unambiguous nfa with output; (3) it is computed by a
bimachine. -/
theorem rational_iff_unambiguous_iff_bimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    [IsRationalFun f,
     IsUnambiguousRel (fun w v => v = f w),
     IsBimachine f].TFAE := by
  sorry

/-- An automaton with *extended transitions*: transitions are labelled by an
input string and a regular language of output strings (used in Lemma B.2.4). -/
def IsExtendedNFAO {A B Q : Type} (M : LabAut A (Language B) Q) : Prop :=
  ∀ t ∈ M.δ, Language.IsRegular t.2.2.1

/-- The relation computed by an automaton with extended transitions: the output
is any string in the concatenation of the languages along an accepting path. -/
def extRel {A B Q : Type} (M : LabAut A (Language B) Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ v ∈ (LabAut.labelsOf ts).prod

/-- The normal form of Lemma B.2.4: in every accepting run, either the input is
nonempty and each transition inputs exactly one letter, or the input is empty
and the run consists of exactly one transition. -/
def EpsilonFree {A L Q : Type} (M : LabAut A L Q) : Prop :=
  ∀ ts, M.Accepting ts →
    (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
    (LabAut.inputOf ts = [] → ts.length = 1)

/-- **Lemma B.2.4 (Elimination of ε-transitions).**  Every rational relation can
be computed by an nfa with output and extended transitions in which every
accepting run is in the normal form described by `EpsilonFree`.  Furthermore, if
every input string has finitely many outputs, then extended transitions are not
needed. -/
theorem epsilon_elimination {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    (∃ (Q : Type) (_ : Finite Q) (M : LabAut A (Language B) Q),
        IsExtendedNFAO M ∧ EpsilonFree M ∧ ∀ w v, R w v ↔ extRel M w v) ∧
      ((∀ w, {v | R w v}.Finite) →
        ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
          EpsilonFree M ∧ ∀ w v, R w v ↔ M.rel w v) :=
  epsilon_elimination_aux hR

/-- **Lemma B.2.5 (Uniformisation).**  If a rational relation is total, then it
contains an unambiguous rational relation. -/
theorem uniformisation {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ S : List A → List B → Prop, (∀ w v, S w v → R w v) ∧ IsUnambiguousRel S := by
  sorry

/-! ### B.2.2 Decomposition into primes -/

/-- The family of **prime rational functions** (Theorem B.2.6): prime Mealy
machines, their right-to-left variants, string homomorphisms, and the function
`w ↦ w#` appending a fresh separator. -/
def PrimeRationalFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  PrimeMealyFam A B f ∨
  PrimeMealyFam A B (fun w => (f w.reverse).reverse) ∨
  (∃ φ : A → List B, f = homOf φ) ∨
  (∃ e : Option A ≃ B, f = fun w => w.map (fun a => e (some a)) ++ [e none])

/-- **Theorem B.2.6.**  A string-to-string function is rational if and only if
it can be obtained by composing prime rational functions. -/
theorem rational_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔ CompClosure PrimeRationalFam A B f := by
  sorry

/-! ### B.2.3 Mealy machines as a subset of the rational functions -/

/-- A rational function is continuous, by Theorem B.1.5. -/
lemma continuous_of_isRationalFun {A B : Type} {f : List A → List B} (hf : IsRationalFun f) :
    Continuous f := by
  intro L hL
  have h := rationalRel_continuous hf L hL
  convert h using 2 with w
  simp

/-- For a prefix and length preserving function, the first `n` letters of the
output only depend on the first `n` letters of the input. -/
lemma take_eq_take_of_prefix {A B : Type} {f : List A → List B} (hpre : PrefixPreserving f)
    (hlen : LengthPreserving f) (w : List A) (n : ℕ) :
    (f (w.take n)).take n = (f w).take n := by
  have hprefix : w.take n <+: w := List.take_prefix n w
  have hprefix' : f (w.take n) <+: f w := hpre _ _ hprefix
  have hlen' : (f (w.take n)).length = (w.take n).length := hlen _
  -- Case split on whether n ≤ w.length
  by_cases h : n ≤ w.length
  · -- Case n ≤ w.length: (w.take n).length = n
    have hlen'' : (w.take n).length = n := List.length_take_of_le h
    have hlen''' : (f (w.take n)).length = n := by rw [hlen, hlen'']
    -- Left side: (f (w.take n)).take n = f (w.take n) since length = n
    have lhs : (f (w.take n)).take n = f (w.take n) := by
      have : (f (w.take n)).length ≤ n := hlen'''.le
      rw [List.take_of_length_le this]
    rw [lhs]
    -- Right side: (f w).take n = f (w.take n) since f (w.take n) <+: f w and length = n
    have rhs : (f w).take n = f (w.take n) := by
      rcases hprefix' with ⟨t, ht⟩
      have h : (f w).take (f (w.take n)).length = f (w.take n) := by
        rw [← ht]
        simp
      rwa [hlen'''] at h
    rw [rhs]
  · -- Case n > w.length: w.take n = w
    push_neg at h
    have hw : w.take n = w := by simp [le_of_lt h]
    rw [hw]

/-- Length preservation together with the determinism condition of
Theorem B.2.7 implies prefix preservation. -/
lemma prefixPreserving_of_take {A B : Type} {f : List A → List B} (hlen : LengthPreserving f)
    (htake : ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) :
    PrefixPreserving f := by
  intro w v hwv
  have hlenw : (f w).length = w.length := hlen w
  rcases hwv with ⟨t, rfl⟩
  have htake_eq : w.take w.length = (w ++ t).take w.length := by simp
  have h := htake w (w ++ t) w.length htake_eq
  rw [← hlenw] at h
  have h1 : (f w).take (f w).length = f w := List.take_length (l := f w)
  rw [h1] at h
  exact h.symm ▸ List.take_prefix (l := f (w ++ t)) (i := (f w).length)

/-- **Theorem B.2.7.**  A rational function is computed by a Mealy machine if
and only if it is length preserving and deterministic in the sense that input
strings agreeing on the first `n` letters have outputs agreeing on the first `n`
letters. -/
theorem rational_isMealy_iff {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) :
    IsMealy f ↔
      (LengthPreserving f ∧
        ∀ (w v : List A) (n : ℕ), w.take n = v.take n → (f w).take n = (f v).take n) := by
  have hchar := isMealy_iff_aux (A := A) (B := B) f
  constructor
  · intro hM
    obtain ⟨hcont, hpre, hlen⟩ := hchar.1 hM
    refine ⟨hlen, fun w v n hwv => ?_⟩
    rw [← take_eq_take_of_prefix hpre hlen w n, ← take_eq_take_of_prefix hpre hlen v n, hwv]
  · rintro ⟨hlen, htake⟩
    exact hchar.2
      ⟨continuous_of_isRationalFun hf, prefixPreserving_of_take hlen htake, hlen⟩

end Transducers
