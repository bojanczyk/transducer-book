/- Part B: Rational relations and rational functions (Sections *Rational relations* and *Rational
functions*)
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections *Rational relations* to *Rational functions* and the
statements of their theorems, lemmas and claims.  The proofs are in the supporting files
(`RatComp.lean`, `RatCont.lean`, `HomComplement.lean`, `EpsElim.lean`, `Unambig.lean`,
`Uniform.lean`, `Bimachine.lean`, `RatBimach.lean`, `PrimeRat.lean`, `BimachPrime.lean`, ...); the
results that are not proved yet are left as `sorry` and are listed in `THEOREMS.md`. -/
import RequestProject.PartA.Statements
import RequestProject.PartB.RatComp
import RequestProject.PartB.RatCont
import RequestProject.PartB.HomComplement
import RequestProject.PartB.MealyChar
import RequestProject.PartB.EpsElim
import RequestProject.PartB.Uniform
import RequestProject.PartB.Bimachine
import RequestProject.PartB.RatBimach
import RequestProject.PartB.BimachPrime
import RequestProject.PartB.PCPRed

namespace Transducers

/-! ## Automata with labelled transitions

The definitions of automata with labelled transitions (`LabAut`), of nondeterministic automata with
output (Definition `def:nfa-with-output`, `NFAO`), of rational relations (Definition
`def:rational-relation`) and of rational functions (Definition `def:rational-function`) are
in `RequestProject/PartB/LabAut.lean`, so that the constructions used in the proofs below can be
developed before the statements of the numbered results. -/

/-! ### Rational and recognisable subsets of a monoid

Section *Why the name rational?* of the book explains the terminology by identifying, in an
arbitrary monoid `M`, the two candidate notions of a "regular" subset: the recognisable subsets,
which generalise the (two-sided) Myhill-Nerode equivalence, and the rational subsets, which
generalise the regular expressions.  In the free monoid `A*` the two notions coincide, by the
Kleene Theorem; the book states the definition only to explain the name "rational", and no later
result uses it. -/

section MonoidSubsets

open scoped Pointwise

universe u

/-- **Definition `def:rational-recognisable-subsets`** (recognisable subsets of a monoid).  A
subset `L` of a monoid `M` is *recognisable* if it is a union of finitely many equivalence classes
of an equivalence relation on `M` that has finite index and is a congruence, i.e. is compatible
with the multiplication of `M`.

A congruence of a monoid is Mathlib's `Con M`, its classes are the elements of the quotient
`c.Quotient`, and finite index is `Finite c.Quotient`; a union of the classes in `S` is the
preimage of `S` under the quotient map.  The finiteness of `S` is then automatic, and is
nevertheless required here, as in the book. -/
def IsRecognisableSubset {M : Type*} [Monoid M] (L : Set M) : Prop :=
  ∃ c : Con M, Finite c.Quotient ∧
    ∃ S : Set c.Quotient, S.Finite ∧ L = (fun m : M => (m : c.Quotient)) ⁻¹' S

/-- **Definition `def:rational-recognisable-subsets`** (rational subsets of a monoid).  The
*rational* subsets of a monoid `M` are those that can be obtained from the finite subsets by
applying finitely many times union, product and Kleene star `L* = ⋃ₙ Lⁿ`.  Being the least such
class, this is an inductive predicate, whose constructors are the operations of the definition and
whose recursor is the induction principle "every class of subsets that contains the finite sets and
is closed under union, product and star contains all rational subsets". -/
inductive IsRationalSubset {M : Type*} [Monoid M] : Set M → Prop
  | finite {L : Set M} (hL : L.Finite) : IsRationalSubset L
  | union {K L : Set M} : IsRationalSubset K → IsRationalSubset L → IsRationalSubset (K ∪ L)
  | mul {K L : Set M} : IsRationalSubset K → IsRationalSubset L → IsRationalSubset (K * L)
  | star {L : Set M} : IsRationalSubset L → IsRationalSubset (⋃ n : ℕ, L ^ n)

/-- The Kleene star `L* = ⋃ₙ Lⁿ` of a subset of a monoid is the submonoid that it generates. -/
theorem iUnion_pow_eq_submonoidClosure {M : Type*} [Monoid M] (L : Set M) :
    (⋃ n : ℕ, L ^ n) = (Submonoid.closure L : Set M) := by
  ext m
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing m with
    | zero =>
        rw [pow_zero, Set.mem_one] at hn
        exact hn ▸ one_mem _
    | succ n ih =>
        rw [pow_succ, Set.mem_mul] at hn
        obtain ⟨x, hx, y, hy, rfl⟩ := hn
        exact mul_mem (ih x hx) (Submonoid.subset_closure hy)
  · intro hm
    induction hm using Submonoid.closure_induction with
    | mem x hx => exact ⟨1, by simpa using hx⟩
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
        obtain ⟨n, hn⟩ := hx
        obtain ⟨k, hk⟩ := hy
        exact ⟨n + k, by rw [pow_add]; exact Set.mul_mem_mul hn hk⟩

/-- A subset of a monoid is recognisable if and only if it is the preimage of some subset of a
finite monoid under a homomorphism.  This is the usual formulation of Definition
`def:rational-recognisable-subsets`: the congruence of finite index and the finite monoid are the
same datum, seen through the quotient map. -/
theorem isRecognisableSubset_iff_exists_hom {M : Type u} [Monoid M] (L : Set M) :
    IsRecognisableSubset L ↔
      ∃ (N : Type u) (_ : Monoid N) (_ : Finite N) (φ : M →* N) (S : Set N), L = φ ⁻¹' S := by
  constructor
  · rintro ⟨c, hfin, S, -, rfl⟩
    exact ⟨c.Quotient, inferInstance, hfin, c.mk', S, rfl⟩
  · rintro ⟨N, _, _, φ, S, rfl⟩
    have hfin : Finite (Con.ker φ).Quotient :=
      Finite.of_injective (Con.kerLift φ) (Con.kerLift_injective φ)
    refine ⟨Con.ker φ, hfin, (Con.kerLift φ) ⁻¹' S, Set.toFinite _, ?_⟩
    ext m
    simp [Con.kerLift]

/-- In a finite monoid every subset is recognisable. -/
theorem isRecognisableSubset_of_finite {M : Type*} [Monoid M] [Finite M] (L : Set M) :
    IsRecognisableSubset L :=
  (isRecognisableSubset_iff_exists_hom L).2
    ⟨M, inferInstance, inferInstance, MonoidHom.id M, L, rfl⟩

/-- In a finite monoid every subset is rational, being finite. -/
theorem isRationalSubset_of_finite {M : Type*} [Monoid M] [Finite M] (L : Set M) :
    IsRationalSubset L :=
  .finite L.toFinite

end MonoidSubsets

/-! ### Composition and continuity -/

/-- **Theorem `thm:composition-rational-relations`.**  Rational relations are closed under
relational composition. -/
theorem rationalRel_comp {A B C : Type}
    {R : List A → List B → Prop} {S : List B → List C → Prop}
    (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => ∃ u, R w u ∧ S u v) :=
  rationalRel_comp_aux hR hS

/-- **Theorem `thm:continuity-rational-relations`.**  The inverse image of a regular language under
a rational relation is regular; that is, rational relations are continuous. -/
theorem rationalRel_continuous {A B : Type}
    {R : List A → List B → Prop} (hR : IsRationalRel R) : RelContinuous R :=
  rationalRel_continuous_aux hR

/-! ### Undecidable equivalence

Decidability statements are formalised by means of Mathlib's notion of a
computable function.  A rational relation over the alphabet `ℕ` (every relation
over a finite alphabet can be presented this way) is described by a *code*: a
finite list of transitions together with the lists of initial and final
states. -/

/-! The code of an automaton (`RelCode`), the automaton and the relation that it
describes (`codeAut`, `codeRel`), the promise that this relation is a function
(`CodeFunctional`, totality on the strings over the alphabet of the code: see
`not_codeTotalFunctional` for why totality on all of `ℕ*` cannot be used) and
the formalisation of decidability under a promise
(`DecidableUnderPromise`) are defined in `RequestProject/PartB/Codes.lean`, so
that the reduction from the Post correspondence problem
(`RequestProject/PartB/PCPRed.lean`) can be developed before the statements of
the numbered results. -/

/-- **Theorem `thm:undecidable-equivalence-rational-relations`.**  The equivalence problem `R = S`
is undecidable for rational relations.

As is customary, undecidability is proved by a reduction from the Post
correspondence problem, whose undecidability is *not* proved here but is taken
as the explicit hypothesis `hPCP`: no algorithm decides, given a finite list of
pairs of strings, whether some nonempty sequence of indices makes the two
concatenations equal (`Transducers.PCP.Solvable`). -/
theorem rationalRel_equivalence_undecidable
    (hPCP : ¬ ComputablePred PCP.Solvable) :
    ¬ ComputablePred (fun p : RelCode × RelCode => codeRel p.1 = codeRel p.2) :=
  PCP.equivalence_undecidable hPCP

/-- **Claim `claim:homomorphism-complement-rational`.**  If `h : A* → B*` is a homomorphism, then
its complement `{(w, v) | v ≠ h w}` is a rational relation. -/
theorem hom_complement_rational {A B : Type} [Finite A] [Finite B] (φ : A → List B) :
    IsRationalRel (fun (w : List A) (v : List B) => v ≠ homOf φ w) :=
  hom_complement_rational_aux φ

/-! ## Rational functions -/

/-! ### Bimachines -/

/-! **Definition `def:bimachine` (Bimachine).**  The definition of a bimachine
(`Bimachine`), of its semantics (`Bimachine.eval`) and of the functions that
bimachines compute (`IsBimachine`, `IsAperiodicBimachine`) is in
`RequestProject/PartB/Bimachine.lean`, together with the proof that these functions are
rational. -/

/-- **Theorem `thm:bimachines`.**  For a string-to-string function the following are
equivalent: (1) it is a rational relation which happens to be functional;
(2) it is computed by an unambiguous nfa with output; (3) it is computed by a
bimachine. -/
theorem rational_iff_unambiguous_iff_bimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    [IsRationalFun f,
     IsUnambiguousRel (fun w v => v = f w),
     IsBimachine f].TFAE := by
  tfae_have 1 → 2 := by
    intro hf
    obtain ⟨P, hP, N, hunamb, -, hrel⟩ := exists_unambiguous_aut_of_rationalFun hf
    exact ⟨P, hP, N, hunamb, fun w v => (hrel w v).symm⟩
  tfae_have 2 → 1 := by
    rintro ⟨P, hP, N, -, hrel⟩
    exact ⟨P, hP, N, hrel⟩
  tfae_have 1 → 3 := isBimachine_of_rationalFun
  tfae_have 3 → 1 := rationalFun_of_isBimachine
  tfae_finish

/-- An automaton with *extended transitions*: transitions are labelled by an input string and a
regular language of output strings (used in Lemma `lemma:eliminate-epsilon-transitions`). -/
def IsExtendedNFAO {A B Q : Type} (M : LabAut A (Language B) Q) : Prop :=
  ∀ t ∈ M.δ, Language.IsRegular t.2.2.1

/-- The relation computed by an automaton with extended transitions: the output
is any string in the concatenation of the languages along an accepting path. -/
def extRel {A B Q : Type} (M : LabAut A (Language B) Q) (w : List A) (v : List B) : Prop :=
  ∃ ts, M.Accepting ts ∧ LabAut.inputOf ts = w ∧ v ∈ (LabAut.labelsOf ts).prod

/-- The normal form of Lemma `lemma:eliminate-epsilon-transitions`: in every accepting run, either
the input is nonempty and each transition inputs exactly one letter, or the input is empty and the
run consists of exactly one transition. -/
def EpsilonFree {A L Q : Type} (M : LabAut A L Q) : Prop :=
  ∀ ts, M.Accepting ts →
    (LabAut.inputOf ts ≠ [] → ∀ t ∈ ts, t.2.1.length = 1) ∧
    (LabAut.inputOf ts = [] → ts.length = 1)

/-- **Lemma `lemma:eliminate-epsilon-transitions` (Elimination of ε-transitions).**  Every rational
relation can be computed by an nfa with output and extended transitions in which every accepting run
is in the normal form described by `EpsilonFree`.  Furthermore, if every input string has finitely
many outputs, then extended transitions are not needed. -/
theorem epsilon_elimination {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) :
    (∃ (Q : Type) (_ : Finite Q) (M : LabAut A (Language B) Q),
        IsExtendedNFAO M ∧ EpsilonFree M ∧ ∀ w v, R w v ↔ extRel M w v) ∧
      ((∀ w, {v | R w v}.Finite) →
        ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
          EpsilonFree M ∧ ∀ w v, R w v ↔ M.rel w v) :=
  epsilon_elimination_aux hR

/-- **Lemma `lem:uniformisation` (Uniformisation).**  If a rational relation is total, then it
contains an unambiguous rational relation. -/
theorem uniformisation {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsRationalRel R) (htotal : ∀ w, ∃ v, R w v) :
    ∃ S : List A → List B → Prop, (∀ w v, S w v → R w v) ∧ IsUnambiguousRel S :=
  uniformisation_aux hR htotal

/-! ### Decomposition into primes -/

/-! The family of **prime rational functions** `PrimeRationalFam`
(Theorem `thm:rational-primes`) — prime Mealy machines, their right-to-left variants, string
homomorphisms, and the function `w ↦ w#` appending a fresh separator — is
defined in `RequestProject/PartB/PrimeRat.lean`. -/

/-- **Theorem `thm:rational-primes`.**  A string-to-string function is rational if and only if
it can be obtained by composing prime rational functions. -/
theorem rational_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) :
    IsRationalFun f ↔ CompClosure PrimeRationalFam A B f := by
  constructor
  · intro hf
    exact compClosure_of_isBimachine (isBimachine_of_rationalFun hf)
  · intro hf
    exact PrimeRat.rationalFun_of_compClosure hf inferInstance inferInstance

/-! ### Mealy machines as a subset of the rational functions -/

/-- A rational function is continuous, by Theorem `thm:continuity-rational-relations`. -/
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
Theorem `thm:rational-is-mealy-characterisation` implies prefix preservation. -/
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

/-- **Theorem `thm:rational-is-mealy-characterisation`.**  A rational function is computed by a
Mealy machine if and only if it is length preserving and deterministic in the sense that input
strings agreeing on the first `n` letters have outputs agreeing on the first `n` letters. -/
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
