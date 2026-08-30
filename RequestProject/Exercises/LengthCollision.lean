/-
Item (b) of Exercise `exer:decide-rational-colision` of the chapter on rational functions
(`rational-functions.tex`) of *Transducers* (M. Bojańczyk): given two rational functions, is
there some input string on which the two outputs have the same length?

The author's solution is: the pairs

  `(|f(w)|, |g(w)|)`   for `w ∈ A*`

form the Parikh image of a regular language -- the language of runs of the product of the two
transducers -- hence a *semilinear* subset of `ℕ × ℕ`, which can be computed; it remains to check
whether that set contains a pair with two equal coordinates.

This file follows that solution.  The second half of it -- the check -- is proved here in full:
a semilinear set is given by finitely many pairs `(base, periods)`, a point of one of them lies
on the diagonal exactly when the differences of the periods generate the difference of the base
coordinates as a nonnegative integer combination, and that membership problem is decided in
`RequestProject/Exercises/IntComb.lean`.  The decision procedure is
`Transducers.Exercises.meetsDiag`, and `Transducers.Exercises.meetsDiag_eq_true_iff` proves it
correct.

The first half -- Parikh's theorem, and the computation of a semilinear description of the length
pairs from two codes -- is not available in this project, which has no semilinear sets and no
Parikh images; it is taken as the explicit hypothesis
`Transducers.Exercises.EffectiveLengthPairsSemilinear`, in the style used by the other
decidability statements of the project.

A second hypothesis, `Transducers.Exercises.ComputableDiagonalTest`, says that the concrete
decision procedure `meetsDiag` defined here is `Computable` in the sense of Mathlib.  It is a
plain total recursive Lean function on a `Primcodable` type -- it is defined by structural
recursion and it runs -- but its correctness proof passes through arithmetic on `ℤ`, and, as
`RequestProject/PartB/Effective.lean` records for the decidability results of Part B, Mathlib's
`Primrec`/`Computable` API has no arithmetic on `ℤ`, so the predicate `Computable` cannot yet be
established for it inside the library.  The hypothesis is stated separately so that exactly this
gap, and nothing else, is what the result rests on besides Parikh's theorem.

Item (a) of the exercise -- the undecidability of the existence of an input with *equal* outputs --
is `Transducers.Exercises.rationalFun_collision_undecidable`, in
`RequestProject/Exercises/PartBC.lean`.
-/
import RequestProject.Exercises.IntComb
import RequestProject.PartB.Codes

namespace Transducers
namespace Exercises

open Transducers.Exercises.IntComb

/-! ## Semilinear sets of pairs -/

/-- A linear set of pairs, given by a base point and a finite list of periods. -/
abbrev LinPair : Type := (ℕ × ℕ) × List (ℕ × ℕ)

/-- The value `Σ nᵢ pᵢ` of the coefficients `ns` against the periods `ps`.  Missing coefficients
count as zero. -/
def pairCombVal : List (ℕ × ℕ) → List ℕ → ℕ × ℕ
  | [], _ => (0, 0)
  | _, [] => (0, 0)
  | p :: ps, n :: ns => (n * p.1 + (pairCombVal ps ns).1, n * p.2 + (pairCombVal ps ns).2)

@[simp] lemma pairCombVal_nil_left (ns : List ℕ) : pairCombVal [] ns = (0, 0) := by
  cases ns <;> rfl

@[simp] lemma pairCombVal_nil_right (ps : List (ℕ × ℕ)) : pairCombVal ps [] = (0, 0) := by
  cases ps <;> rfl

@[simp] lemma pairCombVal_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) (n : ℕ) (ns : List ℕ) :
    pairCombVal (p :: ps) (n :: ns)
      = (n * p.1 + (pairCombVal ps ns).1, n * p.2 + (pairCombVal ps ns).2) := rfl

/-- The linear set with base `l.1` and periods `l.2`. -/
def linPairSet (l : LinPair) : Set (ℕ × ℕ) :=
  {x | ∃ ns : List ℕ, x = (l.1.1 + (pairCombVal l.2 ns).1, l.1.2 + (pairCombVal l.2 ns).2)}

/-- A semilinear set of pairs: a finite union of linear sets. -/
def semiPairSet (S : List LinPair) : Set (ℕ × ℕ) := {x | ∃ l ∈ S, x ∈ linPairSet l}

/-! ## The diagonal test -/

/-- The difference of the coordinates of a value of the periods is the value of the differences
of the periods. -/
lemma pairCombVal_sub : ∀ (ps : List (ℕ × ℕ)) (ns : List ℕ),
    ((pairCombVal ps ns).1 : ℤ) - (pairCombVal ps ns).2
      = combVal (ps.map (fun p => (p.1 : ℤ) - p.2)) ns := by
  intro ps
  induction ps with
  | nil => intro ns; simp
  | cons p ps ih =>
      intro ns
      cases ns with
      | nil => simp
      | cons n ns =>
          have h := ih ns
          simp only [List.map_cons, pairCombVal_cons, combVal_cons]
          push_cast
          push_cast at h
          linarith [h]

/-- **The decision procedure for one linear set**: it contains a point on the diagonal exactly
when the differences of its periods generate the difference of the coordinates of its base. -/
def diagLin (l : LinPair) : Bool :=
  meetsZ (l.2.map (fun p => (p.1 : ℤ) - p.2)) ((l.1.2 : ℤ) - l.1.1)

lemma diagLin_eq_true_iff (l : LinPair) :
    diagLin l = true ↔ ∃ x ∈ linPairSet l, x.1 = x.2 := by
  rw [diagLin, meetsZ_eq_true_iff]
  constructor
  · rintro ⟨ns, hns⟩
    refine ⟨_, ⟨ns, rfl⟩, ?_⟩
    have h := pairCombVal_sub l.2 ns
    rw [hns] at h
    omega
  · rintro ⟨x, ⟨ns, rfl⟩, hx⟩
    refine ⟨ns, ?_⟩
    have h := pairCombVal_sub l.2 ns
    simp only at hx
    omega

/-- **The decision procedure of the exercise**: whether a semilinear set of pairs contains a pair
with two equal coordinates. -/
def meetsDiag (S : List LinPair) : Bool := S.any diagLin

/-- **The decision procedure is correct.** -/
theorem meetsDiag_eq_true_iff (S : List LinPair) :
    meetsDiag S = true ↔ ∃ x ∈ semiPairSet S, x.1 = x.2 := by
  rw [meetsDiag, List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hd⟩
    obtain ⟨x, hx, hxd⟩ := (diagLin_eq_true_iff l).1 hd
    exact ⟨x, ⟨l, hl, hx⟩, hxd⟩
  · rintro ⟨x, ⟨l, hl, hx⟩, hxd⟩
    exact ⟨l, hl, (diagLin_eq_true_iff l).2 ⟨x, hx, hxd⟩⟩

/-! ## The decision problem of the exercise -/

/-- The set of pairs of output lengths of the two relations described by two codes. -/
def lengthPairs (c₁ c₂ : RelCode) : Set (ℕ × ℕ) :=
  {x | ∃ w v u, codeRel c₁ w v ∧ codeRel c₂ w u ∧ x = (v.length, u.length)}

/-- **Hypothesis (Parikh's theorem, effectively).**  There is a computable function which, given
two codes describing rational *functions*, returns a semilinear description of the set of pairs
of output lengths of the two functions.

This is the first half of the author's solution: the pairs `(|f(w)|, |g(w)|)` form the Parikh
image of the language of runs of the product of the two transducers, hence a semilinear set,
which can be computed from the transducers.  Neither Parikh images nor semilinear sets are
developed in this project. -/
def EffectiveLengthPairsSemilinear : Prop :=
  ∃ F : RelCode × RelCode → List LinPair, Computable F ∧
    ∀ p : RelCode × RelCode, CodeFunctional p.1 → CodeFunctional p.2 →
      semiPairSet (F p) = lengthPairs p.1 p.2

/-- **Hypothesis (a `Computable` label for a concrete procedure).**  The decision procedure
`Transducers.Exercises.meetsDiag`, which is defined here by structural recursion and computes, is
`Computable` in the sense of Mathlib.  It is stated as a hypothesis only because Mathlib's
`Primrec`/`Computable` API has no arithmetic on `ℤ`, exactly as recorded in
`RequestProject/PartB/Effective.lean` for the decision procedures of Part B. -/
def ComputableDiagonalTest : Prop := Computable meetsDiag

/-- **Exercise `exer:decide-rational-colision`, item (b).**  It is decidable whether two rational
functions have outputs of the same length on some input.

As for item (a) and for the numbered results of Part B, a decision problem about rational
functions is a problem about their finite descriptions, the codes `Transducers.RelCode`, under
the promise that they describe functions (`Transducers.CodeFunctional`).

The mathematical step of the solution that the project can carry out -- deciding whether a
semilinear set of pairs meets the diagonal -- is proved in full above; the two hypotheses are the
effective form of Parikh's theorem and the `Computable` label for the concrete procedure, both
described in the header of this file. -/
theorem rationalFun_equal_length_decidable (hpar : EffectiveLengthPairsSemilinear)
    (hdec : ComputableDiagonalTest) :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => ∃ w v u, codeRel p.1 w v ∧ codeRel p.2 w u ∧ v.length = u.length) := by
  obtain ⟨F, hFcomp, hFsem⟩ := hpar
  refine ⟨fun p => meetsDiag (F p), hdec.comp hFcomp, ?_⟩
  rintro p ⟨h1, h2⟩
  rw [meetsDiag_eq_true_iff, hFsem p h1 h2]
  constructor
  · rintro ⟨x, ⟨w, v, u, hv, hu, rfl⟩, hx⟩
    exact ⟨w, v, u, hv, hu, hx⟩
  · rintro ⟨w, v, u, hv, hu, hlen⟩
    exact ⟨(v.length, u.length), ⟨w, v, u, hv, hu, rfl⟩, hlen⟩

end Exercises
end Transducers
