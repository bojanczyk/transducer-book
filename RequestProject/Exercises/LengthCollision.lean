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

That the concrete procedure `meetsDiag` is `Computable` in the sense of Mathlib is proved here,
as `Transducers.Exercises.ComputableDiagonalTest`; it used to be an explicit hypothesis, because
Mathlib's `Primrec`/`Computable` API has no arithmetic on `ℤ`.  That arithmetic is now supplied
by `RequestProject/Common/PrimrecArith.lean` (a general-purpose file, about `ℤ` and `ℚ` and not
about transducers), and the procedure itself is shown primitive recursive in
`RequestProject/Exercises/IntCombPrimrec.lean`.  So the only thing the result still rests on is
Parikh's theorem.

Item (a) of the exercise -- the undecidability of the existence of an input with *equal* outputs --
is `Transducers.Exercises.rationalFun_collision_undecidable`, in
`RequestProject/Exercises/PartBC.lean`.
-/
import RequestProject.Exercises.IntCombPrimrec
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

open Primrec in
/-- The test for one linear set is primitive recursive. -/
theorem primrec_diagLin : Primrec diagLin := by
  have hmap : Primrec fun l : LinPair => l.2.map (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2) :=
    Primrec.list_map snd (int_subNat.comp (fst.comp snd) (snd.comp snd)).to₂
  have hc : Primrec fun l : LinPair => ((l.1.2 : ℤ) - l.1.1) :=
    int_subNat.comp (snd.comp fst) (fst.comp fst)
  exact primrec_meetsZ.comp hmap hc

open Primrec in
/-- The diagonal test is primitive recursive. -/
theorem primrec_meetsDiag : Primrec meetsDiag := by
  have h : PrimrecPred fun S : List LinPair => ∃ l ∈ S, diagLin l = true :=
    PrimrecPred.exists_mem_list (p := fun l : LinPair => diagLin l = true)
      (PrimrecRel.comp (Primrec.eq (α := Bool)) primrec_diagLin (const true))
  refine h.decide.of_eq fun S => ?_
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, meetsDiag, List.any_eq_true]

/-- **A `Computable` label for the concrete procedure.**  The decision procedure
`Transducers.Exercises.meetsDiag` is `Computable` in the sense of Mathlib.

This was once an explicit hypothesis, because Mathlib's `Primrec`/`Computable` API has no
arithmetic on `ℤ`.  It is now a theorem: the missing arithmetic is developed in the
general-purpose file `RequestProject/Common/PrimrecArith.lean`, and the procedure is shown
primitive recursive in `RequestProject/Exercises/IntCombPrimrec.lean`. -/
theorem ComputableDiagonalTest : Computable meetsDiag := primrec_meetsDiag.to_comp

/-- **Exercise `exer:decide-rational-colision`, item (b).**  It is decidable whether two rational
functions have outputs of the same length on some input.

As for item (a) and for the numbered results of Part B, a decision problem about rational
functions is a problem about their finite descriptions, the codes `Transducers.RelCode`, under
the promise that they describe functions (`Transducers.CodeFunctional`).

The mathematical step of the solution that the project can carry out -- deciding whether a
semilinear set of pairs meets the diagonal, and the computability of that decision -- is proved
in full above; the one remaining hypothesis is the effective form of Parikh's theorem, described
in the header of this file. -/
theorem rationalFun_equal_length_decidable (hpar : EffectiveLengthPairsSemilinear) :
    DecidableUnderPromise (fun p : RelCode × RelCode => CodeFunctional p.1 ∧ CodeFunctional p.2)
      (fun p => ∃ w v u, codeRel p.1 w v ∧ codeRel p.2 w u ∧ v.length = u.length) := by
  obtain ⟨F, hFcomp, hFsem⟩ := hpar
  refine ⟨fun p => meetsDiag (F p), ComputableDiagonalTest.comp hFcomp, ?_⟩
  rintro p ⟨h1, h2⟩
  rw [meetsDiag_eq_true_iff, hFsem p h1 h2]
  constructor
  · rintro ⟨x, ⟨w, v, u, hv, hu, rfl⟩, hx⟩
    exact ⟨w, v, u, hv, hu, hx⟩
  · rintro ⟨w, v, u, hv, hu, hlen⟩
    exact ⟨(v.length, u.length), ⟨w, v, u, hv, hu, rfl⟩, hlen⟩

end Exercises
end Transducers
