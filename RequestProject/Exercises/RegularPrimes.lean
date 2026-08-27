/-
The exercises of the chapter *Regular functions* (`regular-primes.tex`) of *Transducers*
(M. Bojańczyk) that were not part of the first pass.

The exercise `exer:two-letter-alphabet-suffices` of that chapter is formalised in
`RequestProject/Exercises/PartBC.lean`; this file adds `exer:not-semiring-continuous`.
Exercises are not numbered results of the book, so they are recorded in `EXERCISES.md`, and they
are referred to by their LaTeX label.
-/
import RequestProject.PartC.Statements
import RequestProject.PartB.WeightedStatements

namespace Transducers.Exercises

open Transducers

/-! ## Regular functions (`regular-primes.tex`) -/

/-! ### Exercise `exer:not-semiring-continuous` -/

/-- The homomorphism that erases the separators of a string over `A + 1`. -/
def dropSep (A : Type) : List (Option A) → List A :=
  homOf (fun x => match x with | none => [] | some a => [a])

lemma dropSep_map_some {A : Type} (w : List A) : dropSep A (w.map some) = w := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [dropSep, homOf] using ih

lemma isRationalFun_dropSep (A : Type) [Finite A] : IsRationalFun (dropSep A) :=
  isRationalFun_homOf _

/-- Map reverse over a two-letter alphabet is not a rational function, as soon as string reversal
is not one: reversal factors as the homomorphism `a ↦ a` into `(A + 1)*`, followed by map reverse,
followed by the homomorphism that erases the separators. -/
lemma not_isRationalFun_mapReverse
    (hrev : ¬ IsRationalFun (List.reverse : List Bool → List Bool)) :
    ¬ IsRationalFun (mapReverse Bool) := by
  intro hmr
  refine hrev ?_
  have h1 : IsRationalFun (fun w : List Bool => w.map (some : Bool → Option Bool)) :=
    isRationalFun_map _
  have h := isRationalFun_comp (isRationalFun_comp h1 hmr) (isRationalFun_dropSep Bool)
  have he : (fun w : List Bool => dropSep Bool (mapReverse Bool (w.map some)))
      = (List.reverse : List Bool → List Bool) := by
    funext w
    rw [mapReverse, mapLift_map_some, dropSep_map_some]
  rwa [he] at h

/-- **Exercise `exer:not-semiring-continuous`.**  Weighted automata over arbitrary semirings are
not closed under pre-composition with regular functions: there is a regular function `f`, a
semiring `S` and a weighted automaton `h` over `S` such that `h ∘ f` is not recognised by a
weighted automaton.

The proof is the author's.  By Theorem `thm:characterisation-rational-functions-weighted-automata`
(`Transducers.rational_iff_weighted_precomp`) a function has this closure property exactly when it
is rational, so it suffices to exhibit a regular function that is not rational; the author's
witness is string reversal, and the one used here is map reverse, which is one of the prime
regular functions.  That reversal is not rational is Example `ex:string-reversal-not-rational` of
the main text, which is not part of this formalisation; it is therefore taken here as the explicit
hypothesis `hrev`, exactly as in Exercise `exer:function-that-is-not-rational`
(`Transducers.Exercises.exists_not_isRationalFun_unary_compositions_rational`), and everything else
in the exercise is proved. -/
theorem exists_isRegularFun_not_weighted_precomp
    (hrev : ¬ IsRationalFun (List.reverse : List Bool → List Bool)) :
    ∃ f : List (Option Bool) → List (Option Bool), IsRegularFun f ∧
      ∃ (S : Type) (_ : Semiring S) (h : List (Option Bool) → S),
        IsWeighted h ∧ ¬ IsWeighted (h ∘ f) := by
  refine ⟨mapReverse Bool, isRegularFun_mapReverse Bool, ?_⟩
  have hnr := not_isRationalFun_mapReverse hrev
  rw [rational_iff_weighted_precomp] at hnr
  push_neg at hnr
  obtain ⟨S, hS, h, hh, hcomp⟩ := hnr
  exact ⟨S, hS, h, hh, hcomp⟩

end Transducers.Exercises
