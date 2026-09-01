/-
Exercise `exer:fo-non-elementary` of the chapter on logic (`logic.tex`) of
*Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.FONonElemTop

/-!
# First-order formulas of polynomial size define non-elementary long strings

Exercise `exer:fo-non-elementary` asks to show that for every `n` there is a
first-order formula of size polynomial in `n` whose language consists of exactly
one string, of length at least the tower of exponentials

  `exp 1 = 1`,  `exp (n+1) = 2 ^ exp n`.

The solution defines the *strings of order `n`*: the only string of order `0` is
empty, and, if `w₁, …, w_ℓ` are the strings of order `n` in lexicographic order,
then the strings of order `n+1` are the strings `a₁ w₁ ⋯ a_ℓ w_ℓ` with
`aᵢ ∈ {0,1}`, over the alphabet extended by two fresh letters.  It then proves a
Claim: the *first* string of order `n` is defined by a first-order formula of
size polynomial in `n`, obtained by induction, where the size is kept polynomial
by quantifying over the arguments of the formula for order `n-1` instead of
writing several copies of it.

The Claim is proved here, as `Transducers.Exercises.FirstStringOfOrderDefinable`.
The construction is spread over the files

* `RequestProject/Exercises/FONonElemOrder.lean` (the strings of order `n`),
* `RequestProject/Exercises/FONonElemParse.lean` (their block structure),
* `RequestProject/Exercises/FONonElemCore.lean` (the induction step, combinatorially),
* `RequestProject/Exercises/FONonElemDSL.lean` (the elementary first-order formulas),
* `RequestProject/Exercises/FONonElemForm.lean` (the formula `phiOrd N k` of the Claim),
* `RequestProject/Exercises/FONonElemTop.lean` (the sentence `fTop N k`).

Two conventions were fixed along the way and are recorded here.

* The strings of order `n` are indexed by the natural numbers below `numOrder n`,
  and "consecutive in the lexicographic order" is rendered as "with consecutive
  indices".  The index of a string of order `n+1` is read off the bits of its
  markers, most significant bit last, so this is the order in which the strings
  are enumerated by the construction.
* The two infixes that the formula `phiOrd N k` speaks about are given by their
  endpoints in the left-exclusive form `(x₁, x₂]`.  The sentence `fTop N k` has
  to speak about the whole string, whose first position is `0`, so the block
  structure is repeated there in the left-inclusive form.

What the exercise derives from the Claim, namely that a string of order `n` is
at least `exp n` long, is `Transducers.Exercises.expTower_le_lenOrder`.
-/

namespace Transducers.Exercises

open Transducers

/-! ## The two small cases -/

/-- The sentence saying that the string is empty. -/
def fEmptyS : MSO (Lett 0) := .not (.exFO 0 (MSO.le 0 0))

lemma sat_fEmptyS {u : List (Lett 0)} {fo : ℕ → ℕ} {so : ℕ → Set ℕ} :
    MSO.Sat u fo so fEmptyS ↔ u = [] := by
  simp only [fEmptyS, MSO.Sat, le_refl, and_true, not_exists, not_lt]
  constructor
  · intro h
    exact List.length_eq_zero_iff.1 (Nat.le_zero.1 (h 0))
  · rintro rfl
    simp

/-- The single letter of the one-letter string of order `1`. -/
def lettOne : Lett 1 := (lv 1 1, false)

/-- The sentence saying that the string is the one-letter string of order `1`. -/
def fOneS : MSO (Lett 1) :=
  .and (.exFO 0 (.lab lettOne 0)) (.not (.exFO 0 (.exFO 1 (fLtV 0 1))))

lemma sat_fOneS {u : List (Lett 1)} {fo : ℕ → ℕ} {so : ℕ → Set ℕ} :
    MSO.Sat u fo so fOneS ↔ u = [lettOne] := by
  simp only [fOneS, MSO.Sat, sat_fLtV, Function.update_self,
    Function.update_of_ne (show (0 : ℕ) ≠ 1 by decide)]
  constructor
  · rintro ⟨⟨p, hp, hlab⟩, hno⟩
    have hlen : u.length ≤ 1 := by
      by_contra hc
      exact hno ⟨0, by omega, 1, by omega, by omega⟩
    have hp0 : p = 0 := by omega
    subst hp0
    have h1 : u.length = 1 := by omega
    obtain ⟨a, rfl⟩ : ∃ a, u = [a] := by
      match u, h1 with
      | [a], _ => exact ⟨a, rfl⟩
    simpa using hlab
  · rintro rfl
    refine ⟨⟨0, by simp, by simp⟩, ?_⟩
    rintro ⟨x, hx, y, hy, hxy⟩
    simp only [List.length_singleton] at hx hy
    omega

/-! ## The Claim -/

/-- The polynomial bounding the size of the sentences below. -/
def sizeBound (n : ℕ) : ℕ := 363 + 943 * n

lemma polyBounded_sizeBound : PolyBounded sizeBound := by
  refine ⟨1306, 1, fun n => ?_⟩
  simp only [sizeBound, pow_one]
  omega

/-- **The Claim in the solution of `exer:fo-non-elementary`.**

For every `n` there is a first-order formula of size polynomial in `n` which holds in exactly one
string, the first string of order `n`, whose length is `lenOrder n`.

For `n ≥ 2` the sentence is `fTop n (n-1)`, whose unique model is `ordStr n n 0`
(`Transducers.Exercises.sat_fTop`); the cases `n = 0` and `n = 1`, where the string of order `n`
is too short for the two positions that the construction needs, are handled by the ad hoc
sentences `fEmptyS` and `fOneS`. -/
theorem FirstStringOfOrderDefinable :
    ∃ p : ℕ → ℕ, PolyBounded p ∧
      ∀ n : ℕ, ∃ (A : Type) (_ : Finite A) (φ : MSO A) (w : List A),
        φ.IsFO ∧ fsize φ ≤ p n ∧ w.length = lenOrder n ∧
        ∀ (u : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat u fo so φ ↔ u = w := by
  refine ⟨sizeBound, polyBounded_sizeBound, fun n => ?_⟩
  match n with
  | 0 =>
      exact ⟨Lett 0, inferInstance, fEmptyS, [], by simp [fEmptyS, MSO.IsFO],
        by simp [fEmptyS, fsize, sizeBound], rfl, fun u fo so => sat_fEmptyS⟩
  | 1 =>
      refine ⟨Lett 1, inferInstance, fOneS, [lettOne], ?_, ?_, rfl, fun u fo so => sat_fOneS⟩
      · simp [fOneS, MSO.IsFO, fLtV]
      · simp [fOneS, fsize, fLtV, sizeBound]
  | (k + 2) =>
      refine ⟨Lett (k + 2), inferInstance, fTop (k + 2) (k + 1), ordStr (k + 2) (k + 2) 0,
        isFO_fTop _ _, ?_, ordStr_length _ _ _, fun u fo so => sat_fTop (by omega) (by omega)⟩
      rw [fsize_fTop]
      simp only [sizeBound]
      omega

/-- The sentence produced by the Claim is **satisfiable**: the string it defines is a model of it.
Together with `FirstStringOfOrderDefinable`, which says that it has at most one model, this says
that its language is exactly one string, and in particular that the statement of the exercise is
not vacuous. -/
theorem exists_model_of_firstStringOfOrder (n : ℕ) :
    ∃ (A : Type) (_ : Finite A) (φ : MSO A) (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat w fo so φ ∧ w.length = lenOrder n ∧
        ∀ (u : List A) (fo' : ℕ → ℕ) (so' : ℕ → Set ℕ), MSO.Sat u fo' so' φ ↔ u = w := by
  obtain ⟨p, -, hclaim⟩ := FirstStringOfOrderDefinable
  obtain ⟨A, hA, φ, w, -, -, hlen, hsat⟩ := hclaim n
  exact ⟨A, hA, φ, w, fun _ => 0, fun _ => ∅, (hsat w _ _).2 rfl, hlen, hsat⟩

/-! ## The exercise -/

/-- **Exercise `exer:fo-non-elementary`.**  For every `n` there is a first-order formula of size
polynomial in `n` whose language contains exactly one string, and that string has length at least
`exp n`.

The Claim of the book's solution is `FirstStringOfOrderDefinable`; the step from the Claim to the
statement of the exercise is that a string of order `n` is at least `exp n` long. -/
theorem fo_non_elementary :
    ∃ p : ℕ → ℕ, PolyBounded p ∧
      ∀ n : ℕ, ∃ (A : Type) (_ : Finite A) (φ : MSO A) (w : List A),
        φ.IsFO ∧ fsize φ ≤ p n ∧ expTower n ≤ w.length ∧
        ∀ (u : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat u fo so φ ↔ u = w := by
  obtain ⟨p, hp, hclaim⟩ := FirstStringOfOrderDefinable
  refine ⟨p, hp, fun n => ?_⟩
  obtain ⟨A, hA, φ, w, hfo, hsize, hlen, hsat⟩ := hclaim n
  exact ⟨A, hA, φ, w, hfo, hsize, by rw [hlen]; exact expTower_le_lenOrder n, hsat⟩

end Transducers.Exercises
