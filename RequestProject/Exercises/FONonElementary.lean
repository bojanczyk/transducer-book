/-
Exercise `exer:fo-non-elementary` of the chapter on logic (`logic.tex`) of
*Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.ForFO

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
writing several copies of it.  The book leaves the details of that induction to
the reader.

Accordingly, the Claim is the explicit hypothesis
`Transducers.Exercises.FirstStringOfOrderDefinable` here.  What is proved is the
counting that turns the Claim into the statement of the exercise: the number of
strings of order `n` and their length satisfy

  `numOrder 0 = 1`,      `numOrder (n+1) = 2 ^ numOrder n`,
  `lenOrder 0 = 0`,      `lenOrder (n+1) = numOrder n * (1 + lenOrder n)`,

and a string of order `n` has length at least `exp n`
(`Transducers.Exercises.expTower_le_lenOrder`).
-/

namespace Transducers.Exercises

open Transducers

/-- A function of `ℕ` is bounded by a polynomial. -/
def PolyBounded (p : ℕ → ℕ) : Prop := ∃ C d : ℕ, ∀ n, p n ≤ C * (n + 1) ^ d

/-! ## The tower of exponentials and the strings of order `n` -/

/-- The tower of exponentials `exp` of the exercise: `exp 1 = 1` and `exp (n+1) = 2 ^ exp n`.
The value at `0` is irrelevant to the exercise and is set to `0`. -/
def expTower : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 ^ expTower (n + 1)

/-- The number of strings of order `n`: there is one string of order `0`, and a string of order
`n+1` is a choice of one bit in front of each string of order `n`. -/
def numOrder : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ numOrder n

/-- The length of a string of order `n`: a string of order `n+1` consists of one bit followed by
a string of order `n`, once for each string of order `n`. -/
def lenOrder : ℕ → ℕ
  | 0 => 0
  | n + 1 => numOrder n * (1 + lenOrder n)

lemma numOrder_eq_expTower (n : ℕ) : numOrder n = expTower (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [numOrder, ih]; rfl

lemma numOrder_pos (n : ℕ) : 0 < numOrder n := by
  cases n with
  | zero => norm_num [numOrder]
  | succ n => exact Nat.two_pow_pos _

/-- **A string of order `n` is at least `exp n` long.** -/
theorem expTower_le_lenOrder (n : ℕ) : expTower n ≤ lenOrder n := by
  cases n with
  | zero => simp [expTower, lenOrder]
  | succ n =>
      have h : numOrder n = expTower (n + 1) := numOrder_eq_expTower n
      calc expTower (n + 1) = numOrder n := h.symm
        _ ≤ numOrder n * (1 + lenOrder n) := Nat.le_mul_of_pos_right _ (by omega)
        _ = lenOrder (n + 1) := rfl

/-! ## The exercise -/

/-- **Assumed: the Claim in the solution of `exer:fo-non-elementary`.**

For every `n` there is a first-order formula of size polynomial in `n` which holds in exactly one
string, the first string of order `n`, whose length is `lenOrder n`.

*Why this is true.*  This is the Claim of the solution, whose proof the book sketches and whose
details it leaves to the reader.  The Claim is proved for the stronger statement about a formula
`φₙ (x₁, x₂, y₁, y₂)` saying that the two infixes marked by the pairs of positions are strings of
order `n` that are consecutive in the lexicographic order; the induction step uses `φₙ₋₁` to
match the sub-infixes of order `n-1` carrying the same index, and expresses that the bit
sequences of the two infixes are consecutive binary numbers.  The size stays polynomial by the
standard trick of applying a single copy of `φₙ₋₁` to universally quantified arguments, so that
the size grows by a constant at each step.

*Why it is not available here.*  The construction is an induction on `n` producing a formula
together with a proof of its correctness on the strings of order `n`, over an alphabet that grows
with `n`; the book itself leaves it to the reader, and it is the one genuinely combinatorial part
of the exercise.  What the exercise derives from the Claim — that the unique string of the
language is at least `exp n` long — is proved above. -/
def FirstStringOfOrderDefinable : Prop :=
  ∃ p : ℕ → ℕ, PolyBounded p ∧
    ∀ n : ℕ, ∃ (A : Type) (_ : Finite A) (φ : MSO A) (w : List A),
      φ.IsFO ∧ fsize φ ≤ p n ∧ w.length = lenOrder n ∧
      ∀ (u : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat u fo so φ ↔ u = w

/-- **Exercise `exer:fo-non-elementary`.**  For every `n` there is a first-order formula of size
polynomial in `n` whose language contains exactly one string, and that string has length at least
`exp n`.

The hypothesis is the Claim of the book's solution, `FirstStringOfOrderDefinable`; see its
docstring.  The step from the Claim to the statement of the exercise, namely that a string of
order `n` is at least `exp n` long, is proved. -/
theorem fo_non_elementary (h : FirstStringOfOrderDefinable) :
    ∃ p : ℕ → ℕ, PolyBounded p ∧
      ∀ n : ℕ, ∃ (A : Type) (_ : Finite A) (φ : MSO A) (w : List A),
        φ.IsFO ∧ fsize φ ≤ p n ∧ expTower n ≤ w.length ∧
        ∀ (u : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat u fo so φ ↔ u = w := by
  obtain ⟨p, hp, hclaim⟩ := h
  refine ⟨p, hp, fun n => ?_⟩
  obtain ⟨A, hA, φ, w, hfo, hsize, hlen, hsat⟩ := hclaim n
  exact ⟨A, hA, φ, w, hfo, hsize, by rw [hlen]; exact expTower_le_lenOrder n, hsat⟩

end Transducers.Exercises
