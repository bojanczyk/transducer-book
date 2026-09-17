/-
Claim `lem:fo-non-elementary-order`, in the solution of Exercise `exer:fo-non-elementary` of the
chapter on logic (`logic.tex`) of *Transducers* (M. Bojańczyk).

The claim asks for a first-order formula `φ_n(x₁,x₂,y₁,y₂)` of size polynomial in `n` which says
that the infix from `x₁` to `x₂` and the infix from `y₁` to `y₂` are strings of order `n` and that
they are consecutive in the lexicographic order on the strings of order `n`.

Everything the claim needs was built for the exercise itself, in
`RequestProject/Exercises/FONonElem*.lean`, and nothing is reproved here:

* `Transducers.Exercises.phiOrd` is the formula of the induction.  It has six free position
  variables, the last two of which give a *mode*: according to whether the position `va k 4` is at
  most the position `va k 5`, the formula says that the two infixes are strings of order `k` with
  the *same* index or with *consecutive* indices.  The two modes have to be carried together,
  because the induction step needs both.  `Transducers.Exercises.sat_phiOrd` is its meaning and
  `Transducers.Exercises.fsize_phiOrd` its size, which grows by a constant at each step.
* `Transducers.Exercises.SuccBlk` is "the two infixes are strings of order `k` with consecutive
  indices", and `Transducers.Exercises.IsOrdAt` inside it is "the infix is the `m`-th string of
  order `k`".

What this file adds is the formula of the claim itself, with the four free variables that the book
writes: `Transducers.Exercises.phiOrdSucc` quantifies the two mode variables away, asking for two
positions in the mode "consecutive".  Two positions of the required kind exist as soon as the
string has two positions, which is why the statement carries the hypothesis `2 ≤ u.length` -- the
same hypothesis that `sat_phiOrd` carries.

Conventions.  An infix is read half-open, as `(x₁, x₂]`: the hypothesis `x₁ < x₂` of the book is
part of `IsOrdAt`, which asks for the infix from position `x₁ + 1` to position `x₂`.  "Consecutive
in the lexicographic order" is rendered as "with consecutive indices", the index of a string of
order `n` being the one fixed in `RequestProject/Exercises/FONonElemOrder.lean`; this is the
convention of the whole development of the exercise.
-/
import RequestProject.Exercises.FONonElemTop

namespace Transducers.Exercises

open Transducers

/-! ## The formula with the four free variables of the claim -/

/-- **The formula `φ_n(x₁,x₂,y₁,y₂)` of Claim `lem:fo-non-elementary-order`.**  The formula
`Transducers.Exercises.phiOrd` of the induction, with its two mode variables quantified
existentially in the mode "consecutive".  Its free position variables are `va k 0, …, va k 3`:
`x₁, x₂, y₁, y₂`. -/
def phiOrdSucc (N k : ℕ) : MSO (Lett N) :=
  MSO.exFO (va k 4) (MSO.exFO (va k 5)
    (.and (.not (MSO.le (va k 4) (va k 5))) (phiOrd N k)))

/-! ## What it says -/

/-- **Claim `lem:fo-non-elementary-order`, the meaning of the formula.**  In a string with at least
two positions, `phiOrdSucc N k` holds of `x₁, x₂, y₁, y₂` exactly when the infix `(x₁, x₂]` and the
infix `(y₁, y₂]` are strings of order `k` with consecutive indices. -/
theorem sat_phiOrdSucc {N : ℕ} {u : List (Lett N)} (hu : 2 ≤ u.length) {k : ℕ} (hk : k ≤ N)
    (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat u fo so (phiOrdSucc N k) ↔
      SuccBlk u k (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3)) := by
  constructor
  · rintro ⟨p, -, q, -, hne, hsat⟩
    rw [sat_phiOrd hu k hk] at hsat
    simp only [MSO.Sat, Function.update_apply, va_eq_va, Nat.succ_ne_self, and_false, if_false,
      Nat.reduceEqDiff, if_true] at hne hsat
    rcases hsat with ⟨he, -⟩ | ⟨-, hsucc⟩
    · exact absurd he hne
    · exact hsucc
  · intro hsucc
    refine ⟨1, by omega, 0, by omega, ?_, ?_⟩
    · simp only [MSO.Sat, Function.update_apply, va_eq_va, Nat.succ_ne_self, and_false, if_false,
        Nat.reduceEqDiff, if_true]
      omega
    · rw [sat_phiOrd hu k hk]
      simp only [Mean, Function.update_apply, va_eq_va, Nat.succ_ne_self, and_false, if_false,
        Nat.reduceEqDiff, if_true]
      exact Or.inr ⟨by omega, hsucc⟩

/-! ## Its size, and that it is first order -/

lemma isFO_phiOrdSucc (N k : ℕ) : (phiOrdSucc N k).IsFO := by
  simpa [phiOrdSucc, MSO.IsFO] using isFO_phiOrd N k

/-- **The formula of the claim has linear size.** -/
lemma fsize_phiOrdSucc (N k : ℕ) : fsize (phiOrdSucc N k) = 24 + 943 * k := by
  have h : fsize (phiOrdSucc N k) = fsize (phiOrd N k) + 5 := by
    simp only [phiOrdSucc, fsize]
    omega
  rw [h, fsize_phiOrd]
  omega

/-! ## The claim -/

/-- **Claim `lem:fo-non-elementary-order`.**  For every order `k` there is a first-order formula of
size polynomial in `k` -- in fact linear in `k` -- with four free position variables, which holds
of `x₁, x₂, y₁, y₂` exactly when the infixes `(x₁, x₂]` and `(y₁, y₂]` are strings of order `k`
that are consecutive in the lexicographic order on the strings of order `k`.

The formula is `Transducers.Exercises.phiOrdSucc`, and the free variables `x₁, x₂, y₁, y₂` are
`va k 0, va k 1, va k 2, va k 3`.  The alphabet is the one of the exercise, `Lett N` for any
`N ≥ k`, and the string is asked to have at least two positions, as in
`Transducers.Exercises.sat_phiOrd`. -/
theorem fo_non_elementary_order :
    ∃ p : ℕ → ℕ, PolyBounded p ∧
      ∀ N k : ℕ, k ≤ N → ∃ φ : MSO (Lett N), φ.IsFO ∧ fsize φ ≤ p k ∧
        ∀ (u : List (Lett N)) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), 2 ≤ u.length →
          (MSO.Sat u fo so φ ↔
            SuccBlk u k (fo (va k 0)) (fo (va k 1)) (fo (va k 2)) (fo (va k 3))) := by
  refine ⟨fun k => 24 + 943 * k, ⟨967, 1, fun n => by simp only [pow_one]; omega⟩,
    fun N k hk => ⟨phiOrdSucc N k, isFO_phiOrdSucc N k, le_of_eq (fsize_phiOrdSucc N k),
      fun u fo so hu => sat_phiOrdSucc hu hk fo so⟩⟩

end Transducers.Exercises
