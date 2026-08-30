/-
Exercise `exer:for-transducer-continuity-nonelementary` of the chapter
*For-transducers* (`polyregular-for.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.ForFO
import RequestProject.Exercises.FONonElementary
import RequestProject.Exercises.NFAPump

/-!
# Computing the preimage of a for-transducer takes non-elementary time

Exercise `exer:for-transducer-continuity-nonelementary` asks to show that no algorithm running
in elementary time can solve the computational version of continuity for for-transducers, whose
input is the source code of a for-transducer `f` together with an nfa over its output alphabet,
and whose output is an nfa for the preimage of the language of that nfa.

The solution's reason is a *size* obstruction rather than a statement about running time: the
output nfa itself is already of non-elementary size, so no algorithm can print it in elementary
time.  Since this project has no model of running time, it is that size obstruction which is
formalised here, and it is the whole mathematical content of the solution:

> for every `n` there is a for-program `P` over some alphabet, of size polynomial in `n`, which
> outputs `yes` or `no` on every input, and such that *every* nfa recognising the preimage
> `{u | P.eval u = yes}` has more than `exp n` states,

where `exp` is the tower of exponentials `expTower` of `exer:fo-non-elementary`.  The nfa given
along with `P` to the hypothetical algorithm is the one-state nfa for the language `{yes}`, whose
preimage under the function computed by `P` is exactly `{u | P.eval u = yes}`; it is of constant
size, so the input of the algorithm has size polynomial in `n` while its output does not.

The proof is the one of the book, assembled from three ingredients that are already in the
project:

* `exer:fo-non-elementary` (`Transducers.Exercises.fo_non_elementary`): a first-order sentence
  `φ` of size polynomial in `n` whose language is a single string of length at least `exp n`.
  As there, this rests on the Claim `FirstStringOfOrderDefinable`, which the book leaves to the
  reader; it is the explicit hypothesis of the theorem below.
* `exer:for-transducers-simulate-fo`
  (`Transducers.Exercises.exists_forProg_of_isFO`): a for-program of size linear in `φ` which
  outputs `yes` or `no` according to whether `φ` holds.
* the pumping argument `Transducers.Exercises.nfa_card_gt_length_of_longest`: an nfa whose
  language contains a string of length `ℓ` and no longer string has more than `ℓ` states.
-/

namespace Transducers.Exercises

open Transducers

/-- A polynomial bound survives an affine change: if `q` is polynomially bounded then so is
`c * q + d`. -/
lemma PolyBounded.affine {q : ℕ → ℕ} (h : PolyBounded q) (c d : ℕ) :
    PolyBounded (fun n => c * q n + d) := by
  obtain ⟨C, e, hC⟩ := h
  refine ⟨c * C + d, e, fun n => ?_⟩
  have h1 : c * q n ≤ c * (C * (n + 1) ^ e) := Nat.mul_le_mul_left _ (hC n)
  have h2 : d ≤ d * (n + 1) ^ e := Nat.le_mul_of_pos_right d (pow_pos (Nat.succ_pos n) e)
  calc c * q n + d ≤ c * (C * (n + 1) ^ e) + d * (n + 1) ^ e := Nat.add_le_add h1 h2
    _ = (c * C + d) * (n + 1) ^ e := by ring

/-- **Exercise `exer:for-transducer-continuity-nonelementary`.**  For every `n` there is a
for-program of size polynomial in `n`, computing a function whose values are `yes` and `no`,
such that every nfa recognising the preimage of `{yes}` has more than `exp n` states.

Hence the computational version of continuity — from the source code of a for-transducer and an
nfa over its output alphabet, produce an nfa for the preimage — cannot be solved in elementary
time: on the input consisting of this program together with the one-state nfa for `{yes}`, whose
total size is polynomial in `n`, the output alone is of non-elementary size.

The hypothesis is the Claim of the solution of `exer:fo-non-elementary`,
`FirstStringOfOrderDefinable`; see its docstring. -/
theorem for_transducer_continuity_nonelementary (h : FirstStringOfOrderDefinable) :
    ∃ p : ℕ → ℕ, PolyBounded p ∧
      ∀ n : ℕ, ∃ (A : Type) (_ : Finite A) (P : ForProg A Bool),
        progSize P ≤ p n ∧
        (∀ u : List A, P.eval u = [true] ∨ P.eval u = [false]) ∧
        ∀ (Q : Type) (_ : Fintype Q) (M : NFA A Q),
          (∀ u : List A, u ∈ M.accepts ↔ P.eval u = [true]) →
            expTower n < Fintype.card Q := by
  obtain ⟨q, hq, hclaim⟩ := h
  refine ⟨fun n => 10 * q n + 5, hq.affine 10 5, fun n => ?_⟩
  obtain ⟨A, hA, φ, w, hfo, hsize, hlen, hsat⟩ := hclaim n
  obtain ⟨P, hbool, hiff, hps⟩ := exists_forProg_of_isFO φ hfo
  refine ⟨A, hA, P, ?_, hbool, ?_⟩
  · show progSize P ≤ 10 * q n + 5
    have : 10 * fsize φ ≤ 10 * q n := Nat.mul_le_mul_left _ hsize
    omega
  · intro Q hQ M hM
    have hwacc : w ∈ M.accepts := (hM w).2 ((hiff w).2 ((hsat w _ _).2 rfl))
    have hmax : ∀ u ∈ M.accepts, u.length ≤ w.length := by
      intro u hu
      have : u = w := (hsat u (fun _ => 0) (fun _ => ∅)).1 ((hiff u).1 ((hM u).1 hu))
      exact le_of_eq (by rw [this])
    have hcard : w.length < Fintype.card Q :=
      @nfa_card_gt_length_of_longest A Q hQ M w hwacc hmax
    have hexp : expTower n ≤ w.length := by rw [hlen]; exact expTower_le_lenOrder n
    exact lt_of_le_of_lt hexp hcard

end Transducers.Exercises
