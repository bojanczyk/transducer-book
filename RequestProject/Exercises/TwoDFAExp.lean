/-
Exercise `exer:2dfa-complexity` of the chapter *Two-way transducers* (`2dfa.tex`) of *Transducers*
(M. Bojańczyk): for languages recognised by deterministic two-way automata, the shortest accepted
string can be exponential in the number of states.

The construction of the author's solution does **not** prove this; the divergence is recorded in
`RequestProject/Exercises/TwoDFAComplexity.lean`, where that construction is formalised, and in
`EXERCISES.md`.  What is proved here is the *claim* of the exercise, by a construction that the book
does not give.

Fix `n`.  Over the alphabet `{0, 1, …, n}`, the *ruler word* `rul 0 n` — `0 1 0 2 0 1 0` for `n = 2`
— has length `2 ^ (n + 1) - 1`, and it is the unique word over that alphabet satisfying the `n + 1`
conditions of `RequestProject/Exercises/TwoDFARuler.lean`: for each level `j ≤ n`, among the letters
that are at least `j`, those equal to `j` and those larger than `j` alternate, beginning and ending
with `j`.  Each of these conditions is checked by a one-way automaton with three states, so all of
them together are checked by a two-way automaton that performs the `n + 1` passes one after another
(`RequestProject/Exercises/TwoDFAPass.lean`), with `4 * (n + 1)` states in total.  Its language is
the singleton `{rul 0 n}`, so its shortest — indeed its only — accepted string has length
`2 ^ (n + 1) - 1`, which is exponential in its number of states.

The alphabet grows with `n`, as it does in the author's solution the number of letters stays fixed
but the number of states does not; the measure of the exercise is the number of states, which is
what `exists_twoDFA_shortest_exponential` records.
-/
import RequestProject.Exercises.TwoDFAPass
import RequestProject.Exercises.TwoDFARuler

namespace Transducers
namespace Exercises

open Transducers Ruler

variable (n : ℕ)

/-! ## The automaton -/

/-- The `n + 1` passes: the `i`-th one checks the condition of level `i`. -/
def rulerFam : PassFam (Fin (n + 1)) PSt n where
  init := fun _ => .expJ
  tr := fun i a s => dstep (i : ℕ) (a : ℕ) s
  acc := fun _ s => decide (s = .expHi)

/-- **The automaton of Exercise `exer:2dfa-complexity`.**  Over the alphabet `{0, …, n}` it checks,
one level after another, the `n + 1` conditions that characterise the ruler word, rewinding to the
left end between two checks. -/
def rulerAut : TwoDFA (Fin (n + 1)) (PassSt PSt n) := passAut (rulerFam n)

@[simp] lemma card_pSt : Fintype.card PSt = 3 := rfl

/-- The automaton has `4 * (n + 1)` states: three per pass, plus one rewinding state per pass. -/
lemma card_rulerSt : Fintype.card (PassSt PSt n) = 4 * (n + 1) := by
  rw [card_passSt, card_pSt]
  ring

lemma passRun_rulerFam (i : Fin (n + 1)) (w : List (Fin (n + 1))) :
    passRun (rulerFam n) i w = dfold (i : ℕ) (w.map Fin.val) PSt.expJ := by
  show w.foldl (fun s a => (rulerFam n).tr i a s) ((rulerFam n).init i) = _
  rw [dfold, List.foldl_map]
  rfl

/-! ## Its language is the singleton of the ruler word -/

/-- **The automaton accepts exactly the ruler word.** -/
theorem rulerAut_accepts (w : List (Fin (n + 1))) :
    (rulerAut n).Accepts w ↔ w.map Fin.val = rul 0 n := by
  rw [rulerAut, passAut_accepts]
  have hacc : ∀ i : Fin (n + 1),
      ((rulerFam n).acc i (passRun (rulerFam n) i w) = true) ↔ Cond (i : ℕ) (w.map Fin.val) := by
    intro i
    rw [passRun_rulerFam]
    show (decide (dfold (i : ℕ) (w.map Fin.val) PSt.expJ = PSt.expHi) = true) ↔ _
    rw [decide_eq_true_iff]
    exact dfold_expJ_iff _ _
  constructor
  · rintro ⟨-, h⟩
    refine eq_rul_of_cond (n := n) ?_ ?_
    · intro a ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      omega
    · intro j hj
      have := (hacc ⟨j, by omega⟩).1 (h ⟨j, by omega⟩)
      simpa using this
  · intro h
    have hne : w ≠ [] := by
      rintro rfl
      simp at h
      exact rul_ne_nil 0 n h
    refine ⟨hne, fun i => ?_⟩
    rw [hacc i, h]
    exact cond_rul n (i : ℕ) (by omega)

/-! ## The ruler word as a word over the alphabet of the automaton -/

/-- The ruler word `rul 0 n`, as a word over the alphabet `Fin (n + 1)`. -/
def rulWord : List (Fin (n + 1)) := (rul 0 n).map (fun x => (⟨min x n, by omega⟩ : Fin (n + 1)))

@[simp] lemma rulWord_map : (rulWord n).map Fin.val = rul 0 n := by
  rw [rulWord, List.map_map]
  rw [show ((Fin.val ∘ fun x => (⟨min x n, by omega⟩ : Fin (n + 1)))) = fun x => min x n from rfl]
  rw [List.map_congr_left (g := id) (fun x hx => by
    have := (mem_rul 0 n hx).2
    simp; omega)]
  simp

@[simp] lemma length_rulWord : (rulWord n).length = 2 ^ (n + 1) - 1 := by
  have h := congrArg List.length (rulWord_map n)
  rw [List.length_map, length_rul] at h
  exact h

/-! ## The exercise -/

/-- **Exercise `exer:2dfa-complexity`.**  For every `n` there is a deterministic two-way automaton
with `4 * (n + 1)` states whose shortest accepted string has length `2 ^ (n + 1) - 1`: the length of
the shortest accepted string can be exponential in the number of states.

This is *not* the construction of the author's solution, which gives only a superpolynomial bound;
that construction is formalised in `RequestProject/Exercises/TwoDFAComplexity.lean` and the
divergence is documented there and in `EXERCISES.md`. -/
theorem exists_twoDFA_shortest_exponential (n : ℕ) :
    ∃ (A R : Type) (_ : Fintype A) (_ : Fintype R) (N : TwoDFA A R) (w : List A),
      Fintype.card R = 4 * (n + 1) ∧ N.Accepts w ∧ w.length = 2 ^ (n + 1) - 1 ∧
        ∀ v : List A, N.Accepts v → w.length ≤ v.length := by
  refine ⟨Fin (n + 1), PassSt PSt n, inferInstance, inferInstance, rulerAut n, rulWord n,
    card_rulerSt n, ?_, length_rulWord n, ?_⟩
  · rw [rulerAut_accepts, rulWord_map]
  · intro v hv
    rw [rulerAut_accepts] at hv
    have h1 := congrArg List.length hv
    have h2 := congrArg List.length (rulWord_map n)
    simp only [List.length_map] at h1 h2
    omega

end Exercises
end Transducers
