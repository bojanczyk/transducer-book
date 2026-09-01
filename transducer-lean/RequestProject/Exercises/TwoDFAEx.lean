/-
The exercises of the chapter on two-way automata (`2dfa.tex`) of *Transducers*
(M. Bojańczyk).
-/
import RequestProject.PartC.TwoDFA

/-!
# Boolean combinations of two-way automata

Exercise `exer:2dfa-boolean`: the languages recognised by deterministic two-way automata are
closed under union, intersection and complement.

The class is identified here with the regular languages.  One inclusion is Shepherdson's Theorem
`Transducers.TwoDFA.accepts_isRegular`, which is already in the project; the other is the
observation that a one-way deterministic automaton is a two-way automaton that only moves right,
`Transducers.Exercises.twoDFAOfDFA`.  Closure under the Boolean operations then follows from the
corresponding closure properties of the regular languages.

The exercise also asks for the *sizes* of the constructions to be polynomial in the sizes of the
given automata.  That part is not formalised: it is a statement about the number of states, and
the route taken here, through Shepherdson's Theorem, passes through the Myhill-Nerode
construction and gives no bound on the number of states.  The direct constructions of the book
are moreover not available for `Transducers.TwoDFA` as it is defined in this project, because a
run of a `TwoDFA` may fail to terminate and because a head that leaves the input string rejects
by definition; "swap the two answers", the book's construction for the complement, therefore does
not complement the language.
-/

namespace Transducers.Exercises

open Transducers

variable {A : Type}

/-- A language recognised by a deterministic two-way automaton. -/
def IsTwoDFALang (L : Language A) : Prop :=
  ∃ (R : Type) (_ : Finite R) (N : TwoDFA A R), ∀ w, N.Accepts w ↔ w ∈ L

open Classical in
/-- A one-way deterministic automaton, read as a two-way automaton that only moves right and
answers when the head reaches the right end of the input. -/
noncomputable def twoDFAOfDFA {σ : Type} (D : DFA A σ) : TwoDFA A σ where
  init := D.start
  step := fun _ r a =>
    match a with
    | none => Sum.inl (decide (r ∈ D.accept))
    | some x => Sum.inr (D.step r x, true)

variable {σ : Type} (D : DFA A σ)

private lemma twoDFAOfDFA_iterate (w : List A) :
    ∀ k, k ≤ w.length →
      ((twoDFAOfDFA D).next w)^[k] (Sum.inl (0, D.start))
        = Sum.inl (k, D.evalFrom D.start (w.take k)) := by
  intro k
  induction k with
  | zero => intro _; simp [DFA.evalFrom]
  | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hklt : k < w.length := by omega
      have hget : w[k]? = some w[k] := List.getElem?_eq_getElem hklt
      show (match (twoDFAOfDFA D).step _ (D.evalFrom D.start (w.take k)) w[k]? with
        | Sum.inl b => Sum.inr b
        | Sum.inr (r', true) => if k < w.length then Sum.inl (k + 1, r') else Sum.inr false
        | Sum.inr (r', false) => if 0 < k then Sum.inl (k - 1, r') else Sum.inr false) = _
      rw [hget]
      show (if k < w.length then
          Sum.inl (k + 1, D.step (D.evalFrom D.start (w.take k)) w[k]) else Sum.inr false) = _
      rw [if_pos hklt]
      have hsplit : w.take (k + 1) = w.take k ++ [w[k]] := by
        rw [List.take_add_one, hget]
        rfl
      have key : D.evalFrom D.start (w.take (k + 1))
          = D.step (D.evalFrom D.start (w.take k)) w[k] := by
        rw [hsplit]
        show List.foldl D.step D.start (w.take k ++ [w[k]]) = _
        rw [List.foldl_append]
        rfl
      rw [key]

open Classical in
private lemma twoDFAOfDFA_answer (w : List A) :
    ((twoDFAOfDFA D).next w)^[w.length + 1] (Sum.inl (0, D.start))
      = Sum.inr (decide (D.eval w ∈ D.accept)) := by
  rw [Function.iterate_succ_apply', twoDFAOfDFA_iterate D w w.length le_rfl]
  have hget : w[w.length]? = none := List.getElem?_eq_none le_rfl
  show (match (twoDFAOfDFA D).step _ (D.evalFrom D.start (w.take w.length)) w[w.length]? with
    | Sum.inl b => Sum.inr b
    | Sum.inr (r', true) =>
        if w.length < w.length then Sum.inl (w.length + 1, r') else Sum.inr false
    | Sum.inr (r', false) => if 0 < w.length then Sum.inl (w.length - 1, r') else Sum.inr false) = _
  rw [hget]
  simp [twoDFAOfDFA, DFA.eval, DFA.evalFrom]

open Classical in
lemma twoDFAOfDFA_accepts (w : List A) : (twoDFAOfDFA D).Accepts w ↔ w ∈ D.accepts := by
  constructor
  · rintro ⟨n, hn⟩
    have h := TwoDFA.answer_unique hn (twoDFAOfDFA_answer D w)
    have : D.eval w ∈ D.accept := of_decide_eq_true h.symm
    exact this
  · intro hw
    refine ⟨w.length + 1, ?_⟩
    show ((twoDFAOfDFA D).next w)^[w.length + 1] (Sum.inl (0, D.start)) = Sum.inr true
    rw [twoDFAOfDFA_answer D w]
    have hacc : D.eval w ∈ D.accept := hw
    simp [hacc]

/-- Every regular language is recognised by a deterministic two-way automaton. -/
lemma isTwoDFALang_of_isRegular {L : Language A} (hL : L.IsRegular) : IsTwoDFALang L := by
  obtain ⟨σ, _, D, rfl⟩ := hL
  exact ⟨σ, Finite.of_fintype σ, twoDFAOfDFA D, twoDFAOfDFA_accepts D⟩

/-- Shepherdson's Theorem, in the form used here. -/
lemma isRegular_of_isTwoDFALang [Finite A] {L : Language A} (hL : IsTwoDFALang L) :
    L.IsRegular := by
  obtain ⟨R, _, N, hN⟩ := hL
  have : {w : List A | N.Accepts w} = L := Set.ext hN
  exact this ▸ N.accepts_isRegular

/-- The languages of deterministic two-way automata are exactly the regular languages. -/
theorem isTwoDFALang_iff_isRegular [Finite A] {L : Language A} :
    IsTwoDFALang L ↔ L.IsRegular :=
  ⟨isRegular_of_isTwoDFALang, isTwoDFALang_of_isRegular⟩

/-- **Exercise `exer:2dfa-boolean`.**  The languages recognised by deterministic two-way automata
are closed under complement, union and intersection.

Only the closure properties are formalised; the polynomial bounds on the number of states that
the exercise also asks for are not, see the note at the top of this file. -/
theorem isTwoDFALang_boolean [Finite A] {L M : Language A}
    (hL : IsTwoDFALang L) (hM : IsTwoDFALang M) :
    IsTwoDFALang Lᶜ ∧ IsTwoDFALang (L + M) ∧ IsTwoDFALang (L ⊓ M) := by
  rw [isTwoDFALang_iff_isRegular] at hL hM
  refine ⟨?_, ?_, ?_⟩ <;> rw [isTwoDFALang_iff_isRegular]
  · exact hL.compl
  · exact hL.add hM
  · exact hL.inf hM

end Transducers.Exercises
