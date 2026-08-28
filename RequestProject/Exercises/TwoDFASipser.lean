/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): correctness of the searching automaton of
`RequestProject/Exercises/TwoDFASipserDef.lean`, and the exercise itself.

The searching automaton terminates on every input, because the sweep over the root candidates and
the exploration of each of their subtrees terminate (`scanEnd`); it accepts every input accepted by
the automaton it searches, because the sweep reaches the last configuration of the accepting run and
then the exploration of its subtree finds the initial configuration (`scanTo` and `descFound`); and
it accepts nothing else, because of the invariant of `RequestProject/Exercises/TwoDFASipserSound.lean`.
-/
import RequestProject.Exercises.TwoDFASipserScan
import RequestProject.Exercises.TwoDFASipserSound

namespace Transducers
namespace Exercises

open Transducers

variable {A R : Type}

/-! ## Correctness -/

section Correct

open Classical

variable [Fintype R] (N : TwoDFA A R)

/-- On the empty input the searching automaton answers at once. -/
lemma dfsAut_next_nil :
    (dfsAut N).next ([] : List A) (Sum.inl (0, (dfsAut N).init))
      = Sum.inr (decide (N.Accepts [])) :=
  next_answer N [] rfl

/-- The searching automaton terminates on every input. -/
theorem dfsAut_terminates (w : List A) :
    ∃ (k : ℕ) (b : Bool),
      ((dfsAut N).next w)^[k] (Sum.inl (0, (dfsAut N).init)) = Sum.inr b := by
  by_cases hne : w = []
  · subst hne
    exact ⟨1, decide (N.Accepts []), by rw [Function.iterate_one]; exact dfsAut_next_nil N⟩
  · rcases scanEnd hne w.length 0 (by omega) (Nat.zero_le _) (rFirst N.init) with h | h
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, false, hk⟩
    · obtain ⟨k, hk⟩ := h
      exact ⟨k, true, hk⟩

/-- If the searched automaton accepts, so does the search. -/
lemma dfsAut_accepts_of_accepts {w : List A} (hne : w ≠ []) (hacc : N.Accepts w) :
    (dfsAut N).Accepts w := by
  classical
  obtain ⟨m, hm, hmin⟩ : ∃ m, (N.next w)^[m] (Sum.inl (0, N.init)) = Sum.inr true ∧
      ∀ j < m, (N.next w)^[j] (Sum.inl (0, N.init)) ≠ Sum.inr true := by
    obtain ⟨n, hn⟩ := hacc
    have hex : ∃ m, (N.next w)^[m] (Sum.inl (0, N.init)) = Sum.inr true := ⟨n, hn⟩
    exact ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  -- the run is at a configuration `(p, q)` one step before it answers
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    cases m with
    | zero => exact absurd hm (by simp)
    | succ k => exact ⟨k, rfl⟩
  rcases hy : (N.next w)^[k] (Sum.inl (0, N.init)) with ⟨p, q⟩ | b
  · rw [Function.iterate_succ_apply', hy] at hm
    have hp : p ≤ w.length := pos_le_of_iterate k 0 N.init p q (Nat.zero_le _) hy
    have hRT : RT N w (p, q) := RT.of_answer hm
    have hcs : cstep N w p q = Sum.inl true := cstep_eq_inl_true hm
    have hscan : SReachT N w (0, Dfs.scanCur (rFirst N.init)) (Sum.inl (p, Dfs.scanCur q)) :=
      scanTo hne q hp p 0 (by omega) (Nat.zero_le _)
    have hfin : SReachT N w (0, Dfs.scanCur (rFirst N.init)) (Sum.inr true) := by
      refine hscan.trans ?_
      by_cases hinit : p = 0 ∧ q = N.init
      · exact SReachT.acc (sreach_scanCur_init N w hne hp hcs hinit.1 hinit.2)
      · refine (SReachT.of (sreach_scanCur_desc N w hne hp hcs hinit)).trans ?_
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
          cases k with
          | zero =>
              simp only [Function.iterate_zero_apply, Sum.inl.injEq, Prod.mk.injEq] at hy
              exact absurd ⟨hy.1.symm, hy.2.symm⟩ hinit
          | succ j => exact ⟨j, rfl⟩
        exact descFound hne j p q hp hRT hy
    obtain ⟨n, hn⟩ := hfin.toSReach
    exact ⟨n, hn⟩
  · rw [Function.iterate_succ_apply', hy, TwoDFA.next_inr] at hm
    exact absurd (hy.trans hm) (hmin k (by omega))

/-- The searching automaton accepts the same inputs as the automaton it searches. -/
theorem dfsAut_accepts (w : List A) : (dfsAut N).Accepts w ↔ N.Accepts w := by
  by_cases hne : w = []
  · subst hne
    constructor
    · rintro ⟨k, hk⟩
      have h1 : ((dfsAut N).next ([] : List A))^[1] (Sum.inl (0, (dfsAut N).init))
          = Sum.inr (decide (N.Accepts [])) := by
        rw [Function.iterate_one]; exact dfsAut_next_nil N
      have := TwoDFA.answer_unique h1 hk
      exact of_decide_eq_true this
    · intro h
      exact ⟨1, by rw [Function.iterate_one, dfsAut_next_nil N, decide_eq_true h]⟩
  · exact ⟨accepts_of_dfsAut_accepts hne, dfsAut_accepts_of_accepts N hne⟩

end Correct

/-- Every deterministic two-way automaton is equivalent to one with a quadratic number of states
that terminates on every input. -/
theorem exists_terminating_twoDFA [Fintype R] (N : TwoDFA A R) :
    ∃ (R' : Type) (_ : Fintype R') (N' : TwoDFA A R'),
      Fintype.card R' ≤ 24 * Fintype.card R ^ 2 ∧
      (∀ w : List A, ∃ (k : ℕ) (b : Bool),
        (N'.next w)^[k] (Sum.inl (0, N'.init)) = Sum.inr b) ∧
      (∀ w : List A, N'.Accepts w ↔ N.Accepts w) := by
  classical
  refine ⟨DfsSt R, inferInstance, dfsAut N, ?_, dfsAut_terminates N, dfsAut_accepts N⟩
  have hpos : 1 ≤ Fintype.card R := Fintype.card_pos_iff.2 ⟨N.init⟩
  have := card_dfsSt (R := R)
  nlinarith [this, hpos, sq_nonneg (Fintype.card R)]

/-- **Exercise `exer:2dfa-loop-elimination-sipser`.**  The set of inputs on which a deterministic
two-way transducer terminates is recognised by a deterministic two-way automaton which itself
terminates on every input and whose number of states is quadratic in the number of states of the
transducer. -/
theorem exists_terminating_twoDFA_halts {B Q : Type} [Fintype Q] (M : TwoWay A B Q) :
    ∃ (R : Type) (_ : Fintype R) (N : TwoDFA A R),
      Fintype.card R ≤ 24 * Fintype.card Q ^ 2 ∧
      (∀ w : List A, ∃ (k : ℕ) (b : Bool),
        (N.next w)^[k] (Sum.inl (0, N.init)) = Sum.inr b) ∧
      (∀ w : List A, N.Accepts w ↔ Halts M w) := by
  obtain ⟨R, hR, N, hcard, hterm, hacc⟩ := exists_terminating_twoDFA (haltDFA M)
  exact ⟨R, hR, N, hcard, hterm, fun w => (hacc w).trans (haltDFA_accepts M w)⟩

end Exercises
end Transducers
