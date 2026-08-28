/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): the sweep over the candidate children of the root.

The tree explored by the searching automaton is rooted at a virtual vertex, the answer *true*; its
children are the configurations from which the searched automaton answers *true* in one step.  They
are enumerated by a left-to-right sweep over the input, which explores the subtree of each of them
in turn.  `scanEnd` says that the sweep runs to its end -- and then the search rejects -- unless it
accepts on the way, and `scanTo` says that it reaches any prescribed configuration, again unless it
accepts on the way.
-/
import RequestProject.Exercises.TwoDFASipserExplore

namespace Transducers
namespace Exercises

open Transducers

variable {A R : Type}

section Scan

variable [Fintype R] {N : TwoDFA A R} {w : List A}

/-- One root candidate is dealt with: either it is not a child of the root, or its subtree is
explored. -/
lemma scanStep (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) (r : R) :
    SReachT N w (p, Dfs.scanCur r) (Sum.inl (p, Dfs.scanNext r)) := by
  by_cases hcs : cstep N w p r = Sum.inl true
  · by_cases hinit : p = 0 ∧ r = N.init
    · exact SReachT.acc (sreach_scanCur_init N w hne hp hcs hinit.1 hinit.2)
    · have hRT : RT N w (p, r) := RT.of_answer (next_eq_answer hcs)
      refine (SReachT.of (sreach_scanCur_desc N w hne hp hcs hinit)).trans ?_
      exact (explore hne hp hRT).trans (SReachT.of (sreach_up_root N w hne hp hcs))
  · exact SReachT.of (sreach_scanCur_next N w hne hp hcs)

/-- The candidates at the position `p`, from `r` on, are dealt with, and the sweep passes to the
next position. -/
lemma scanRowNext (hne : w ≠ []) {p : ℕ} (hlt : p < w.length) :
    ∀ (j : ℕ) (r : R), Fintype.card R - rIdx r ≤ j →
      SReachT N w (p, Dfs.scanCur r) (Sum.inl (p + 1, Dfs.scanCur (rFirst N.init))) := by
  intro j
  induction j with
  | zero => intro r hj; have := rIdx_lt r; omega
  | succ j ih =>
      intro r hj
      refine (scanStep hne (le_of_lt hlt) r).trans ?_
      rcases hs : rSucc r with _ | r'
      · exact SReachT.of (sreach_scanNext_move N w hne hlt hs)
      · have hidx := rIdx_of_rSucc hs
        have hcard := rIdx_lt r'
        refine (SReachT.of (sreach_scanNext_succ N w hne (le_of_lt hlt) hs)).trans ?_
        exact ih r' (by omega)

/-- The candidates at the last position, from `r` on, are dealt with, and the search rejects. -/
lemma scanRowEnd (hne : w ≠ []) {p : ℕ} (hpe : p = w.length) :
    ∀ (j : ℕ) (r : R), Fintype.card R - rIdx r ≤ j →
      SReachT N w (p, Dfs.scanCur r) (Sum.inr false) := by
  intro j
  induction j with
  | zero => intro r hj; have := rIdx_lt r; omega
  | succ j ih =>
      intro r hj
      refine (scanStep hne (le_of_eq hpe) r).trans ?_
      rcases hs : rSucc r with _ | r'
      · exact SReachT.of (sreach_scanNext_end N w hne hpe hs)
      · have hidx := rIdx_of_rSucc hs
        have hcard := rIdx_lt r'
        refine (SReachT.of (sreach_scanNext_succ N w hne (le_of_eq hpe) hs)).trans ?_
        exact ih r' (by omega)

/-- The candidates at the position `p`, from `r` up to `r'`, are dealt with. -/
lemma scanRowTo (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) (r' : R) :
    ∀ (j : ℕ) (r : R), rIdx r' - rIdx r ≤ j → rIdx r ≤ rIdx r' →
      SReachT N w (p, Dfs.scanCur r) (Sum.inl (p, Dfs.scanCur r')) := by
  intro j
  induction j with
  | zero =>
      intro r h1 h2
      rw [rIdx_inj (show rIdx r = rIdx r' by omega)]
      exact SReachT.refl _
  | succ j ih =>
      intro r h1 h2
      by_cases he : rIdx r = rIdx r'
      · rw [rIdx_inj he]; exact SReachT.refl _
      · have hlt : rIdx r < rIdx r' := by omega
        have hcard := rIdx_lt r'
        obtain ⟨d, hd⟩ := exists_rSucc (r := r) (by omega)
        have hidx := rIdx_of_rSucc hd
        refine (scanStep hne hp r).trans ?_
        refine (SReachT.of (sreach_scanNext_succ N w hne hp hd)).trans ?_
        exact ih d (by omega) (by omega)

/-- The sweep over the root candidates runs to its end, and then the search rejects -- unless it
accepts on the way. -/
lemma scanEnd (hne : w ≠ []) : ∀ (j p : ℕ), w.length - p ≤ j → p ≤ w.length → ∀ r : R,
    SReachT N w (p, Dfs.scanCur r) (Sum.inr false) := by
  intro j
  induction j with
  | zero =>
      intro p hj hp r
      exact scanRowEnd hne (by omega) (Fintype.card R) r (by omega)
  | succ j ih =>
      intro p hj hp r
      rcases lt_or_eq_of_le hp with hlt | hpe
      · refine (scanRowNext hne hlt (Fintype.card R) r (by omega)).trans ?_
        exact ih (p + 1) (by omega) hlt (rFirst N.init)
      · exact scanRowEnd hne hpe (Fintype.card R) r (by omega)

/-- The sweep over the root candidates reaches any prescribed candidate -- unless it accepts on the
way. -/
lemma scanTo (hne : w ≠ []) {p' : ℕ} (q : R) (hp' : p' ≤ w.length) :
    ∀ (j p : ℕ), p' - p ≤ j → p ≤ p' →
      SReachT N w (p, Dfs.scanCur (rFirst N.init)) (Sum.inl (p', Dfs.scanCur q)) := by
  intro j
  induction j with
  | zero =>
      intro p hj hp
      have hpe : p = p' := by omega
      subst hpe
      exact scanRowTo hne hp' q (rIdx q) (rFirst N.init) (by rw [rIdx_rFirst]; omega)
        (by rw [rIdx_rFirst]; omega)
  | succ j ih =>
      intro p hj hp
      rcases lt_or_eq_of_le hp with hlt | hpe
      · refine (scanRowNext hne (by omega) (Fintype.card R) (rFirst N.init) (by omega)).trans ?_
        exact ih (p + 1) (by omega) (by omega)
      · subst hpe
        exact scanRowTo hne hp' q (rIdx q) (rFirst N.init) (by rw [rIdx_rFirst]; omega)
          (by rw [rIdx_rFirst]; omega)

end Scan

end Exercises
end Transducers
