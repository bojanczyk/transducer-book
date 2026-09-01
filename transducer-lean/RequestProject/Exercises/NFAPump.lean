/-
Pumping for the runs of an nfa, used by the exercise
`exer:for-transducer-continuity-nonelementary` of the chapter *For-transducers*
(`polyregular-for.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.NFAUnambig

/-!
# An nfa with a longest accepted string has more states than that string is long

This file proves the pumping step that the solution of
`exer:for-transducer-continuity-nonelementary` uses in one sentence: *an nfa whose language
contains a string of length `ℓ` and no longer string must have more than `ℓ` states, since
otherwise the accepting run would repeat a state and could be pumped.*

The runs are the ones of `RequestProject.Exercises.NFAUnambig`: `RunFrom M q w qs` says that
`qs` lists the states visited after each letter of `w` when the run starts in `q`, and
`AccRun` adds that the run starts in an initial state and ends in an accepting one.  The two
new pieces of that api here are that runs compose (`RunFrom.append`) and that a run can be cut
at any position (`RunFrom.take`, `RunFrom.drop`); together they give the pumping lemma
`runFrom_pump` and then the statement above, `nfa_card_gt_length_of_longest`.
-/

namespace Transducers.Exercises

open Transducers

variable {A Q : Type}

/-! ## Composing and cutting runs -/

lemma getLastD_append (q : Q) (qs rs : List Q) :
    (qs ++ rs).getLastD q = rs.getLastD (qs.getLastD q) := by
  induction qs generalizing q with
  | nil => simp
  | cons a as ih => rw [List.cons_append, getLastD_cons, ih, getLastD_cons]

/-- Two runs, the second one starting where the first one ends, compose to a run. -/
lemma RunFrom.append {M : NFA A Q} {q : Q} {u v : List A} {qs rs : List Q}
    (h : RunFrom M q u qs) (h' : RunFrom M (qs.getLastD q) v rs) :
    RunFrom M q (u ++ v) (qs ++ rs) := by
  induction h with
  | nil q => simpa using h'
  | @cons q a r u qs hst _ ih =>
      rw [getLastD_cons] at h'
      simpa using RunFrom.cons hst (ih h')

/-- The first `k` steps of a run form a run. -/
lemma RunFrom.take {M : NFA A Q} {q : Q} {w : List A} {qs : List Q}
    (h : RunFrom M q w qs) (k : ℕ) : RunFrom M q (w.take k) (qs.take k) := by
  induction h generalizing k with
  | nil q => simpa using RunFrom.nil q
  | @cons q a r w qs hst _ ih =>
      cases k with
      | zero => simpa using RunFrom.nil q
      | succ k => simpa using RunFrom.cons hst (ih k)

/-- The steps of a run after the first `k` form a run, starting in the state reached after
`k` steps. -/
lemma RunFrom.drop {M : NFA A Q} {q : Q} {w : List A} {qs : List Q}
    (h : RunFrom M q w qs) (k : ℕ) :
    RunFrom M ((qs.take k).getLastD q) (w.drop k) (qs.drop k) := by
  induction h generalizing k with
  | nil q => simpa using RunFrom.nil q
  | @cons q a r w qs hst hrun ih =>
      cases k with
      | zero => simpa using RunFrom.cons hst hrun
      | succ k =>
          have h' := ih k
          rw [List.take_succ_cons, getLastD_cons, List.drop_succ_cons, List.drop_succ_cons]
          exact h'

/-! ## Pumping -/

/-- **Pumping.**  If a run visits the same state after `i` and after `j > i` letters, then the
loop between the two visits can be repeated: there is a strictly longer input with a run that
starts and ends in the same states. -/
lemma runFrom_pump {M : NFA A Q} {q : Q} {w : List A} {qs : List Q}
    (hrun : RunFrom M q w qs) {i j : ℕ} (hij : i < j) (hj : j ≤ w.length)
    (heq : (qs.take i).getLastD q = (qs.take j).getLastD q) :
    ∃ (w' : List A) (qs' : List Q), RunFrom M q w' qs' ∧ w.length < w'.length ∧
      qs'.getLastD q = qs.getLastD q := by
  have hAj : RunFrom M q (w.take j) (qs.take j) := hrun.take j
  have hB : RunFrom M ((qs.take j).getLastD q) (w.drop j) (qs.drop j) := hrun.drop j
  have h1 : RunFrom M q (w.take i) (qs.take i) := by
    have h := hAj.take i
    rwa [List.take_take, List.take_take, Nat.min_eq_left hij.le] at h
  have h2 : RunFrom M ((qs.take i).getLastD q) ((w.take j).drop i) ((qs.take j).drop i) := by
    have h := hAj.drop i
    rwa [List.take_take, Nat.min_eq_left hij.le] at h
  have hsplit : (qs.take i) ++ ((qs.take j).drop i) = qs.take j := by
    have h := List.take_append_drop i (qs.take j)
    rwa [List.take_take, Nat.min_eq_left hij.le] at h
  have hmidlast : ((qs.take j).drop i).getLastD ((qs.take i).getLastD q)
      = (qs.take j).getLastD q := by
    have h := getLastD_append q (qs.take i) ((qs.take j).drop i)
    rw [hsplit] at h
    exact h.symm
  have hmp : ((qs.take j).drop i).getLastD ((qs.take i).getLastD q) = (qs.take i).getLastD q := by
    rw [hmidlast, ← heq]
  have r2 : RunFrom M q (w.take i ++ (w.take j).drop i) (qs.take i ++ (qs.take j).drop i) :=
    h1.append h2
  have last2 : (qs.take i ++ (qs.take j).drop i).getLastD q = (qs.take i).getLastD q := by
    rw [getLastD_append, hmp]
  have r3 : RunFrom M q ((w.take i ++ (w.take j).drop i) ++ (w.take j).drop i)
      ((qs.take i ++ (qs.take j).drop i) ++ (qs.take j).drop i) := r2.append (by rw [last2]; exact h2)
  have last3 : ((qs.take i ++ (qs.take j).drop i) ++ (qs.take j).drop i).getLastD q
      = (qs.take i).getLastD q := by
    rw [getLastD_append, last2, hmp]
  have hBp : RunFrom M ((qs.take i).getLastD q) (w.drop j) (qs.drop j) := by rw [heq]; exact hB
  have r4 := r3.append (by rw [last3]; exact hBp)
  refine ⟨_, _, r4, ?_, ?_⟩
  · have hlt : w.length < (((w.take i ++ (w.take j).drop i) ++ (w.take j).drop i)
        ++ w.drop j).length := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    exact hlt
  · rw [getLastD_append, last3]
    have hs := getLastD_append q (qs.take j) (qs.drop j)
    rw [List.take_append_drop] at hs
    rw [hs, ← heq]

/-! ## The consequence used by the exercise -/

/-- **An nfa whose language has a longest string has more states than that string is long.**
If `w` is accepted and no accepted string is longer than `w`, then the automaton has more than
`w.length` states: otherwise an accepting run of `w` would repeat a state, and pumping the loop
would produce a longer accepted string. -/
theorem nfa_card_gt_length_of_longest [Fintype Q] (M : NFA A Q) (w : List A)
    (hw : w ∈ M.accepts) (hmax : ∀ u ∈ M.accepts, u.length ≤ w.length) :
    w.length < Fintype.card Q := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨q, qs, hstart, hrun, hacc⟩ := (mem_accepts_iff_exists_accRun M w).1 hw
  have hcard : Fintype.card Q < Fintype.card (Fin (w.length + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨i, j, hne, hfi⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (w.length + 1) => (qs.take (k : ℕ)).getLastD q) hcard
  have hi : (i : ℕ) ≤ w.length := Nat.lt_succ_iff.mp i.isLt
  have hj : (j : ℕ) ≤ w.length := Nat.lt_succ_iff.mp j.isLt
  have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h)
  have key : ∀ {a b : ℕ}, a < b → b ≤ w.length →
      (qs.take a).getLastD q = (qs.take b).getLastD q → False := by
    intro a b hab hb heq
    obtain ⟨w', qs', hrun', hlen', hlast'⟩ := runFrom_pump hrun hab hb heq
    have hmem : w' ∈ M.accepts :=
      (mem_accepts_iff_exists_accRun M w').2 ⟨q, qs', hstart, hrun', by rw [hlast']; exact hacc⟩
    exact absurd (hmax w' hmem) (by omega)
  rcases lt_or_gt_of_ne hne' with hlt | hlt
  · exact key hlt hj hfi
  · exact key hlt hi hfi.symm

end Transducers.Exercises
