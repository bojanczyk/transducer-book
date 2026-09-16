/-
Part D, Section *A functional programming language*: an accepting computation gives a solution of
the tiling problem.

This file completes the second half of the reduction proving Lemma `lem:tiling`.  Given an
accepting computation of the machine `M` on the input `w` -- a derivation of the rewriting system
`PCP.TM.machineSRS` leading to a configuration that contains the accepting state -- it produces the
data `Transducers.TilingRed.CompData` from which `Transducers.TilingRed.isSolution_gcell` builds a
solution of `Transducers.TilingRed.inst M w`.

Three things have to be arranged.  The blanks that the derivation appends at the right-hand end are
put at the end of the starting configuration instead (`Transducers.TilingRed.reachesRule_pad`), and
further blanks are appended so that every configuration has the width of the grid.  The derivation
is then written as a sequence of configurations indexed by the rows of the grid, each consecutive
pair being related by an *action* (`Transducers.TilingRed.exists_seq`), which is read off the rule
that is applied.  Finally the sequence is shifted by one row, so that the first row of the grid
does nothing and merely carries the starting configuration.
-/
import RequestProject.PartD.TilingGrid
import RequestProject.PartD.TilingSRS

namespace Transducers
namespace TilingRed

open PCP

/-! ## Reading letters off a string split in three -/

section ListGetD
variable {α : Type*}

lemma getD_append_lt (l pad : List α) (d : α) {i : ℕ} (h : i < l.length) :
    (l ++ pad).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_append_ge (l pad : List α) (d : α) {i : ℕ} (h : l.length ≤ i) :
    (l ++ pad).getD i d = pad.getD (i - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma getD_append_mid (l m rr : List α) (d : α) {i : ℕ} (h : i < m.length) :
    (l ++ m ++ rr).getD (l.length + i) d = m.getD i d := by
  rw [List.append_assoc, getD_append_ge _ _ _ (by omega), Nat.add_sub_cancel_left,
    getD_append_lt _ _ _ h]

lemma getD_append_congr {l m m' rr : List α} (d : α) (hm : m.length = m'.length) {i : ℕ}
    (h : i < l.length ∨ l.length + m.length ≤ i) :
    (l ++ m ++ rr).getD i d = (l ++ m' ++ rr).getD i d := by
  rw [List.append_assoc, List.append_assoc]
  rcases h with h | h
  · rw [getD_append_lt l (m ++ rr) d h, getD_append_lt l (m' ++ rr) d h]
  · rw [getD_append_ge l (m ++ rr) d (by omega), getD_append_ge l (m' ++ rr) d (by omega),
      getD_append_ge m rr d (by omega), getD_append_ge m' rr d (by omega), hm]

end ListGetD

/-! ## A rule step of the machine is an action -/

variable {M : TM} {w : List ℕ}

lemma stepAt_right {l rr : List Sym} {q a r' b : ℕ} (htr : (q, a, r', b, true) ∈ M.trans) :
    StepAt M (l ++ [Sym.state q, Sym.tape a] ++ rr) (l ++ [Sym.tape b, Sym.state r'] ++ rr)
      (Act.right l.length q a r' b) := by
  refine ⟨htr, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using getD_append_mid l [Sym.state q, Sym.tape a] rr blank (i := 0) (by simp)
  · simpa using getD_append_mid l [Sym.state q, Sym.tape a] rr blank (i := 1) (by simp)
  · simpa using getD_append_mid l [Sym.tape b, Sym.state r'] rr blank (i := 0) (by simp)
  · simpa using getD_append_mid l [Sym.tape b, Sym.state r'] rr blank (i := 1) (by simp)
  · intro i h1 h2
    exact getD_append_congr blank (by simp) (by simp; omega)

lemma stepAt_left {l rr : List Sym} {q a r' b c : ℕ} (htr : (q, a, r', b, false) ∈ M.trans) :
    StepAt M (l ++ [Sym.tape c, Sym.state q, Sym.tape a] ++ rr)
      (l ++ [Sym.state r', Sym.tape c, Sym.tape b] ++ rr)
      (Act.left l.length q a r' b c) := by
  refine ⟨htr, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using getD_append_mid l [Sym.tape c, Sym.state q, Sym.tape a] rr blank (i := 0) (by simp)
  · simpa using getD_append_mid l [Sym.tape c, Sym.state q, Sym.tape a] rr blank (i := 1) (by simp)
  · simpa using getD_append_mid l [Sym.tape c, Sym.state q, Sym.tape a] rr blank (i := 2) (by simp)
  · simpa using getD_append_mid l [Sym.state r', Sym.tape c, Sym.tape b] rr blank (i := 0) (by simp)
  · simpa using getD_append_mid l [Sym.state r', Sym.tape c, Sym.tape b] rr blank (i := 1) (by simp)
  · simpa using getD_append_mid l [Sym.state r', Sym.tape c, Sym.tape b] rr blank (i := 2) (by simp)
  · intro i h1 h2 h3
    exact getD_append_congr blank (by simp) (by simp; omega)

/-- **Every rule step of the machine is an action.** -/
lemma exists_act_of_stepRule {u v : List Sym} (h : StepRule (M.transRules w) u v) :
    ∃ A, StepAt M u v A := by
  cases h with
  | mk l lhs rhs rr hmem =>
      rcases List.mem_append.1 hmem with hm | hm
      · simp only [TM.rightRules, List.mem_filterMap] at hm
        obtain ⟨⟨q, a, r', b, dir⟩, hx, hx'⟩ := hm
        cases dir with
        | false => simp at hx'
        | true =>
            simp only [if_true, Option.some.injEq, Prod.mk.injEq] at hx'
            obtain ⟨e1, e2⟩ := hx'
            subst e1
            subst e2
            exact ⟨_, stepAt_right hx⟩
      · simp only [TM.leftRules, List.mem_flatMap, List.mem_filterMap] at hm
        obtain ⟨c, hc, ⟨q, a, r', b, dir⟩, hx, hx'⟩ := hm
        cases dir with
        | true => simp at hx'
        | false =>
            simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at hx'
            obtain ⟨e1, e2⟩ := hx'
            subst e1
            subst e2
            exact ⟨_, stepAt_left hx⟩

/-! ## A derivation is a sequence of configurations -/

/-- **A derivation of the machine, written as a sequence of configurations** indexed by the
natural numbers, consecutive ones being related by an action, and constant from the step `L` on. -/
lemma exists_seq {a b : List Sym} (h : ReachesR (M.transRules w) a b) :
    ∃ (L : ℕ) (σ : ℕ → List Sym) (A : ℕ → Act),
      σ 0 = a ∧ (∀ t, L ≤ t → σ t = b) ∧ (∀ t, ReachesR (M.transRules w) a (σ t)) ∧
      ∀ t < L, StepAt M (σ t) (σ (t + 1)) (A t) := by
  induction h with
  | refl =>
      exact ⟨0, fun _ => a, fun _ => Act.idle, rfl, fun _ _ => rfl,
        fun _ => ReachesR.refl _ _, fun t ht => absurd ht (by omega)⟩
  | @tail c d hac hstep ih =>
      obtain ⟨L, σ, A, h0, hst, hre, hstp⟩ := ih
      obtain ⟨Aend, hAend⟩ := exists_act_of_stepRule hstep
      have hσL : σ L = c := hst L le_rfl
      refine ⟨L + 1, fun t => if t ≤ L then σ t else d, fun t => if t < L then A t else Aend,
        by simp [h0], ?_, ?_, ?_⟩
      · intro t ht
        show (if t ≤ L then σ t else d) = d
        rw [if_neg (by omega)]
      · intro t
        show ReachesR (M.transRules w) a (if t ≤ L then σ t else d)
        by_cases ht : t ≤ L
        · rw [if_pos ht]; exact hre t
        · rw [if_neg ht]; exact hac.trans (ReachesR.single hstep)
      · intro t ht
        show StepAt M (if t ≤ L then σ t else d) (if t + 1 ≤ L then σ (t + 1) else d)
          (if t < L then A t else Aend)
        by_cases htL : t < L
        · rw [if_pos (by omega : t ≤ L), if_pos (by omega : t + 1 ≤ L), if_pos htL]
          exact hstp t htL
        · have htL' : t = L := by omega
          subst htL'
          rw [if_pos le_rfl, if_neg (by omega : ¬ t + 1 ≤ t), if_neg (by omega : ¬ t < t), hσL]
          exact hAend

/-! ## The data of a computation -/

/-- The rules of the machine preserve the length of a configuration. -/
lemma transRules_length_eq (M : TM) (w : List ℕ) :
    ∀ p ∈ M.transRules w, p.1.length = p.2.length := by
  intro p hp
  rcases List.mem_append.1 hp with hm | hm
  · simp only [TM.rightRules, List.mem_filterMap] at hm
    obtain ⟨⟨q, a, r', b, dir⟩, -, hx'⟩ := hm
    cases dir with
    | false => simp at hx'
    | true => simp only [if_true, Option.some.injEq] at hx'; subst hx'; rfl
  · simp only [TM.leftRules, List.mem_flatMap, List.mem_filterMap] at hm
    obtain ⟨c, -, ⟨q, a, r', b, dir⟩, -, hx'⟩ := hm
    cases dir with
    | true => simp at hx'
    | false =>
        simp only [Bool.false_eq_true, if_false, Option.some.injEq] at hx'
        subst hx'
        rfl

/-- A string of blanks carries blanks. -/
lemma getD_replicate (k i : ℕ) : (List.replicate k blank).getD i blank = blank := by
  rcases lt_or_ge i k with h | h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

/-- The letters of the starting configuration, padded with blanks. -/
lemma getD_startCfg_padded (M : TM) (w : List ℕ) (k i : ℕ) :
    (Sym.state M.q0 :: (w.map Sym.tape ++ List.replicate k blank)).getD i blank =
      if i = 0 then Sym.state M.q0 else Sym.tape (w.getD (i - 1) 0) := by
  cases i with
  | zero => simp
  | succ i =>
      rw [if_neg (by omega)]
      show (w.map Sym.tape ++ List.replicate k blank).getD i blank =
        Sym.tape (w.getD (i + 1 - 1) 0)
      rw [show i + 1 - 1 = i from rfl]
      rcases lt_or_ge i w.length with hi | hi
      · rw [getD_append_lt _ _ _ (by simpa using hi),
          List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
        simp
      · rw [getD_append_ge _ _ _ (by simpa using hi), List.getD_eq_default w 0 hi,
          getD_replicate]
        rfl

/-- A string all of whose letters may be appended at the right-hand end of a configuration of the
machine is a string of blanks. -/
lemma eq_replicate_blank {z : List Sym} (hz : ∀ x ∈ z, x ∈ (M.machineSRS w).ext) :
    z = List.replicate z.length blank := by
  refine (List.eq_replicate_iff.2 ⟨rfl, fun x hx => ?_⟩)
  have := hz x hx
  simpa [TM.machineSRS, blank] using this

/-- **Padding a step on the right.**  An action performed between two configurations of the same
length is still performed between them after blanks have been appended to both. -/
lemma stepAt_pad {u v : List Sym} {A : Act} (h : StepAt M u v A) (hlen : u.length = v.length)
    (pad : List Sym) : StepAt M (u ++ pad) (v ++ pad) A := by
  have hrest : ∀ i, v.getD i blank = u.getD i blank →
      (v ++ pad).getD i blank = (u ++ pad).getD i blank := by
    intro i hi
    rcases lt_or_ge i u.length with hlt | hge
    · rw [getD_append_lt _ _ _ (by omega), getD_append_lt _ _ _ hlt, hi]
    · rw [getD_append_ge _ _ _ (by omega), getD_append_ge _ _ _ hge, hlen]
  cases A with
  | idle =>
      have hv : v = u := h
      subst hv
      exact rfl
  | right q a r' b pp =>
      obtain ⟨htr, hp, e1, e2, e3, e4, hr⟩ := h
      refine ⟨htr, by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [getD_append_lt _ _ _ (by omega), e1]
      · rw [getD_append_lt _ _ _ (by omega), e2]
      · rw [getD_append_lt _ _ _ (by omega), e3]
      · rw [getD_append_lt _ _ _ (by omega), e4]
      · intro i h1 h2
        exact hrest i (hr i h1 h2)
  | left q a r' b c pp =>
      obtain ⟨htr, hp, e1, e2, e3, e4, e5, e6, hr⟩ := h
      refine ⟨htr, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [getD_append_lt _ _ _ (by omega), e1]
      · rw [getD_append_lt _ _ _ (by omega), e2]
      · rw [getD_append_lt _ _ _ (by omega), e3]
      · rw [getD_append_lt _ _ _ (by omega), e4]
      · rw [getD_append_lt _ _ _ (by omega), e5]
      · rw [getD_append_lt _ _ _ (by omega), e6]
      · intro i h1 h2 h3
        exact hrest i (hr i h1 h2 h3)

/-- **An accepting computation of the machine gives the data of a computation**, in a grid wide
enough to hold the input and tall enough to hold the computation. -/
lemma exists_compData (M : TM) (w : List ℕ) (h : M.Accepts w) :
    ∃ N cont act, CompData M w N cont act := by
  obtain ⟨C, hreach, hqacc⟩ := h
  obtain ⟨z, hz, hR⟩ := reachesRule_pad hreach
  have hzrep : z = List.replicate z.length blank := eq_replicate_blank hz
  obtain ⟨L, σ, A, h0, hst, hre, hstp⟩ := exists_seq (w := w) hR
  have hW₀ : (M.startCfg w ++ z).length = w.length + 1 + z.length := by
    simp [TM.startCfg]
    omega
  have hlen : ∀ t, (σ t).length = w.length + 1 + z.length := by
    intro t
    have hl := ReachesR.length_eq (transRules_length_eq M w) (hre t)
    rw [← hl]
    exact hW₀
  have halph : ∀ t, ∀ s ∈ σ t, s ∈ M.alphabet w := by
    intro t
    refine Reaches.mem_alphabet (S := M.machineSRS w) (machineSRS_wf M w)
      (a := M.startCfg w ++ z) (b := σ t) ?_ ?_
    · exact ReachesRule.toReaches (S := M.machineSRS w) (hre t)
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact startCfg_mem_alphabet M w s hs
      · rw [hzrep] at hs
        rw [List.eq_of_mem_replicate hs]
        exact blank_mem_alphabet M w
  refine ⟨L + w.length + z.length + 3,
    fun j => σ (j - 1) ++ List.replicate (L + 3) blank,
    fun j => if 1 ≤ j ∧ j - 1 < L then A (j - 1) else Act.idle, ?_⟩
  have hpad : ∀ s ∈ List.replicate (L + 3) blank, s ∈ M.alphabet w := by
    intro s hs
    rw [List.eq_of_mem_replicate hs]
    exact blank_mem_alphabet M w
  refine
    { size := by omega
      len := ?_
      alph := ?_
      step := ?_
      act0 := by simp
      first := ?_
      accept := ?_ }
  · intro j _
    rw [List.length_append, hlen (j - 1), List.length_replicate]
    omega
  · intro j _ s hs
    rcases List.mem_append.1 hs with hs | hs
    · exact halph _ s hs
    · exact hpad s hs
  · intro j _
    by_cases hj : 1 ≤ j ∧ j - 1 < L
    · rw [if_pos hj]
      obtain ⟨hj1, hj2⟩ := hj
      have hstep := hstp (j - 1) hj2
      rw [show j - 1 + 1 = j from by omega] at hstep
      have hs : j + 1 - 1 = j := by omega
      rw [hs]
      exact stepAt_pad hstep (by rw [hlen, hlen]) _
    · rw [if_neg hj]
      show σ (j + 1 - 1) ++ _ = σ (j - 1) ++ _
      by_cases hj0 : j = 0
      · subst hj0; rfl
      · rw [hst (j + 1 - 1) (by omega), hst (j - 1) (by omega)]
  · intro i
    have he : σ (0 - 1) ++ List.replicate (L + 3) blank =
        Sym.state M.q0 :: (w.map Sym.tape ++ List.replicate (z.length + (L + 3)) blank) := by
      rw [show (0 : ℕ) - 1 = 0 from rfl, h0]
      conv_lhs => rw [hzrep]
      simp [TM.startCfg, List.append_assoc, List.replicate_add]
    rw [he, getD_startCfg_padded]
  · refine List.mem_append_left _ ?_
    rw [hst _ (by omega)]
    exact hqacc

/-- **An accepting computation of the machine gives a solution of the tiling instance.** -/
lemma solvable_of_accepts (M : TM) (w : List ℕ) (h : M.Accepts w) :
    Tiling.Solvable (inst M w) := by
  obtain ⟨N, cont, act, hdata⟩ := exists_compData M w h
  exact solvable_of_compData hdata

end TilingRed
end Transducers
