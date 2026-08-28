/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): the depth-first search performed by the automaton of
`RequestProject/Exercises/TwoDFASipserDef.lean` runs to completion.

Two things are proved here.  The first is that the exploration of the subtree of a configuration
terminates: it either returns to the configuration it started from, or accepts on the way.  This is
the content of `explore`, proved by induction on the number of configurations below the one being
explored, which decreases when one passes to a child because a configuration that reaches the answer
*true* does not lie on a cycle.  The second is that the exploration *does* accept when the initial
configuration lies below the configuration being explored: this is `descFound`, proved by induction
on the distance from the initial configuration, using the first part to get past the candidate
children that are not on the accepting run.

The two statements are combined with the left-to-right sweep over the root candidates, `scanEnd` and
`scanTo`, in `RequestProject/Exercises/TwoDFASipser.lean`.
-/
import RequestProject.Exercises.TwoDFASipserTree

namespace Transducers
namespace Exercises

open Transducers

variable {A R : Type}

/-! ## The enumeration of the states -/

section Enum

variable [Fintype R]

lemma rIdx_lt (r : R) : rIdx r < Fintype.card R := (Fintype.equivFin R r).isLt

lemma rIdx_inj {r r' : R} (h : rIdx r = rIdx r') : r = r' :=
  (Fintype.equivFin R).injective (Fin.ext h)

lemma rIdx_rFirst (r₀ : R) : rIdx (rFirst r₀) = 0 := by
  unfold rIdx rFirst
  rw [Equiv.apply_symm_apply]

lemma rIdx_of_rSucc {r r' : R} (h : rSucc r = some r') : rIdx r' = rIdx r + 1 := by
  unfold rSucc at h
  split_ifs at h with hlt
  · rw [Option.some_inj] at h
    subst h
    unfold rIdx
    rw [Equiv.apply_symm_apply]

lemma card_of_rSucc_none {r : R} (h : rSucc r = none) : rIdx r + 1 = Fintype.card R := by
  unfold rSucc at h
  split_ifs at h with hlt
  have := rIdx_lt r
  omega

lemma exists_rSucc {r : R} (h : rIdx r + 1 < Fintype.card R) : ∃ r', rSucc r = some r' := by
  refine ⟨(Fintype.equivFin R).symm ⟨rIdx r + 1, h⟩, ?_⟩
  unfold rSucc
  rw [dif_pos h]

end Enum

/-! ## Reaching a search configuration, or accepting -/

section Explore

variable [Fintype R] {N : TwoDFA A R} {w : List A}

/-- The search started at `c` reaches `t`, or accepts before reaching it.  All the steps of the
search are stated in this form: the search may always stumble upon the initial configuration of the
searched automaton, and then it accepts at once. -/
def SReachT (N : TwoDFA A R) (w : List A) (c : SCfg R) (t : SCfg R ⊕ Bool) : Prop :=
  SReach N w c t ∨ SReach N w c (Sum.inr true)

lemma SReachT.of {c : SCfg R} {t : SCfg R ⊕ Bool} (h : SReach N w c t) : SReachT N w c t := Or.inl h

lemma SReachT.acc {c : SCfg R} {t : SCfg R ⊕ Bool} (h : SReach N w c (Sum.inr true)) :
    SReachT N w c t := Or.inr h

lemma SReachT.refl (c : SCfg R) : SReachT N w c (Sum.inl c) :=
  Or.inl (SReach.refl (N := N) (w := w) c)

lemma SReachT.trans {c c' : SCfg R} {t : SCfg R ⊕ Bool} (h1 : SReachT N w c (Sum.inl c'))
    (h2 : SReachT N w c' t) : SReachT N w c t := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact Or.inl (SReach.trans (N := N) (w := w) h1 h2)
    · exact Or.inr (SReach.trans (N := N) (w := w) h1 h2)
  · exact Or.inr h1

lemma SReachT.toSReach {c : SCfg R} (h : SReachT N w c (Sum.inr true)) :
    SReach N w c (Sum.inr true) := h.elim id id

/-- Every child of the configuration `(p, q)` can be explored: the search started at the child
returns to it, or accepts. -/
def ChildOK (N : TwoDFA A R) (w : List A) (p : ℕ) (q : R) : Prop :=
  ∀ (p' : ℕ) (c : R), p' ≤ w.length → N.next w (Sum.inl (p', c)) = Sum.inl (p, q) →
    SReachT N w (p', Dfs.desc c) (Sum.inl (p', Dfs.up c))

/-! ### One candidate child -/

/-- One candidate child on the right of `(p, q)` is dealt with. -/
lemma rightStep (hne : w ≠ []) {p : ℕ} {q : R} (hpn : p + 1 ≤ w.length)
    (hch : ChildOK N w p q) (c : R) :
    SReachT N w (p + 1, Dfs.chk q c false) (Sum.inl (p, Dfs.cont q c false)) := by
  by_cases hcs : cstep N w (p + 1) c = Sum.inr (q, false)
  · have h2 : ¬((p + 1) = 0 ∧ c = N.init) := by rintro ⟨h, -⟩; omega
    have s1 := sreach_chk_desc N w hne hpn hcs h2
    have hstep : N.next w (Sum.inl (p + 1, c)) = Sum.inl (p, q) := by
      have := next_eq_inl_left hcs (Nat.succ_pos p)
      simpa using this
    have s2 := hch (p + 1) c hpn hstep
    have s3 : SReach N w (p + 1, Dfs.up c) (Sum.inl (p, Dfs.cont q c false)) := by
      have := sreach_up_left N w hne (Nat.succ_pos p) hpn hcs
      simpa using this
    exact (SReachT.of s1).trans (s2.trans (SReachT.of s3))
  · have := sreach_chk_no_right N w hne (Nat.succ_pos p) hpn hcs
    exact SReachT.of (by simpa using this)

/-- One candidate child on the left of `(p, q)` is dealt with. -/
lemma leftStep (hne : w ≠ []) {p : ℕ} {q : R} (hp0 : 0 < p) (hpn : p ≤ w.length)
    (hch : ChildOK N w p q) (c : R) :
    SReachT N w (p - 1, Dfs.chk q c true) (Sum.inl (p, Dfs.cont q c true)) := by
  by_cases hcs : cstep N w (p - 1) c = Sum.inr (q, true)
  · by_cases hinit : p - 1 = 0 ∧ c = N.init
    · exact SReachT.acc
        (sreach_chk_init N w hne (show p - 1 ≤ w.length by omega) hcs hinit.1 hinit.2)
    · have s1 := sreach_chk_desc N w hne (show p - 1 ≤ w.length by omega) hcs hinit
      have hstep : N.next w (Sum.inl (p - 1, c)) = Sum.inl (p, q) := by
        have := next_eq_inl_right hcs (show p - 1 < w.length by omega)
        rwa [show p - 1 + 1 = p by omega] at this
      have s2 := hch (p - 1) c (by omega) hstep
      have s3 : SReach N w (p - 1, Dfs.up c) (Sum.inl (p, Dfs.cont q c true)) := by
        have := sreach_up_right N w hne (show p - 1 < w.length by omega) hcs
        rwa [show p - 1 + 1 = p by omega] at this
      exact (SReachT.of s1).trans (s2.trans (SReachT.of s3))
  · have := sreach_chk_no_left N w hne (show p - 1 < w.length by omega) hcs
    rw [show p - 1 + 1 = p by omega] at this
    exact SReachT.of this

/-! ### The loops over the candidate children -/

/-- The candidates on the right of `(p, q)`, from `c` on, are all dealt with. -/
lemma rightRunEnd (hne : w ≠ []) {p : ℕ} {q : R} (hpn : p + 1 ≤ w.length)
    (hch : ChildOK N w p q) :
    ∀ (j : ℕ) (c : R), Fintype.card R - rIdx c ≤ j →
      SReachT N w (p + 1, Dfs.chk q c false) (Sum.inl (p, Dfs.up q)) := by
  intro j
  induction j with
  | zero => intro c hj; have := rIdx_lt c; omega
  | succ j ih =>
      intro c hj
      refine (rightStep hne hpn hch c).trans ?_
      rcases hs : rSucc c with _ | c'
      · exact SReachT.of (sreach_cont_right_up N w hne (by omega) hs)
      · have hidx := rIdx_of_rSucc hs
        have hlt := rIdx_lt c'
        refine (SReachT.of (sreach_cont_succ_right N w hne (by omega) hs)).trans ?_
        exact ih c' (by omega)

/-- The candidates on the right of `(p, q)`, from `c` up to `c'`, are all dealt with. -/
lemma rightRunTo (hne : w ≠ []) {p : ℕ} {q : R} (hpn : p + 1 ≤ w.length)
    (hch : ChildOK N w p q) (c' : R) :
    ∀ (j : ℕ) (c : R), rIdx c' - rIdx c ≤ j → rIdx c ≤ rIdx c' →
      SReachT N w (p + 1, Dfs.chk q c false) (Sum.inl (p + 1, Dfs.chk q c' false)) := by
  intro j
  induction j with
  | zero =>
      intro c h1 h2
      rw [rIdx_inj (show rIdx c = rIdx c' by omega)]
      exact SReachT.refl _
  | succ j ih =>
      intro c h1 h2
      by_cases he : rIdx c = rIdx c'
      · rw [rIdx_inj he]; exact SReachT.refl _
      · have hlt : rIdx c < rIdx c' := by omega
        have hcard := rIdx_lt c'
        obtain ⟨d, hd⟩ := exists_rSucc (r := c) (by omega)
        have hidx := rIdx_of_rSucc hd
        refine (rightStep hne hpn hch c).trans ?_
        refine (SReachT.of (sreach_cont_succ_right N w hne (by omega) hd)).trans ?_
        exact ih d (by omega) (by omega)

/-- The candidates on the left of `(p, q)`, from `c` on, are all dealt with, and then the search
passes to the candidates on the right. -/
lemma leftRunAll (hne : w ≠ []) {p : ℕ} {q : R} (hp0 : 0 < p) (hlt : p < w.length)
    (hch : ChildOK N w p q) :
    ∀ (j : ℕ) (c : R), Fintype.card R - rIdx c ≤ j →
      SReachT N w (p - 1, Dfs.chk q c true)
        (Sum.inl (p + 1, Dfs.chk q (rFirst N.init) false)) := by
  intro j
  induction j with
  | zero => intro c hj; have := rIdx_lt c; omega
  | succ j ih =>
      intro c hj
      refine (leftStep hne hp0 (le_of_lt hlt) hch c).trans ?_
      rcases hs : rSucc c with _ | c'
      · exact SReachT.of (sreach_cont_left_switch N w hne hlt hs)
      · have hidx := rIdx_of_rSucc hs
        have hcard := rIdx_lt c'
        refine (SReachT.of (sreach_cont_succ_left N w hne hp0 (le_of_lt hlt) hs)).trans ?_
        exact ih c' (by omega)

/-- The candidates on the left of `(p, q)`, from `c` up to `c'`, are all dealt with. -/
lemma leftRunTo (hne : w ≠ []) {p : ℕ} {q : R} (hp0 : 0 < p) (hpn : p ≤ w.length)
    (hch : ChildOK N w p q) (c' : R) :
    ∀ (j : ℕ) (c : R), rIdx c' - rIdx c ≤ j → rIdx c ≤ rIdx c' →
      SReachT N w (p - 1, Dfs.chk q c true) (Sum.inl (p - 1, Dfs.chk q c' true)) := by
  intro j
  induction j with
  | zero =>
      intro c h1 h2
      rw [rIdx_inj (show rIdx c = rIdx c' by omega)]
      exact SReachT.refl _
  | succ j ih =>
      intro c h1 h2
      by_cases he : rIdx c = rIdx c'
      · rw [rIdx_inj he]; exact SReachT.refl _
      · have hlt : rIdx c < rIdx c' := by omega
        have hcard := rIdx_lt c'
        obtain ⟨d, hd⟩ := exists_rSucc (r := c) (by omega)
        have hidx := rIdx_of_rSucc hd
        refine (leftStep hne hp0 hpn hch c).trans ?_
        refine (SReachT.of (sreach_cont_succ_left N w hne hp0 hpn hd)).trans ?_
        exact ih d (by omega) (by omega)

/-- All the candidate children of `(p, q)` are dealt with, and the search moves up. -/
lemma leftRunEnd (hne : w ≠ []) {p : ℕ} {q : R} (hp0 : 0 < p) (hpn : p ≤ w.length)
    (hch : ChildOK N w p q) :
    ∀ (j : ℕ) (c : R), Fintype.card R - rIdx c ≤ j →
      SReachT N w (p - 1, Dfs.chk q c true) (Sum.inl (p, Dfs.up q)) := by
  intro j
  induction j with
  | zero => intro c hj; have := rIdx_lt c; omega
  | succ j ih =>
      intro c hj
      refine (leftStep hne hp0 hpn hch c).trans ?_
      rcases hs : rSucc c with _ | c'
      · rcases lt_or_eq_of_le hpn with hlt | heq
        · refine (SReachT.of (sreach_cont_left_switch N w hne hlt hs)).trans ?_
          exact rightRunEnd hne (by omega) hch _ (rFirst N.init) le_rfl
        · exact SReachT.of (sreach_cont_left_up N w hne heq hs)
      · have hidx := rIdx_of_rSucc hs
        have hcard := rIdx_lt c'
        refine (SReachT.of (sreach_cont_succ_left N w hne hp0 hpn hs)).trans ?_
        exact ih c' (by omega)

/-! ### The exploration of a subtree -/

/-- The exploration of the subtree of a configuration that reaches the answer *true* terminates:
the search comes back to the configuration it started from, or accepts on the way. -/
lemma exploreAux (hne : w ≠ []) : ∀ (m p : ℕ) (q : R), (Below N w (p, q)).ncard < m →
    p ≤ w.length → RT N w (p, q) →
    SReachT N w (p, Dfs.desc q) (Sum.inl (p, Dfs.up q)) := by
  intro m
  induction m with
  | zero => intro p q h; omega
  | succ m ih =>
      intro p q hm hp hRT
      have hch : ChildOK N w p q := by
        intro p' c hp' hstep
        exact ih p' c (lt_of_lt_of_le (ncard_below_lt hp' hstep hRT) (by omega)) hp'
          (RT.of_step hstep hRT)
      rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0
        have hlen : 0 < w.length := List.length_pos_iff.2 hne
        refine (SReachT.of (sreach_desc_right N w hne hlen (r := q))).trans ?_
        exact rightRunEnd hne (by omega) hch _ (rFirst N.init) le_rfl
      · refine (SReachT.of (sreach_desc_left N w hne hp hp0 (r := q))).trans ?_
        exact leftRunEnd hne hp0 hp hch _ (rFirst N.init) le_rfl

/-- The exploration of the subtree of a configuration that reaches the answer *true* terminates. -/
lemma explore (hne : w ≠ []) {p : ℕ} {q : R} (hp : p ≤ w.length) (hRT : RT N w (p, q)) :
    SReachT N w (p, Dfs.desc q) (Sum.inl (p, Dfs.up q)) :=
  exploreAux hne ((Below N w (p, q)).ncard + 1) p q (Nat.lt_succ_self _) hp hRT

/-- Every configuration that reaches the answer *true* can be explored. -/
lemma childOK (hne : w ≠ []) {p : ℕ} {q : R} (hRT : RT N w (p, q)) : ChildOK N w p q := by
  intro p' c hp' hstep
  exact explore hne hp' (RT.of_step hstep hRT)

/-! ### The exploration finds the initial configuration -/

/-- The exploration of the subtree of `(p, q)` accepts, provided the exploration of the subtree of
the child `(p', c)` of `(p, q)` does -- or `(p', c)` is the initial configuration itself, which the
search recognises when it checks it. -/
lemma descFoundStep (hne : w ≠ []) {p : ℕ} {q : R} (hp : p ≤ w.length) (hRT : RT N w (p, q))
    (p' : ℕ) (c : R) (hp' : p' ≤ w.length)
    (hstep : N.next w (Sum.inl (p', c)) = Sum.inl (p, q))
    (hrec : ¬(p' = 0 ∧ c = N.init) → SReachT N w (p', Dfs.desc c) (Sum.inr true)) :
    SReachT N w (p, Dfs.desc q) (Sum.inr true) := by
  have hch : ChildOK N w p q := childOK hne hRT
  rcases next_eq_inl_cases hstep with ⟨hcs, hlt, hpe⟩ | ⟨hcs, hpos, hpe⟩
  · -- the child lies to the left of `(p, q)`
    have hpp : p' = p - 1 := by omega
    subst hpp
    have hp0 : 0 < p := by omega
    refine (SReachT.of (sreach_desc_left N w hne hp hp0 (r := q))).trans ?_
    refine (leftRunTo hne hp0 hp hch c (rIdx c) (rFirst N.init)
      (by rw [rIdx_rFirst]; omega) (by rw [rIdx_rFirst]; omega)).trans ?_
    by_cases hinit : p - 1 = 0 ∧ c = N.init
    · exact SReachT.acc (sreach_chk_init N w hne hp' hcs hinit.1 hinit.2)
    · exact (SReachT.of (sreach_chk_desc N w hne hp' hcs hinit)).trans (hrec hinit)
  · -- the child lies to the right of `(p, q)`
    have hpp : p' = p + 1 := by omega
    subst hpp
    have hstart :
        SReachT N w (p, Dfs.desc q) (Sum.inl (p + 1, Dfs.chk q (rFirst N.init) false)) := by
      rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0
        exact SReachT.of (sreach_desc_right N w hne (by omega) (r := q))
      · refine (SReachT.of (sreach_desc_left N w hne hp hp0 (r := q))).trans ?_
        exact leftRunAll hne hp0 (by omega) hch (Fintype.card R) (rFirst N.init)
          (by rw [rIdx_rFirst]; omega)
    refine hstart.trans ?_
    refine (rightRunTo hne hp' hch c (rIdx c) (rFirst N.init)
      (by rw [rIdx_rFirst]; omega) (by rw [rIdx_rFirst]; omega)).trans ?_
    have hinit : ¬(p + 1 = 0 ∧ c = N.init) := by rintro ⟨h, -⟩; omega
    exact (SReachT.of (sreach_chk_desc N w hne hp' hcs hinit)).trans (hrec hinit)

/-- If the initial configuration of the searched automaton lies strictly below the configuration
`(p, q)` -- more precisely, if the run started at the initial configuration is at `(p, q)` after
`k + 1` steps -- then the exploration of the subtree of `(p, q)` accepts. -/
lemma descFound (hne : w ≠ []) : ∀ (k p : ℕ) (q : R), p ≤ w.length → RT N w (p, q) →
    (N.next w)^[k + 1] (Sum.inl (0, N.init)) = Sum.inl (p, q) →
    SReachT N w (p, Dfs.desc q) (Sum.inr true) := by
  intro k
  induction k with
  | zero =>
      intro p q hp hRT hrun
      rw [show (0 : ℕ) + 1 = 1 from rfl, Function.iterate_one] at hrun
      exact descFoundStep hne hp hRT (0 : ℕ) N.init (Nat.zero_le _) hrun
        (fun h => absurd ⟨rfl, rfl⟩ h)
  | succ k ih =>
      intro p q hp hRT hrun
      rw [Function.iterate_succ_apply'] at hrun
      rcases hy : (N.next w)^[k + 1] (Sum.inl (0, N.init)) with ⟨p', c⟩ | b
      · rw [hy] at hrun
        have hp' : p' ≤ w.length :=
          pos_le_of_iterate (k + 1) 0 N.init p' c (Nat.zero_le _) hy
        exact descFoundStep hne hp hRT p' c hp' hrun
          (fun _ => ih p' c hp' (RT.of_step hrun hRT) hy)
      · rw [hy] at hrun; exact absurd hrun (by simp)

end Explore

end Exercises
end Transducers
