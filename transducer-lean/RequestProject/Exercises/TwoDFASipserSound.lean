/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): the searching automaton accepts only what it should.

The search accepts when it discovers the initial configuration of the searched automaton, and it
does so on the strength of the phase it is in.  What makes that legitimate is an invariant of the
run of the searching automaton: in the phases `desc r`, `up r` and `cont q _ _` the configuration
that the search is visiting reaches the answer *true*, and in the phase `chk q _ s` so does the
configuration one step to the side `s`.  The invariant is preserved by every transition, and it
turns an accepting run of the searching automaton into an accepting run of the searched one.
-/
import RequestProject.Exercises.TwoDFASipserTree

namespace Transducers
namespace Exercises

open Transducers

variable {A R : Type}

section Sound

variable [Fintype R] {N : TwoDFA A R} {w : List A}

/-- The invariant of a phase of the search, at the position `p`. -/
def Inv (N : TwoDFA A R) (w : List A) : ℕ → Dfs R → Prop
  | _, Dfs.scanCur _ => True
  | _, Dfs.scanNext _ => True
  | p, Dfs.desc r => RT N w (p, r)
  | p, Dfs.up q => RT N w (p, q)
  | p, Dfs.chk q _ true => p + 1 ≤ w.length ∧ RT N w (p + 1, q)
  | p, Dfs.chk q _ false => 1 ≤ p ∧ RT N w (p - 1, q)
  | p, Dfs.cont q _ _ => RT N w (p, q)

/-- The invariant of a configuration of the searching automaton. -/
def InvC (N : TwoDFA A R) (w : List A) : TwoCfg (DfsSt R) → Prop
  | Sum.inr b => b = true → N.Accepts w
  | Sum.inl (p, Sum.inl ph) => p ≤ w.length ∧ Inv N w p ph
  | Sum.inl (p, Sum.inr (ph, true)) => p ≤ w.length ∧ 1 ≤ p ∧ Inv N w (p - 1) ph
  | Sum.inl (p, Sum.inr (ph, false)) => p ≤ w.length ∧ p + 1 ≤ w.length ∧ Inv N w (p + 1) ph

omit [Fintype R] in
lemma invC_false : InvC N w (Sum.inr false) := by
  intro h
  exact absurd h (by simp)

/-! ### The invariant is preserved by one transition -/

lemma invC_next_of_answer {p : ℕ} {st : DfsSt R} {b : Bool}
    (h : dfsStep N (lftLet w p) st w[p]? = Sum.inl b) (hb : b = true → N.Accepts w) :
    InvC N w ((dfsAut N).next w (Sum.inl (p, st))) := by
  rw [next_answer N w h]
  exact hb

lemma invC_next_of_move {p : ℕ} {st st' : DfsSt R} {d : Bool}
    (h : dfsStep N (lftLet w p) st w[p]? = Sum.inr (st', d))
    (hR : d = true → p < w.length → InvC N w (Sum.inl (p + 1, st')))
    (hL : d = false → 0 < p → InvC N w (Sum.inl (p - 1, st'))) :
    InvC N w ((dfsAut N).next w (Sum.inl (p, st))) := by
  cases d with
  | true =>
      by_cases hp : p < w.length
      · rw [next_right N w hp h]; exact hR rfl hp
      · have : (dfsAut N).next w (Sum.inl (p, st)) = Sum.inr false := by
          dsimp only [TwoDFA.next]
          rw [show (dfsAut N).step (if p = 0 then none else w[p - 1]?) st w[p]?
            = Sum.inr (st', true) from h]
          exact if_neg hp
        rw [this]
        exact invC_false
  | false =>
      by_cases hp : 0 < p
      · rw [next_left N w hp h]; exact hL rfl hp
      · have : (dfsAut N).next w (Sum.inl (p, st)) = Sum.inr false := by
          dsimp only [TwoDFA.next]
          rw [show (dfsAut N).step (if p = 0 then none else w[p - 1]?) st w[p]?
            = Sum.inr (st', false) from h]
          exact if_neg hp
        rw [this]
        exact invC_false

lemma invC_next_of_stay (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {st : DfsSt R} {ph' : Dfs R}
    (h : dfsStep N (lftLet w p) st w[p]? = dfsStay ph' w[p]?) (hph : Inv N w p ph') :
    InvC N w ((dfsAut N).next w (Sum.inl (p, st))) := by
  rcases hx : w[p]? with _ | a
  · -- the head is at the right end; it moves left and comes back
    have hpn : p = w.length := (getElem?_eq_none_iff' w hp).1 hx
    have hp0 : 0 < p := by
      rcases Nat.eq_zero_or_pos w.length with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hne
      · omega
    have hstep : dfsStep N (lftLet w p) st w[p]? = Sum.inr (Sum.inr (ph', false), false) := by
      rw [h, hx]; rfl
    refine invC_next_of_move hstep (fun hd => Bool.noConfusion hd) (fun _ _ => ?_)
    exact ⟨by omega, by omega, by rwa [show p - 1 + 1 = p by omega]⟩
  · -- the head moves right and comes back
    have hpn : p < w.length := by
      by_contra hc
      rw [show p = w.length by omega] at hx
      simp at hx
    have hstep : dfsStep N (lftLet w p) st w[p]? = Sum.inr (Sum.inr (ph', true), true) := by
      rw [h, hx]; rfl
    refine invC_next_of_move hstep (fun _ _ => ?_) (fun hd => Bool.noConfusion hd)
    exact ⟨by omega, by omega, by rwa [show p + 1 - 1 = p by omega]⟩

/-! ### The invariant is preserved by the search -/

lemma invC_next (hne : w ≠ []) {c : TwoCfg (DfsSt R)} (h : InvC N w c) :
    InvC N w ((dfsAut N).next w c) := by
  rcases c with ⟨p, st⟩ | b
  · rcases st with ph | ⟨ph, d⟩
    · obtain ⟨hp, hinv⟩ := h
      have hnb := not_both_none w hne hp
      have hl0 : (lftLet w p).isNone = true ↔ p = 0 := by
        rw [Option.isNone_iff_eq_none]
        exact lftLet_eq_none_iff w hp
      cases ph with
      | scanCur r =>
          rcases hcs : cstep N w p r with b | y
          · cases b with
            | true =>
                by_cases hinit : (lftLet w p).isNone ∧ r = N.init
                · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanCur r)) w[p]?
                      = Sum.inl true := by
                    rw [dfsStep_inl N hnb]
                    exact dfsPhase_scanCur_init hcs hinit
                  refine invC_next_of_answer hstep (fun _ => ?_)
                  have hp0 : p = 0 := hl0.1 (by simpa using hinit.1)
                  refine ⟨1, ?_⟩
                  rw [Function.iterate_one, ← hp0, ← hinit.2]
                  exact next_eq_answer hcs
                · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanCur r)) w[p]?
                      = dfsStay (Dfs.desc r) w[p]? := by
                    rw [dfsStep_inl N hnb]
                    exact dfsPhase_scanCur_desc hcs hinit
                  exact invC_next_of_stay hne hp hstep (RT.of_answer (next_eq_answer hcs))
            | false =>
                have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanCur r)) w[p]?
                    = dfsStay (Dfs.scanNext r) w[p]? := by
                  rw [dfsStep_inl N hnb]
                  exact dfsPhase_scanCur_false hcs
                exact invC_next_of_stay hne hp hstep trivial
          · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanCur r)) w[p]?
                = dfsStay (Dfs.scanNext r) w[p]? := by
              rw [dfsStep_inl N hnb]
              exact dfsPhase_scanCur_move hcs
            exact invC_next_of_stay hne hp hstep trivial
      | scanNext r =>
          rcases hs : rSucc r with _ | r'
          · rcases hx : w[p]? with _ | a
            · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanNext r)) w[p]?
                  = Sum.inl false := by
                rw [dfsStep_inl N hnb, hx]
                exact dfsPhase_scanNext_end hs
              exact invC_next_of_answer hstep (fun hb => Bool.noConfusion hb)
            · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanNext r)) w[p]?
                  = Sum.inr (Sum.inl (Dfs.scanCur (rFirst N.init)), true) := by
                rw [dfsStep_inl N hnb, hx]
                exact dfsPhase_scanNext_none hs
              refine invC_next_of_move hstep (fun _ hlt => ⟨by omega, trivial⟩)
                (fun hd => Bool.noConfusion hd)
          · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.scanNext r)) w[p]?
                = dfsStay (Dfs.scanCur r') w[p]? := by
              rw [dfsStep_inl N hnb]
              exact dfsPhase_scanNext_succ hs
            exact invC_next_of_stay hne hp hstep trivial
      | desc r =>
          rcases hl : lftLet w p with _ | a
          · rcases hx : w[p]? with _ | a
            · exact absurd ⟨hl, hx⟩ hnb
            · have hp0 : p = 0 := (lftLet_eq_none_iff w hp).1 hl
              have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.desc r)) w[p]?
                  = Sum.inr (Sum.inl (Dfs.chk r (rFirst N.init) false), true) := by
                rw [dfsStep_inl N hnb, hl, hx]
                exact dfsPhase_desc_right
              refine invC_next_of_move hstep (fun _ hlt => ?_) (fun hd => Bool.noConfusion hd)
              exact ⟨by omega, by omega, by rwa [show p + 1 - 1 = p by omega]⟩
          · have hp0 : 0 < p := by
              rcases Nat.eq_zero_or_pos p with h0 | h0
              · rw [h0] at hl; exact absurd hl (by simp [lftLet])
              · exact h0
            have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.desc r)) w[p]?
                = Sum.inr (Sum.inl (Dfs.chk r (rFirst N.init) true), false) := by
              rw [dfsStep_inl N hnb, hl]
              exact dfsPhase_desc_left
            refine invC_next_of_move hstep (fun hd => Bool.noConfusion hd) (fun _ _ => ?_)
            exact ⟨by omega, by omega, by rwa [show p - 1 + 1 = p by omega]⟩
      | chk q c s =>
          by_cases hcs : cstep N w p c = Sum.inr (q, s)
          · by_cases hinit : (lftLet w p).isNone ∧ c = N.init
            · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.chk q c s)) w[p]?
                  = Sum.inl true := by
                rw [dfsStep_inl N hnb]
                exact dfsPhase_chk_init hcs hinit
              refine invC_next_of_answer hstep (fun _ => ?_)
              have hp0 : p = 0 := hl0.1 (by simpa using hinit.1)
              cases s with
              | false => exact absurd hinv.1 (by omega)
              | true =>
                  have hstep' : N.next w (Sum.inl (p, c)) = Sum.inl (p + 1, q) :=
                    next_eq_inl_right hcs (by have := hinv.1; omega)
                  have hRT : RT N w (p, c) := RT.of_step hstep' hinv.2
                  rw [hp0, hinit.2] at hRT
                  exact hRT
            · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.chk q c s)) w[p]?
                  = dfsStay (Dfs.desc c) w[p]? := by
                rw [dfsStep_inl N hnb]
                exact dfsPhase_chk_desc hcs hinit
              refine invC_next_of_stay hne hp hstep ?_
              cases s with
              | true =>
                  exact RT.of_step (next_eq_inl_right hcs (by have := hinv.1; omega)) hinv.2
              | false =>
                  exact RT.of_step (next_eq_inl_left hcs (by have := hinv.1; omega)) hinv.2
          · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.chk q c s)) w[p]?
                = Sum.inr (Sum.inl (Dfs.cont q c s), s) := by
              rw [dfsStep_inl N hnb]
              exact dfsPhase_chk_no hcs
            cases s with
            | true =>
                refine invC_next_of_move hstep (fun _ _ => ?_) (fun hd => Bool.noConfusion hd)
                exact ⟨by have := hinv.1; omega, hinv.2⟩
            | false =>
                refine invC_next_of_move hstep (fun hd => Bool.noConfusion hd) (fun _ _ => ?_)
                exact ⟨by omega, hinv.2⟩
      | cont q c s =>
          rcases hs : rSucc c with _ | c'
          · cases s with
            | false =>
                have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.cont q c false)) w[p]?
                    = dfsStay (Dfs.up q) w[p]? := by
                  rw [dfsStep_inl N hnb]
                  exact dfsPhase_cont_right hs
                exact invC_next_of_stay hne hp hstep hinv
            | true =>
                rcases hx : w[p]? with _ | a
                · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.cont q c true)) w[p]?
                      = dfsStay (Dfs.up q) w[p]? := by
                    rw [dfsStep_inl N hnb, hx]
                    exact dfsPhase_cont_left_none hs
                  exact invC_next_of_stay hne hp hstep hinv
                · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.cont q c true)) w[p]?
                      = Sum.inr (Sum.inl (Dfs.chk q (rFirst N.init) false), true) := by
                    rw [dfsStep_inl N hnb, hx]
                    exact dfsPhase_cont_left_end hs
                  refine invC_next_of_move hstep (fun _ hlt => ?_) (fun hd => Bool.noConfusion hd)
                  exact ⟨by omega, by omega, by rwa [show p + 1 - 1 = p by omega]⟩
          · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.cont q c s)) w[p]?
                = Sum.inr (Sum.inl (Dfs.chk q c' s), !s) := by
              rw [dfsStep_inl N hnb]
              exact dfsPhase_cont_succ hs
            cases s with
            | true =>
                refine invC_next_of_move hstep (fun hd => Bool.noConfusion hd) (fun _ hp0 => ?_)
                exact ⟨by omega, by omega, by rwa [show p - 1 + 1 = p by omega]⟩
            | false =>
                refine invC_next_of_move hstep (fun _ hlt => ?_) (fun hd => Bool.noConfusion hd)
                exact ⟨by omega, by omega, by rwa [show p + 1 - 1 = p by omega]⟩
      | up q =>
          rcases hcs : cstep N w p q with b | ⟨q', d⟩
          · cases b with
            | true =>
                have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.up q)) w[p]?
                    = dfsStay (Dfs.scanNext q) w[p]? := by
                  rw [dfsStep_inl N hnb]
                  exact dfsPhase_up_true hcs
                exact invC_next_of_stay hne hp hstep trivial
            | false =>
                have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.up q)) w[p]? = Sum.inl false := by
                  rw [dfsStep_inl N hnb]
                  exact dfsPhase_up_false hcs
                exact invC_next_of_answer hstep (fun hb => Bool.noConfusion hb)
          · have hstep : dfsStep N (lftLet w p) (Sum.inl (Dfs.up q)) w[p]?
                = Sum.inr (Sum.inl (Dfs.cont q' q d), d) := by
              rw [dfsStep_inl N hnb]
              exact dfsPhase_up_move hcs
            cases d with
            | true =>
                refine invC_next_of_move hstep (fun _ hlt => ?_) (fun hd => Bool.noConfusion hd)
                exact ⟨by omega, RT.step (next_eq_inl_right hcs hlt) hinv⟩
            | false =>
                refine invC_next_of_move hstep (fun hd => Bool.noConfusion hd) (fun _ hp0 => ?_)
                exact ⟨by omega, RT.step (next_eq_inl_left hcs hp0) hinv⟩
    · cases d with
      | true =>
          have hnb := not_both_none w hne h.1
          have hstep : dfsStep N (lftLet w p) (Sum.inr (ph, true)) w[p]?
              = Sum.inr (Sum.inl ph, false) := dfsStep_inr N hnb ph true
          refine invC_next_of_move hstep (fun hd => Bool.noConfusion hd) (fun _ _ => ?_)
          exact ⟨by have := h.1; omega, h.2.2⟩
      | false =>
          have hnb := not_both_none w hne h.1
          have hstep : dfsStep N (lftLet w p) (Sum.inr (ph, false)) w[p]?
              = Sum.inr (Sum.inl ph, true) := dfsStep_inr N hnb ph false
          refine invC_next_of_move hstep (fun _ _ => ?_) (fun hd => Bool.noConfusion hd)
          exact ⟨by have := h.2.1; omega, h.2.2⟩
  · rw [TwoDFA.next_inr]
    exact h

/-- The invariant is preserved along the whole run. -/
lemma invC_iterate (hne : w ≠ []) : ∀ (k : ℕ) (c : TwoCfg (DfsSt R)), InvC N w c →
    InvC N w (((dfsAut N).next w)^[k] c) := by
  intro k
  induction k with
  | zero => intro c h; exact h
  | succ k ih =>
      intro c h
      rw [Function.iterate_succ_apply]
      exact ih _ (invC_next hne h)

/-- The searching automaton accepts only inputs accepted by the automaton it searches. -/
lemma accepts_of_dfsAut_accepts (hne : w ≠ []) (h : (dfsAut N).Accepts w) : N.Accepts w := by
  obtain ⟨k, hk⟩ := h
  have h0 : InvC N w (Sum.inl (0, (dfsAut N).init)) := ⟨Nat.zero_le _, trivial⟩
  have hfin := invC_iterate hne k _ h0
  rw [hk] at hfin
  exact hfin rfl

end Sound

end Exercises
end Transducers
