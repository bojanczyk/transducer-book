/-
Exercise `exer:2dfa-loop-elimination` of the chapter on two-way automata
(`2dfa.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.TwoDFAEx
import RequestProject.PartC.TwoWayCont

/-!
# Loop elimination

Exercise `exer:2dfa-loop-elimination`: a deterministic two-way transducer need not terminate on
every input, and the set of inputs on which it does terminate is a regular language.

The solution of the book goes through the string representation of the configuration graph.  Here
the same fact is obtained from Shepherdson's Theorem, which the project already has: the two-way
transducer, with its outputs forgotten and with "halt" turned into "accept", *is* a deterministic
two-way automaton, and the runs of the two machines correspond step by step.  A run that leaves
the input string is stuck for the transducer and rejects for the automaton, and a run that never
terminates never accepts, so the automaton accepts exactly the inputs on which the transducer
halts.
-/

namespace Transducers.Exercises

open Transducers

variable {A B Q : Type}

/-- The two-way transducer read as a two-way automaton: the outputs are forgotten and a halting
transition becomes an accepting one. -/
def haltDFA (M : TwoWay A B Q) : TwoDFA A Q where
  init := M.init
  step := fun l q r =>
    match M.step l q r with
    | Sum.inl _ => Sum.inl true
    | Sum.inr (q', _, d) => Sum.inr (q', d)

/-- The transducer terminates on the input `w`. -/
def Halts (M : TwoWay A B Q) (w : List A) : Prop :=
  ∃ o, M.Reaches (Cfg.conf [] M.init w) o Cfg.halt

private lemma take_getLast? (w : List A) (p : ℕ) (hp : p ≤ w.length) :
    (w.take p).getLast? = if p = 0 then none else w[p - 1]? := by
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · simp
  · have h1 : (w.take p)[p - 1]? = w[p - 1]? := by
      rw [List.getElem?_take, if_pos (by omega)]
    rw [if_neg (by omega), List.getLast?_eq_getElem?, List.length_take,
      show min p w.length = p by omega, h1]

/-- One step of the transducer and one step of the automaton agree. -/
private lemma step_corr (M : TwoWay A B Q) (w : List A) (p : ℕ) (q : Q) (hp : p ≤ w.length) :
    (M.stepCfg (Cfg.conf (w.take p) q (w.drop p)) = none ∧
        (haltDFA M).next w (Sum.inl (p, q)) = Sum.inr false)
      ∨ (∃ o, M.stepCfg (Cfg.conf (w.take p) q (w.drop p)) = some (o, Cfg.halt) ∧
        (haltDFA M).next w (Sum.inl (p, q)) = Sum.inr true)
      ∨ (∃ (o : List B) (p' : ℕ) (q' : Q), p' ≤ w.length ∧
        M.stepCfg (Cfg.conf (w.take p) q (w.drop p))
          = some (o, Cfg.conf (w.take p') q' (w.drop p')) ∧
        (haltDFA M).next w (Sum.inl (p, q)) = Sum.inl (p', q')) := by
  have hlast : (w.take p).getLast? = if p = 0 then none else w[p - 1]? := take_getLast? w p hp
  have hhead : (w.drop p).head? = w[p]? := List.head?_drop
  have hnext : (haltDFA M).next w (Sum.inl (p, q))
      = (match (haltDFA M).step (if p = 0 then none else w[p - 1]?) q w[p]? with
        | Sum.inl b => Sum.inr b
        | Sum.inr (r', true) => if p < w.length then Sum.inl (p + 1, r') else Sum.inr false
        | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false) := rfl
  have hstep : M.stepCfg (Cfg.conf (w.take p) q (w.drop p))
      = (match M.step (w.take p).getLast? q (w.drop p).head? with
        | Sum.inl o => some (o, Cfg.halt)
        | Sum.inr (q', o, true) =>
            match w.drop p with
            | [] => none
            | a :: v' => some (o, Cfg.conf (w.take p ++ [a]) q' v')
        | Sum.inr (q', o, false) =>
            match (w.take p).getLast? with
            | none => none
            | some a => some (o, Cfg.conf (w.take p).dropLast q' (a :: w.drop p))) := rfl
  rw [hlast, hhead] at hstep
  rw [hnext, hstep]
  rcases hM : M.step (if p = 0 then none else w[p - 1]?) q w[p]? with o | ⟨q', o, d⟩
  · refine Or.inr (Or.inl ⟨o, rfl, ?_⟩)
    show (match (haltDFA M).step (if p = 0 then none else w[p - 1]?) q w[p]? with
      | Sum.inl b => Sum.inr b
      | Sum.inr (r', true) => if p < w.length then Sum.inl (p + 1, r') else Sum.inr false
      | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false) = _
    rw [show (haltDFA M).step (if p = 0 then none else w[p - 1]?) q w[p]? = Sum.inl true by
      show (match M.step (if p = 0 then none else w[p - 1]?) q w[p]? with
        | Sum.inl _ => Sum.inl true
        | Sum.inr (q', _, d) => Sum.inr (q', d)) = _
      rw [hM]]
  · have hN : (haltDFA M).step (if p = 0 then none else w[p - 1]?) q w[p]? = Sum.inr (q', d) := by
      show (match M.step (if p = 0 then none else w[p - 1]?) q w[p]? with
        | Sum.inl _ => Sum.inl true
        | Sum.inr (q', _, d) => Sum.inr (q', d)) = _
      rw [hM]
    rw [hN]
    cases d with
    | true =>
        rcases lt_or_ge p w.length with hlt | hge
        · have hdrop : w.drop p = w[p] :: w.drop (p + 1) := List.drop_eq_getElem_cons hlt
          have htake : w.take p ++ [w[p]] = w.take (p + 1) := by
            rw [List.take_add_one, List.getElem?_eq_getElem hlt]
            rfl
          refine Or.inr (Or.inr ⟨o, p + 1, q', by omega, ?_, ?_⟩)
          · rw [hdrop]
            show some (o, Cfg.conf (w.take p ++ [w[p]]) q' (w.drop (p + 1))) = _
            rw [htake]
          · show (if p < w.length then Sum.inl (p + 1, q') else Sum.inr false) = _
            rw [if_pos hlt]
        · have hp' : p = w.length := le_antisymm hp hge
          have hdrop : w.drop p = [] := by rw [hp']; simp
          refine Or.inl ⟨?_, ?_⟩
          · rw [hdrop]
          · show (if p < w.length then Sum.inl (p + 1, q') else Sum.inr false) = _
            rw [if_neg (by omega)]
    | false =>
        rcases Nat.eq_zero_or_pos p with rfl | hpos
        · refine Or.inl ⟨?_, ?_⟩
          · rw [if_pos rfl]
          · show (if 0 < 0 then Sum.inl (0 - 1, q') else Sum.inr false) = _
            rw [if_neg (by omega)]
        · have hget : w[p - 1]? = some w[p - 1] :=
            List.getElem?_eq_getElem (by omega)
          have hdl : (w.take p).dropLast = w.take (p - 1) := by
            rw [List.dropLast_eq_take, List.length_take, show min p w.length = p by omega,
              List.take_take, show min (p - 1) p = p - 1 by omega]
          have hdrop : w[p - 1] :: w.drop p = w.drop (p - 1) := by
            have hd := List.drop_eq_getElem_cons (show p - 1 < w.length by omega)
            rw [show p - 1 + 1 = p by omega] at hd
            exact hd.symm
          refine Or.inr (Or.inr ⟨o, p - 1, q', by omega, ?_, ?_⟩)
          · rw [if_neg (show ¬ p = 0 by omega), hget]
            show some (o, Cfg.conf (w.take p).dropLast q' (w[p - 1] :: w.drop p)) = _
            rw [hdl, hdrop]
          · show (if 0 < p then Sum.inl (p - 1, q') else Sum.inr false) = _
            rw [if_pos hpos]

private lemma reaches_to_accepts (M : TwoWay A B Q) (w : List A) :
    ∀ {c : Cfg A Q} {o : List B} {d : Cfg A Q}, M.Reaches c o d → d = Cfg.halt →
      ∀ (p : ℕ) (q : Q), p ≤ w.length → c = Cfg.conf (w.take p) q (w.drop p) →
        ∃ n, ((haltDFA M).next w)^[n] (Sum.inl (p, q)) = Sum.inr true := by
  intro c o d hr
  induction hr with
  | refl c => intro hd p q _ hc; rw [hc] at hd; exact absurd hd (by simp)
  | @step c c' c'' o o' hs _ ih =>
      intro hd p q hp hc
      subst hc
      rcases step_corr M w p q hp with ⟨h1, h2⟩ | ⟨o'', h1, h2⟩ | ⟨o'', p', q', hp', h1, h2⟩
      · rw [h1] at hs; exact absurd hs (by simp)
      · rw [h1] at hs
        obtain ⟨-, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.injEq .. ▸ hs
        exact ⟨1, by simpa using h2⟩
      · rw [h1] at hs
        have hc' : c' = Cfg.conf (w.take p') q' (w.drop p') := by
          exact (Prod.mk.inj (Option.some.inj hs)).2.symm
        obtain ⟨n, hn⟩ := ih hd p' q' hp' hc'
        refine ⟨n + 1, ?_⟩
        rw [Function.iterate_succ_apply, h2, hn]

private lemma accepts_to_reaches (M : TwoWay A B Q) (w : List A) :
    ∀ (n : ℕ) (p : ℕ) (q : Q), p ≤ w.length →
      ((haltDFA M).next w)^[n] (Sum.inl (p, q)) = Sum.inr true →
        ∃ o : List B, M.Reaches (Cfg.conf (w.take p) q (w.drop p)) o Cfg.halt := by
  intro n
  induction n with
  | zero => intro p q _ h; exact absurd h (by simp)
  | succ n ih =>
      intro p q hp h
      rw [Function.iterate_succ_apply] at h
      rcases step_corr M w p q hp with ⟨h1, h2⟩ | ⟨o, h1, h2⟩ | ⟨o, p', q', hp', h1, h2⟩
      · rw [h2] at h; simp at h
      · exact ⟨o ++ [], TwoWay.Reaches.step h1 (TwoWay.Reaches.refl _)⟩
      · rw [h2] at h
        obtain ⟨o', ho'⟩ := ih p' q' hp' h
        exact ⟨o ++ o', TwoWay.Reaches.step h1 ho'⟩

lemma haltDFA_accepts (M : TwoWay A B Q) (w : List A) :
    (haltDFA M).Accepts w ↔ Halts M w := by
  have hstart : Cfg.conf (w.take 0) M.init (w.drop 0) = Cfg.conf [] M.init w := by simp
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨o, ho⟩ := accepts_to_reaches M w n 0 M.init (Nat.zero_le _) hn
    exact ⟨o, hstart ▸ ho⟩
  · rintro ⟨o, ho⟩
    exact reaches_to_accepts M w ho rfl 0 M.init (Nat.zero_le _) hstart.symm

/-- **Exercise `exer:2dfa-loop-elimination`.**  For a deterministic two-way transducer that is not
required to terminate, the set of input strings on which it does terminate is a regular
language. -/
theorem halts_isRegular [Finite A] [Finite Q] (M : TwoWay A B Q) :
    Language.IsRegular {w : List A | Halts M w} := by
  have : {w : List A | Halts M w} = {w : List A | (haltDFA M).Accepts w} := by
    ext w; exact (haltDFA_accepts M w).symm
  rw [this]
  exact (haltDFA M).accepts_isRegular

end Transducers.Exercises
