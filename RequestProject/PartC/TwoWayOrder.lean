/-
The *order* in which the run of a two-way transducer visits a cut of the input
is a regular property of the marked input.

`RequestProject/PartC/TwoWayVisit.lean` shows that the set of configurations that lie on the run is
regular: mark a cut of the input and a state, and the marked inputs whose run visits the marked cut
in the marked state form a regular language (`TwoWay.visitLang_isRegular`).  That is the information
needed to walk *backwards* along the run, and it is what the proof of Theorem
`thm:composition-of-two-way-transducers` uses.

The proof of the snake lemma (the induction step `Transducers.boundedWidth_isRegular_step` of
Theorem `thm:2dfa-decomposition-into-primes`) needs more: the record-breaking columns of the book
are defined by a recursion that refers to the *first* and the *last* visit to a column, so the
marking of the record-breakers requires knowing in which order the run visits a cut, not only which
states occur there.

This file supplies exactly that.  A cut is marked with a *pair* of states
`(q₁, q₂)`, and the two-way automaton `TwoWay.orderAut M` simulates `M` and
stops as soon as the run reaches the marked cut in one of the two marked
states: it accepts if that state is `q₁` and rejects if it is `q₂`.  By
Shepherdson's Theorem (`TwoDFA.accepts_isRegular`) the accepted language is
regular, and

* `TwoWay.visits_before_iff_accepts_left`,
* `TwoWay.visits_before_iff_accepts_right`

identify it: the run visits the marked cut in the state `q₁` at some time before
it has ever visited that cut in the state `q₂`.  Since the visits to a cut are
in pairwise distinct states (a repeated configuration would make the run loop),
these languages determine the time order of the visits to a cut completely.
-/
import RequestProject.PartC.TwoWayVisit

namespace Transducers

namespace TwoWay

variable {A B Q S : Type}

open scoped Classical

/-! ## The marker of a cut -/

/-- The marker of the cut between two letters: the letter to the right of the
cut may carry a marker `Sum.inl s` selecting the cut to its left, and the letter
to the left of the cut may carry a marker `Sum.inr s` selecting the cut to its
right. -/
def cutMark (ml mr : Option (S ⊕ S)) : Option S :=
  match mr with
  | some (Sum.inl s) => some s
  | _ =>
    match ml with
    | some (Sum.inr s) => some s
    | _ => none

/-- The letter to the left of the cut `i` of a marked string. -/
def prevLetter (z : List (Marked A S)) (i : ℕ) : Option (Marked A S) :=
  if i = 0 then none else z[i - 1]?

/-- The marker of the cut `i` of the marked string `z`. -/
def cutMarkOf (z : List (Marked A S)) (i : ℕ) : Option S :=
  cutMark ((prevLetter z i).bind Prod.snd) ((z[i]?).bind Prod.snd)

/-! ## The automaton -/

/-- One step of the simulation of `M` by a two-way automaton over the marked
alphabet: the automaton follows the run of `M`, and rejects if the run halts or
falls off the input. -/
def followStep (M : TwoWay A B Q) (l : Option (Marked A S)) (q : Q)
    (r : Option (Marked A S)) : Bool ⊕ (Q × Bool) :=
  match M.step (l.map Prod.fst) q (r.map Prod.fst) with
  | Sum.inl _ => Sum.inl false
  | Sum.inr (q', _, d) => Sum.inr (q', d)

/-- The two-way automaton that simulates `M` and stops as soon as the run
reaches the marked cut in one of the two marked states: it accepts if that state
is the first of the two, and rejects if it is the second. -/
noncomputable def orderAut (M : TwoWay A B Q) : TwoDFA (Marked A (Q × Q)) Q where
  init := M.init
  step := fun l q r =>
    match cutMark (l.bind Prod.snd) (r.bind Prod.snd) with
    | some (q₁, q₂) =>
        if q = q₁ then Sum.inl true
        else if q = q₂ then Sum.inl false
        else followStep M l q r
    | none => followStep M l q r

@[simp] lemma orderAut_init (M : TwoWay A B Q) : (orderAut M).init = M.init := rfl

variable (M : TwoWay A B Q)

/-- The run of `M` stops the automaton at the cut `i` if that cut is marked and
the state is one of the two marked states. -/
def StopsAt (z : List (Marked A (Q × Q))) (i : ℕ) (q : Q) : Prop :=
  ∃ q₁ q₂, cutMarkOf z i = some (q₁, q₂) ∧ (q = q₁ ∨ q = q₂)

lemma orderAut_step_accept {l r : Option (Marked A (Q × Q))} {q q₂ : Q}
    (h : cutMark (l.bind Prod.snd) (r.bind Prod.snd) = some (q, q₂)) :
    (orderAut M).step l q r = Sum.inl true := by
  simp only [orderAut, h, if_true]

lemma orderAut_step_reject {l r : Option (Marked A (Q × Q))} {q q₁ : Q}
    (h : cutMark (l.bind Prod.snd) (r.bind Prod.snd) = some (q₁, q))
    (hne : q ≠ q₁) :
    (orderAut M).step l q r = Sum.inl false := by
  simp only [orderAut, h, if_neg hne, if_true]

lemma orderAut_step_miss {l r : Option (Marked A (Q × Q))} {q : Q}
    (h : ∀ q₁ q₂, cutMark (l.bind Prod.snd) (r.bind Prod.snd) = some (q₁, q₂) →
      q ≠ q₁ ∧ q ≠ q₂) :
    (orderAut M).step l q r = followStep M l q r := by
  rcases hc : cutMark (l.bind Prod.snd) (r.bind Prod.snd) with _ | ⟨q₁, q₂⟩
  · simp only [orderAut, hc]
  · obtain ⟨h1, h2⟩ := h q₁ q₂ hc
    simp only [orderAut, hc, if_neg h1, if_neg h2]

/-- The marker read by the automaton at the cut `i` is the marker of that cut. -/
lemma cutMark_eq_cutMarkOf (z : List (Marked A S)) (i : ℕ) :
    cutMark (((if i = 0 then none else z[i - 1]?) : Option (Marked A S)).bind Prod.snd)
      ((z[i]?).bind Prod.snd) = cutMarkOf z i := rfl

/-! ## The run of the automaton follows the run of the transducer -/

/-- At a marked cut, in the first of the two marked states, the automaton
accepts. -/
lemma next_ordCfg_accept {z : List (Marked A (Q × Q))} {i : ℕ} {q q₂ : Q}
    (h : cutMarkOf z i = some (q, q₂)) :
    (orderAut M).next z (Sum.inl (i, q)) = Sum.inr true := by
  rw [TwoDFA.next, orderAut_step_accept M (by rw [cutMark_eq_cutMarkOf]; exact h)]

/-- At a marked cut, in the second of the two marked states, the automaton
rejects. -/
lemma next_ordCfg_reject {z : List (Marked A (Q × Q))} {i : ℕ} {q q₁ : Q}
    (h : cutMarkOf z i = some (q₁, q)) (hne : q ≠ q₁) :
    (orderAut M).next z (Sum.inl (i, q)) = Sum.inr false := by
  rw [TwoDFA.next, orderAut_step_reject M (by rw [cutMark_eq_cutMarkOf]; exact h) hne]

/-- Away from the marked cut, the automaton follows the run of `M`. -/
lemma next_ordCfg {z : List (Marked A (Q × Q))} {w u v : List A} {q : Q}
    (hz : z.map Prod.fst = w) (huv : u ++ v = w) (hnot : ¬ StopsAt z u.length q) :
    (orderAut M).next z (Sum.inl (u.length, q))
      = visCfgOpt ((M.stepCfg (Cfg.conf u q v)).map Prod.snd) := by
  have hlenz : z.length = w.length := by rw [← hz]; simp
  have hmap : ∀ i : ℕ, z[i]?.map Prod.fst = w[i]? := by
    intro i; rw [← hz, List.getElem?_map]
  have hleft : (if u.length = 0 then none else z[u.length - 1]?).map Prod.fst = u.getLast? := by
    by_cases hu : u = []
    · simp [hu]
    · have hpos : 0 < u.length := List.length_pos_iff.mpr hu
      rw [if_neg (by omega), hmap, ← huv, List.getElem?_append_left (by omega),
        List.getLast?_eq_getElem?]
  have hright : z[u.length]?.map Prod.fst = v.head? := by
    rw [hmap, ← huv, List.getElem?_append_right (le_refl _), Nat.sub_self,
      ← List.head?_eq_getElem?]
  have hlen : w.length = u.length + v.length := by rw [← huv]; simp
  have hnot' : ∀ q₁ q₂, cutMark
      (((if u.length = 0 then none else z[u.length - 1]?) : Option (Marked A (Q × Q))).bind
        Prod.snd) ((z[u.length]?).bind Prod.snd) = some (q₁, q₂) → q ≠ q₁ ∧ q ≠ q₂ := by
    intro q₁ q₂ hc
    rw [cutMark_eq_cutMarkOf] at hc
    constructor
    · intro hq; exact hnot ⟨q₁, q₂, hc, Or.inl hq⟩
    · intro hq; exact hnot ⟨q₁, q₂, hc, Or.inr hq⟩
  rw [TwoDFA.next, orderAut_step_miss M hnot']
  simp only [followStep]
  rw [hleft, hright]
  rcases hM : M.step u.getLast? q v.head? with o | ⟨q', o, dir⟩
  · rw [stepCfg_halt_eq M hM]
    rfl
  · cases dir with
    | true =>
        cases v with
        | nil =>
            rw [stepCfg_right_nil M hM]
            have : ¬ (u.length < z.length) := by rw [hlenz]; simp at hlen; omega
            simp only [visCfgOpt, Option.map_none, if_neg this]
        | cons b v' =>
            rw [stepCfg_right_cons M hM]
            have hlt : u.length < z.length := by rw [hlenz]; simp at hlen; omega
            simp only [visCfgOpt, visCfg, Option.map_some, if_pos hlt]
            simp
    | false =>
        rcases hu : u.getLast? with _ | b
        · rw [stepCfg_left_none M hu hM]
          have h0 : u.length = 0 := by
            rcases u with _ | ⟨c, u'⟩
            · simp
            · simp at hu
          simp only [visCfgOpt, Option.map_none, if_neg (by omega : ¬ (0 < u.length))]
        · rw [stepCfg_left_some M hu hM]
          have hpos : 0 < u.length := by
            rcases u with _ | ⟨c, u'⟩
            · simp at hu
            · simp
          simp only [visCfgOpt, visCfg, Option.map_some, if_pos hpos]
          simp

/-- As long as the run of `M` has not stopped the automaton, the run of the
automaton follows it. -/
lemma iterate_ordCfg {z : List (Marked A (Q × Q))} {w : List A} (hz : z.map Prod.fst = w) (t : ℕ)
    (hmiss : ∀ s < t, ∀ u q v, cfgAt M w s = some (Cfg.conf u q v) → ¬ StopsAt z u.length q) :
    ((orderAut M).next z)^[t] (Sum.inl (0, (orderAut M).init)) = visCfgOpt (cfgAt M w t) := by
  induction t with
  | zero => simp [visCfgOpt, visCfg, orderAut]
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih (fun s hs => hmiss s (by omega))]
      rcases hc : cfgAt M w t with _ | c
      · rw [cfgAt_none_succ M w hc]
        rfl
      · cases c with
        | halt =>
            rw [cfgAt_halt_succ M w hc]
            rfl
        | conf u q v =>
            have hnot := hmiss t (by omega) u q v hc
            rw [show visCfgOpt (some (Cfg.conf u q v)) = Sum.inl (u.length, q) from rfl,
              next_ordCfg M hz (cfgAt_append M w t hc) hnot, cfgAt_succ, hc]
            rfl

/-! ## What the automaton accepts -/

/-- **The automaton accepts exactly when the run reaches the marked cut in the
first of the two marked states before it reaches it in the second one.** -/
theorem orderAut_accepts_iff {z : List (Marked A (Q × Q))} {w : List A}
    (hz : z.map Prod.fst = w) :
    (orderAut M).Accepts z ↔
      ∃ t u q v, cfgAt M w t = some (Cfg.conf u q v) ∧
        (∃ q₂, cutMarkOf z u.length = some (q, q₂)) ∧
        ∀ s < t, ∀ u' q' v', cfgAt M w s = some (Cfg.conf u' q' v') →
          ¬ StopsAt z u'.length q' := by
  classical
  constructor
  · rintro ⟨n, hn⟩
    by_cases hex : ∃ t, ∃ u q v, cfgAt M w t = some (Cfg.conf u q v) ∧ StopsAt z u.length q
    · obtain ⟨u, q, v, hc, hstop⟩ := Nat.find_spec hex
      have hmiss : ∀ s < Nat.find hex, ∀ u q v,
          cfgAt M w s = some (Cfg.conf u q v) → ¬ StopsAt z u.length q := by
        intro s hs u₁ q₁ v₁ h₁ hh₁
        exact Nat.find_min hex hs ⟨u₁, q₁, v₁, h₁, hh₁⟩
      obtain ⟨q₁, q₂, hmark, hq⟩ := hstop
      by_cases hqq : q = q₁
      · subst hqq
        exact ⟨Nat.find hex, u, q, v, hc, ⟨q₂, hmark⟩, hmiss⟩
      · -- the run reaches the marked cut in the second marked state first, so the
        -- automaton rejects, contradicting the acceptance
        exfalso
        have hq2 : q = q₂ := hq.resolve_left hqq
        subst hq2
        have hrej : ((orderAut M).next z)^[Nat.find hex + 1]
            (Sum.inl (0, (orderAut M).init)) = Sum.inr false := by
          rw [Function.iterate_succ_apply', iterate_ordCfg M hz _ hmiss, hc]
          exact next_ordCfg_reject M hmark hqq
        have := TwoDFA.answer_unique hrej hn
        simp at this
    · exfalso
      push_neg at hex
      have hmiss : ∀ s < n, ∀ u q v, cfgAt M w s = some (Cfg.conf u q v) →
          ¬ StopsAt z u.length q := by
        intro s _ u q v hs hstop
        exact hex s u q v hs hstop
      rw [iterate_ordCfg M hz n hmiss] at hn
      rcases hcc : cfgAt M w n with _ | c
      · rw [hcc] at hn; exact absurd hn (by simp [visCfgOpt])
      · cases c with
        | halt => rw [hcc] at hn; exact absurd hn (by simp [visCfgOpt, visCfg])
        | conf u q v => rw [hcc] at hn; exact absurd hn (by simp [visCfgOpt, visCfg])
  · rintro ⟨t, u, q, v, hc, ⟨q₂, hmark⟩, hmiss⟩
    refine ⟨t + 1, ?_⟩
    rw [Function.iterate_succ_apply', iterate_ordCfg M hz t hmiss, hc]
    exact next_ordCfg_accept M hmark

/-! ## The two marked words -/

/-- The marker of a cut of a string with one marked letter, the marker selecting
the cut to the left of that letter. -/
lemma cutMarkOf_left (x : List A) (a : A) (y : List A) (s : S) (i : ℕ) :
    cutMarkOf (plainList S x ++ (a, some (Sum.inl s)) :: plainList S y) i
      = if i = x.length then some s else none := by
  have hget := getElem?_marked (Q := S) x (some (Sum.inl s)) a y
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [cutMarkOf, prevLetter, if_pos rfl]
    have h0 := hget 0
    by_cases hx : (0 : ℕ) = x.length
    · rw [if_pos hx] at h0
      rw [if_pos hx]
      rcases hz : (plainList S x ++ (a, some (Sum.inl s)) :: plainList S y)[0]?
        with _ | ⟨b, mk⟩
      · rw [hz] at h0; simp at h0
      · rw [hz] at h0
        simp only [Option.bind_some] at h0
        subst h0
        rfl
    · rw [if_neg hx] at h0
      rw [if_neg hx]
      rcases hz : (plainList S x ++ (a, some (Sum.inl s)) :: plainList S y)[0]?
        with _ | ⟨b, mk⟩
      · rfl
      · rw [hz] at h0
        simp only [Option.bind_some] at h0
        subst h0
        rfl
  · rw [cutMarkOf, prevLetter, if_neg (by omega)]
    have h0 := hget i
    have h1 := hget (i - 1)
    have hne : i - 1 ≠ x.length ∨ i = x.length + 1 := by omega
    by_cases hx : i = x.length
    · rw [if_pos hx] at h0
      rw [if_pos hx]
      rcases hz : (plainList S x ++ (a, some (Sum.inl s)) :: plainList S y)[i]?
        with _ | ⟨b, mk⟩
      · rw [hz] at h0; simp at h0
      · rw [hz] at h0
        simp only [Option.bind_some] at h0
        subst h0
        rfl
    · rw [if_neg hx] at h0
      rw [if_neg hx]
      have hmr : ((plainList S x ++ (a, some (Sum.inl s)) :: plainList S y)[i]?).bind Prod.snd
          = none := h0
      have hml : (((plainList S x ++ (a, some (Sum.inl s)) :: plainList S y)[i - 1]?).bind
          Prod.snd) = if i - 1 = x.length then some (Sum.inl s) else none := h1
      rw [hmr]
      rcases hml' : ((plainList S x ++ (a, some (Sum.inl s)) :: plainList S y)[i - 1]?).bind
        Prod.snd with _ | mk
      · rfl
      · rw [hml'] at hml
        by_cases hx' : i - 1 = x.length
        · rw [if_pos hx'] at hml
          have : mk = Sum.inl s := by simpa using hml
          subst this
          rfl
        · rw [if_neg hx'] at hml
          simp at hml

/-- The marker of a cut of a string with one marked letter, the marker selecting
the cut to the right of that letter. -/
lemma cutMarkOf_right (x : List A) (a : A) (y : List A) (s : S) (i : ℕ) :
    cutMarkOf (plainList S x ++ (a, some (Sum.inr s)) :: plainList S y) i
      = if i = x.length + 1 then some s else none := by
  have hget := getElem?_marked (Q := S) x (some (Sum.inr s)) a y
  have hmr : ((plainList S x ++ (a, some (Sum.inr s)) :: plainList S y)[i]?).bind Prod.snd
      = if i = x.length then some (Sum.inr s) else none := hget i
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [cutMarkOf, prevLetter, if_pos rfl, if_neg (by omega)]
    rcases hz : (plainList S x ++ (a, some (Sum.inr s)) :: plainList S y)[0]?
      with _ | ⟨b, mk⟩
    · rfl
    · rw [hz] at hmr
      simp only [Option.bind_some] at hmr
      subst hmr
      by_cases hx : (0 : ℕ) = x.length
      · rw [if_pos hx]; rfl
      · rw [if_neg hx]; rfl
  · rw [cutMarkOf, prevLetter, if_neg (by omega)]
    have hml : (((plainList S x ++ (a, some (Sum.inr s)) :: plainList S y)[i - 1]?).bind
        Prod.snd) = if i - 1 = x.length then some (Sum.inr s) else none := hget (i - 1)
    by_cases hx : i = x.length
    · -- the cut just before the marked letter carries no marker
      rw [if_neg (by omega)]
      rw [hmr, if_pos hx]
      have hx' : i - 1 ≠ x.length := by omega
      rw [hml, if_neg hx']
      rfl
    · rw [hmr, if_neg hx]
      by_cases hx' : i - 1 = x.length
      · rw [if_pos (by omega)]
        rw [hml, if_pos hx']
        rfl
      · rw [if_neg (by omega)]
        rw [hml, if_neg hx']
        rfl

/-! ## The order of the visits to a cut is a regular property -/

/-- The run of `M` on `w` reaches the configuration `c₁` at some time at which it
has never yet been in the configuration `c₂`.  For two configurations at the same
cut this says that the run visits that cut in the state of `c₁` before it ever
visits it in the state of `c₂`. -/
def VisitsBefore (M : TwoWay A B Q) (w : List A) (c₁ c₂ : Cfg A Q) : Prop :=
  ∃ t, cfgAt M w t = some c₁ ∧ ∀ s < t, cfgAt M w s ≠ some c₂

/-- **The run visits the cut before the marked letter in the state `q₁` before
it ever visits it in the state `q₂`** exactly when the automaton accepts the
input marked with the pair `(q₁, q₂)` to the left of the letter. -/
theorem visits_before_iff_accepts_left (x : List A) (a : A) (y : List A) (q₁ q₂ : Q) :
    VisitsBefore M (x ++ a :: y) (Cfg.conf x q₁ (a :: y)) (Cfg.conf x q₂ (a :: y)) ↔
      (orderAut M).Accepts
        (plainList (Q × Q) x ++ (a, some (Sum.inl (q₁, q₂))) :: plainList (Q × Q) y) := by
  classical
  set z := plainList (Q × Q) x ++ (a, some (Sum.inl (q₁, q₂))) :: plainList (Q × Q) y with hzdef
  have hz : z.map Prod.fst = x ++ a :: y := by
    simp [hzdef, plainList, Function.comp_def]
  have hmark : ∀ i, cutMarkOf z i = if i = x.length then some (q₁, q₂) else none :=
    cutMarkOf_left x a y (q₁, q₂)
  rw [orderAut_accepts_iff M hz]
  constructor
  · rintro ⟨t, ht, hbefore⟩
    -- take the first time at which the run is at the cut in the state `q₁`
    obtain ⟨t₀, ht₀t, ht₀, hmin⟩ : ∃ t₀ ≤ t, cfgAt M (x ++ a :: y) t₀
        = some (Cfg.conf x q₁ (a :: y)) ∧
        ∀ s < t₀, cfgAt M (x ++ a :: y) s ≠ some (Cfg.conf x q₁ (a :: y)) := by
      have hex : ∃ t, cfgAt M (x ++ a :: y) t = some (Cfg.conf x q₁ (a :: y)) := ⟨t, ht⟩
      exact ⟨Nat.find hex, Nat.find_le ht, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
    refine ⟨t₀, x, q₁, a :: y, ht₀, ⟨q₂, by rw [hmark, if_pos rfl]⟩, ?_⟩
    rintro s hs u' q' v' hc ⟨p₁, p₂, hp, hq'⟩
    rw [hmark] at hp
    by_cases hlen : u'.length = x.length
    · rw [if_pos hlen] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have huv : u' ++ v' = x ++ a :: y := cfgAt_append M _ s hc
      obtain ⟨rfl, rfl⟩ := List.append_inj huv hlen
      rcases hq' with rfl | rfl
      · exact hmin s hs hc
      · exact hbefore s (by omega) hc
    · rw [if_neg hlen] at hp
      simp at hp
  · rintro ⟨t, u, q, v, hc, ⟨p₂, hp⟩, hmiss⟩
    rw [hmark] at hp
    by_cases hlen : u.length = x.length
    · rw [if_pos hlen] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have huv : u ++ v = x ++ a :: y := cfgAt_append M _ t hc
      obtain ⟨rfl, rfl⟩ := List.append_inj huv hlen
      refine ⟨t, hc, ?_⟩
      intro s hs hcon
      exact hmiss s hs _ q₂ _ hcon ⟨q₁, q₂, by rw [hmark, if_pos rfl], Or.inr rfl⟩
    · rw [if_neg hlen] at hp
      simp at hp

/-- **The run visits the cut after the marked letter in the state `q₁` before it
ever visits it in the state `q₂`** exactly when the automaton accepts the input
marked with the pair `(q₁, q₂)` to the right of the letter. -/
theorem visits_before_iff_accepts_right (x : List A) (a : A) (y : List A) (q₁ q₂ : Q) :
    VisitsBefore M (x ++ a :: y) (Cfg.conf (x ++ [a]) q₁ y) (Cfg.conf (x ++ [a]) q₂ y) ↔
      (orderAut M).Accepts
        (plainList (Q × Q) x ++ (a, some (Sum.inr (q₁, q₂))) :: plainList (Q × Q) y) := by
  classical
  set z := plainList (Q × Q) x ++ (a, some (Sum.inr (q₁, q₂))) :: plainList (Q × Q) y with hzdef
  have hz : z.map Prod.fst = x ++ a :: y := by
    simp [hzdef, plainList, Function.comp_def]
  have hmark : ∀ i, cutMarkOf z i = if i = x.length + 1 then some (q₁, q₂) else none :=
    cutMarkOf_right x a y (q₁, q₂)
  have hxa : (x ++ [a]).length = x.length + 1 := by simp
  rw [orderAut_accepts_iff M hz]
  constructor
  · rintro ⟨t, ht, hbefore⟩
    obtain ⟨t₀, ht₀t, ht₀, hmin⟩ : ∃ t₀ ≤ t, cfgAt M (x ++ a :: y) t₀
        = some (Cfg.conf (x ++ [a]) q₁ y) ∧
        ∀ s < t₀, cfgAt M (x ++ a :: y) s ≠ some (Cfg.conf (x ++ [a]) q₁ y) := by
      have hex : ∃ t, cfgAt M (x ++ a :: y) t = some (Cfg.conf (x ++ [a]) q₁ y) := ⟨t, ht⟩
      exact ⟨Nat.find hex, Nat.find_le ht, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
    refine ⟨t₀, x ++ [a], q₁, y, ht₀, ⟨q₂, by rw [hmark, hxa, if_pos rfl]⟩, ?_⟩
    rintro s hs u' q' v' hc ⟨p₁, p₂, hp, hq'⟩
    rw [hmark] at hp
    by_cases hlen : u'.length = x.length + 1
    · rw [if_pos hlen] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have huv : u' ++ v' = x ++ a :: y := cfgAt_append M _ s hc
      have huv' : u' ++ v' = (x ++ [a]) ++ y := by simpa using huv
      obtain ⟨rfl, rfl⟩ := List.append_inj huv' (by rw [hlen, hxa])
      rcases hq' with rfl | rfl
      · exact hmin s hs hc
      · exact hbefore s (by omega) hc
    · rw [if_neg hlen] at hp
      simp at hp
  · rintro ⟨t, u, q, v, hc, ⟨p₂, hp⟩, hmiss⟩
    rw [hmark] at hp
    by_cases hlen : u.length = x.length + 1
    · rw [if_pos hlen] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      have huv : u ++ v = x ++ a :: y := cfgAt_append M _ t hc
      have huv' : u ++ v = (x ++ [a]) ++ y := by simpa using huv
      obtain ⟨rfl, rfl⟩ := List.append_inj huv' (by rw [hlen, hxa])
      refine ⟨t, hc, ?_⟩
      intro s hs hcon
      exact hmiss s hs _ q₂ _ hcon
        ⟨q₁, q₂, by rw [hmark, hxa, if_pos rfl], Or.inr rfl⟩
    · rw [if_neg hlen] at hp
      simp at hp

/-! ## `VisitsBefore` is a total order on the configurations of the run

The order in which the run passes through its configurations is a *linear*
order: two configurations of a run occur at two comparable times.  The first and
the last visit to a cut are therefore determined by the relation `VisitsBefore`
alone, which is what makes them readable from the annotation of
`RequestProject/PartC/TwoWayAnnotOrd.lean`. -/

variable {M} {w : List A} {c c₁ c₂ c₃ : Cfg A Q}

/-- The first time at which the run is in a configuration that it visits. -/
noncomputable def firstTime (M : TwoWay A B Q) (w : List A) (c : Cfg A Q) : ℕ :=
  open Classical in
  if h : Visits M w c then Nat.find h else 0

lemma cfgAt_firstTime (h : Visits M w c) : cfgAt M w (firstTime M w c) = some c := by
  classical
  rw [firstTime, dif_pos h]
  exact Nat.find_spec h

lemma firstTime_le {t : ℕ} (h : cfgAt M w t = some c) : firstTime M w c ≤ t := by
  classical
  have hv : Visits M w c := ⟨t, h⟩
  rw [firstTime, dif_pos hv]
  exact Nat.find_le h

/-- A visited configuration precedes itself: the relation is reflexive on the
run. -/
lemma visitsBefore_self (h : Visits M w c) : VisitsBefore M w c c := by
  refine ⟨firstTime M w c, cfgAt_firstTime h, ?_⟩
  intro s hs hcon
  exact absurd (firstTime_le hcon) (by omega)

lemma visits_of_visitsBefore (h : VisitsBefore M w c₁ c₂) : Visits M w c₁ :=
  ⟨h.choose, h.choose_spec.1⟩

/-- A configuration precedes itself exactly when it is visited. -/
lemma visitsBefore_self_iff : VisitsBefore M w c c ↔ Visits M w c :=
  ⟨visits_of_visitsBefore, visitsBefore_self⟩

/-- The relation is decided by the first times at which the two configurations
occur. -/
lemma visitsBefore_iff_firstTime_le (h₁ : Visits M w c₁) (h₂ : Visits M w c₂) :
    VisitsBefore M w c₁ c₂ ↔ firstTime M w c₁ ≤ firstTime M w c₂ := by
  constructor
  · rintro ⟨t, ht, hno⟩
    by_contra hcon
    push_neg at hcon
    have h1 : firstTime M w c₁ ≤ t := firstTime_le ht
    exact hno _ (by omega) (cfgAt_firstTime h₂)
  · intro hle
    refine ⟨firstTime M w c₁, cfgAt_firstTime h₁, ?_⟩
    intro s hs hcon
    exact absurd (firstTime_le hcon) (by omega)

/-- Two visited configurations of a run are comparable. -/
lemma visitsBefore_total (h₁ : Visits M w c₁) (h₂ : Visits M w c₂) :
    VisitsBefore M w c₁ c₂ ∨ VisitsBefore M w c₂ c₁ := by
  rcases le_total (firstTime M w c₁) (firstTime M w c₂) with h | h
  · exact Or.inl ((visitsBefore_iff_firstTime_le h₁ h₂).2 h)
  · exact Or.inr ((visitsBefore_iff_firstTime_le h₂ h₁).2 h)

/-- A visited configuration precedes a configuration that the run never
reaches. -/
lemma visitsBefore_of_not_visits (h : Visits M w c₁) (h₃ : ¬ Visits M w c₃) :
    VisitsBefore M w c₁ c₃ :=
  ⟨firstTime M w c₁, cfgAt_firstTime h, fun s _ hcon => h₃ ⟨s, hcon⟩⟩

/-- The relation is transitive. -/
lemma visitsBefore_trans (h₁ : VisitsBefore M w c₁ c₂) (h₂ : VisitsBefore M w c₂ c₃) :
    VisitsBefore M w c₁ c₃ := by
  have v₁ : Visits M w c₁ := visits_of_visitsBefore h₁
  have v₂ : Visits M w c₂ := visits_of_visitsBefore h₂
  by_cases v₃ : Visits M w c₃
  swap
  · exact visitsBefore_of_not_visits v₁ v₃
  have k₁ := (visitsBefore_iff_firstTime_le v₁ v₂).1 h₁
  have k₂ := (visitsBefore_iff_firstTime_le v₂ v₃).1 h₂
  exact (visitsBefore_iff_firstTime_le v₁ v₃).2 (by omega)

/-- Two configurations that precede each other are the same. -/
lemma visitsBefore_antisymm (h₁ : VisitsBefore M w c₁ c₂) (h₂ : VisitsBefore M w c₂ c₁) :
    c₁ = c₂ := by
  have v₁ : Visits M w c₁ := visits_of_visitsBefore h₁
  have v₂ : Visits M w c₂ := visits_of_visitsBefore h₂
  have k₁ := (visitsBefore_iff_firstTime_le v₁ v₂).1 h₁
  have k₂ := (visitsBefore_iff_firstTime_le v₂ v₁).1 h₂
  have heq : firstTime M w c₁ = firstTime M w c₂ := by omega
  have := cfgAt_firstTime v₁
  rw [heq, cfgAt_firstTime v₂] at this
  exact (Option.some_injective _ this).symm

/-! ## The first and the last visit to a cut -/

variable (M)

/-- The state `q` is the state of the *last* visit of the run to the cut between
`u` and `v`: the cut is visited in the state `q`, and every visit to it precedes
that one. -/
def IsLastVisitAt (M : TwoWay A B Q) (w u v : List A) (q : Q) : Prop :=
  ∀ q' : Q, Visits M w (Cfg.conf u q' v) → VisitsBefore M w (Cfg.conf u q' v) (Cfg.conf u q v)

/-- The state `q` is the state of the *first* visit of the run to the cut
between `u` and `v`. -/
def IsFirstVisitAt (M : TwoWay A B Q) (w u v : List A) (q : Q) : Prop :=
  ∀ q' : Q, Visits M w (Cfg.conf u q' v) → VisitsBefore M w (Cfg.conf u q v) (Cfg.conf u q' v)

variable {M}

/-- There is at most one state of the last visit to a cut. -/
lemma isLastVisitAt_unique {u v : List A} {q q' : Q} (h : IsLastVisitAt M w u v q)
    (h' : IsLastVisitAt M w u v q') (hq : Visits M w (Cfg.conf u q v))
    (hq' : Visits M w (Cfg.conf u q' v)) : q = q' := by
  have := visitsBefore_antisymm (h q' hq') (h' q hq)
  cases this
  rfl

/-- There is at most one state of the first visit to a cut. -/
lemma isFirstVisitAt_unique {u v : List A} {q q' : Q} (h : IsFirstVisitAt M w u v q)
    (h' : IsFirstVisitAt M w u v q') (hq : Visits M w (Cfg.conf u q v))
    (hq' : Visits M w (Cfg.conf u q' v)) : q = q' := by
  have := visitsBefore_antisymm (h q' hq') (h' q hq)
  cases this
  rfl

/-- **A visited cut has a last visit.** -/
theorem exists_isLastVisitAt [Finite Q] {u v : List A} {q₀ : Q}
    (hq₀ : Visits M w (Cfg.conf u q₀ v)) :
    ∃ q, Visits M w (Cfg.conf u q v) ∧ IsLastVisitAt M w u v q := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  set s : Finset Q := Finset.univ.filter (fun q => Visits M w (Cfg.conf u q v)) with hs
  have hne : s.Nonempty := ⟨q₀, by simp [hs, hq₀]⟩
  obtain ⟨q, hqs, hmax⟩ := s.exists_max_image (fun q => firstTime M w (Cfg.conf u q v)) hne
  have hq : Visits M w (Cfg.conf u q v) := by simpa [hs] using hqs
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have : q' ∈ s := by simp [hs, hq']
  exact (visitsBefore_iff_firstTime_le hq' hq).2 (hmax q' this)

/-- **A visited cut has a first visit.** -/
theorem exists_isFirstVisitAt [Finite Q] {u v : List A} {q₀ : Q}
    (hq₀ : Visits M w (Cfg.conf u q₀ v)) :
    ∃ q, Visits M w (Cfg.conf u q v) ∧ IsFirstVisitAt M w u v q := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  set s : Finset Q := Finset.univ.filter (fun q => Visits M w (Cfg.conf u q v)) with hs
  have hne : s.Nonempty := ⟨q₀, by simp [hs, hq₀]⟩
  obtain ⟨q, hqs, hmin⟩ := s.exists_min_image (fun q => firstTime M w (Cfg.conf u q v)) hne
  have hq : Visits M w (Cfg.conf u q v) := by simpa [hs] using hqs
  refine ⟨q, hq, ?_⟩
  intro q' hq'
  have : q' ∈ s := by simp [hs, hq']
  exact (visitsBefore_iff_firstTime_le hq hq').2 (hmin q' this)

variable (M)

/-- **The order of the visits to a cut is a regular property of the marked
input.**  The marked inputs whose run reaches the marked cut in the first of the
two marked states before it reaches it in the second one form a regular
language. -/
theorem orderLang_isRegular [Finite A] [Finite Q] :
    Language.IsRegular {z : List (Marked A (Q × Q)) | (orderAut M).Accepts z} :=
  TwoDFA.accepts_isRegular _

end TwoWay

end Transducers
