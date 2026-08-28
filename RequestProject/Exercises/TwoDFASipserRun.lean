/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): the machine steps of the searching automaton of
`RequestProject/Exercises/TwoDFASipserDef.lean`.

Each phase of the depth-first search is executed by one or two transitions of the automaton; the
lemmas below package these transitions into a *macro step* of the search, one lemma per phase.
-/
import RequestProject.Exercises.TwoDFASipserDef

namespace Transducers
namespace Exercises

open Transducers

variable {A R : Type}

/-! ## The machine steps of the search -/

section Run

variable [Fintype R] (N : TwoDFA A R) (w : List A)

/-- The letter to the left of the head at position `p`. -/
def lftLet (w : List A) (p : ℕ) : Option A := if p = 0 then none else w[p - 1]?

@[simp] lemma lftLet_zero : lftLet w 0 = none := rfl

lemma lftLet_eq_none_iff (hp : p ≤ w.length) : lftLet w p = none ↔ p = 0 := by
  unfold lftLet
  by_cases h : p = 0
  · simp [h]
  · simp only [if_neg h]
    rw [List.getElem?_eq_getElem (show p - 1 < w.length by omega)]
    simp [h]

lemma getElem?_eq_none_iff' (hp : p ≤ w.length) : w[p]? = none ↔ p = w.length := by
  rcases lt_or_eq_of_le hp with h | h
  · simp [List.getElem?_eq_getElem h]
    omega
  · simp [h]

/-- The automaton answers `b` when the transition function does. -/
lemma next_answer {p : ℕ} {st : DfsSt R} {b : Bool}
    (h : dfsStep N (lftLet w p) st w[p]? = Sum.inl b) :
    (dfsAut N).next w (Sum.inl (p, st)) = Sum.inr b := by
  dsimp only [TwoDFA.next]
  rw [show (dfsAut N).step (if p = 0 then none else w[p - 1]?) st w[p]? = Sum.inl b from h]

/-- The automaton moves right when the transition function says so. -/
lemma next_right {p : ℕ} {st st' : DfsSt R} (hp : p < w.length)
    (h : dfsStep N (lftLet w p) st w[p]? = Sum.inr (st', true)) :
    (dfsAut N).next w (Sum.inl (p, st)) = Sum.inl (p + 1, st') := by
  dsimp only [TwoDFA.next]
  rw [show (dfsAut N).step (if p = 0 then none else w[p - 1]?) st w[p]? = Sum.inr (st', true)
    from h]
  exact if_pos hp

/-- The automaton moves left when the transition function says so. -/
lemma next_left {p : ℕ} {st st' : DfsSt R} (hp : 0 < p)
    (h : dfsStep N (lftLet w p) st w[p]? = Sum.inr (st', false)) :
    (dfsAut N).next w (Sum.inl (p, st)) = Sum.inl (p - 1, st') := by
  dsimp only [TwoDFA.next]
  rw [show (dfsAut N).step (if p = 0 then none else w[p - 1]?) st w[p]? = Sum.inr (st', false)
    from h]
  exact if_pos hp

/-! ### The transition function, case by case -/

lemma dfsStep_inl {l x : Option A} (h : ¬(l = none ∧ x = none)) (ph : Dfs R) :
    dfsStep N l (Sum.inl ph) x = dfsPhase N l ph x := by
  rcases l with _ | a <;> rcases x with _ | b
  · exact absurd ⟨rfl, rfl⟩ h
  · rfl
  · rfl
  · rfl

lemma dfsStep_inr {l x : Option A} (h : ¬(l = none ∧ x = none)) (ph : Dfs R) (d : Bool) :
    dfsStep N l (Sum.inr (ph, d)) x = Sum.inr (Sum.inl ph, !d) := by
  rcases l with _ | a <;> rcases x with _ | b
  · exact absurd ⟨rfl, rfl⟩ h
  · rfl
  · rfl
  · rfl

lemma not_both_none (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) :
    ¬(lftLet w p = none ∧ w[p]? = none) := by
  rintro ⟨h1, h2⟩
  rw [lftLet_eq_none_iff w hp] at h1
  rw [getElem?_eq_none_iff' w hp] at h2
  exact hne (List.eq_nil_of_length_eq_zero (by omega))

/-! ### Reachability inside the search -/

/-- A configuration of the search: a position and a phase. -/
abbrev SCfg (R : Type) := ℕ × Dfs R

/-- A search configuration, or an answer, read as a configuration of the automaton. -/
def enc : SCfg R ⊕ Bool → TwoCfg (DfsSt R)
  | Sum.inl (p, ph) => Sum.inl (p, Sum.inl ph)
  | Sum.inr b => Sum.inr b

/-- The search started in the configuration `c` reaches `t`. -/
def SReach (N : TwoDFA A R) (w : List A) (c : SCfg R) (t : SCfg R ⊕ Bool) : Prop :=
  ∃ k, ((dfsAut N).next w)^[k] (Sum.inl (c.1, Sum.inl c.2)) = enc t

lemma SReach.refl (c : SCfg R) : SReach N w c (Sum.inl c) := ⟨0, rfl⟩

lemma SReach.trans {c c' : SCfg R} {t : SCfg R ⊕ Bool}
    (h1 : SReach N w c (Sum.inl c')) (h2 : SReach N w c' t) : SReach N w c t := by
  obtain ⟨p', ph'⟩ := c'
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [Function.iterate_add_apply, hk1]; exact hk2⟩

/-- One step of the automaton is a step of the search. -/
lemma SReach.one {p : ℕ} {ph : Dfs R} {t : SCfg R ⊕ Bool}
    (h : (dfsAut N).next w (Sum.inl (p, Sum.inl ph)) = enc t) : SReach N w (p, ph) t :=
  ⟨1, by simpa using h⟩

/-- A phase that only stays where it is: the head moves to a neighbour and comes back. -/
lemma sreach_stay (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {ph ph' : Dfs R}
    (h : dfsPhase N (lftLet w p) ph w[p]? = dfsStay ph' w[p]?) :
    SReach N w (p, ph) (Sum.inl (p, ph')) := by
  have hnb := not_both_none w hne hp
  have hstep : dfsStep N (lftLet w p) (Sum.inl ph) w[p]? = dfsStay ph' w[p]? := by
    rw [dfsStep_inl N hnb, h]
  rcases hx : w[p]? with _ | a
  · -- the head is at the right end; it moves left and comes back
    have hpn : p = w.length := (getElem?_eq_none_iff' w hp).1 hx
    have hp0 : 0 < p := by
      rcases Nat.eq_zero_or_pos w.length with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hne
      · omega
    have h1 : (dfsAut N).next w (Sum.inl (p, Sum.inl ph)) = Sum.inl (p - 1, Sum.inr (ph', false)) :=
      next_left N w hp0 (by rw [hstep, hx]; rfl)
    have hx' : w[p - 1]? = some w[p - 1] := List.getElem?_eq_getElem (by omega)
    have hnb' := not_both_none w hne (show p - 1 ≤ w.length by omega)
    have h2 : (dfsAut N).next w (Sum.inl (p - 1, Sum.inr (ph', false)))
        = Sum.inl (p - 1 + 1, Sum.inl ph') :=
      next_right N w (by omega) (by rw [dfsStep_inr N hnb']; rfl)
    refine ⟨2, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [h1, h2, show p - 1 + 1 = p by omega]
    rfl
  · -- the head moves right and comes back
    have hpn : p < w.length := by
      by_contra hc
      have : p = w.length := by omega
      rw [this] at hx
      simp at hx
    have h1 : (dfsAut N).next w (Sum.inl (p, Sum.inl ph)) = Sum.inl (p + 1, Sum.inr (ph', true)) :=
      next_right N w hpn (by rw [hstep, hx]; rfl)
    have hnb' := not_both_none w hne (show p + 1 ≤ w.length by omega)
    have h2 : (dfsAut N).next w (Sum.inl (p + 1, Sum.inr (ph', true)))
        = Sum.inl (p + 1 - 1, Sum.inl ph') :=
      next_left N w (by omega) (by rw [dfsStep_inr N hnb']; rfl)
    refine ⟨2, ?_⟩
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply]
    simp only [Function.iterate_one]
    rw [h1, h2, show p + 1 - 1 = p by omega]
    rfl

/-! ### The phases, one by one -/

/-- The transition of the searched automaton at the configuration `(p, r)`. -/
def cstep (N : TwoDFA A R) (w : List A) (p : ℕ) (r : R) : Bool ⊕ (R × Bool) :=
  N.step (lftLet w p) r w[p]?

variable {N w}

lemma dfsPhase_scanCur_init {l x : Option A} {r : R} (h : N.step l r x = Sum.inl true)
    (h2 : l.isNone ∧ r = N.init) : dfsPhase N l (Dfs.scanCur r) x = Sum.inl true := by
  simp only [dfsPhase, h]
  exact if_pos h2

lemma dfsPhase_scanCur_desc {l x : Option A} {r : R} (h : N.step l r x = Sum.inl true)
    (h2 : ¬(l.isNone ∧ r = N.init)) :
    dfsPhase N l (Dfs.scanCur r) x = dfsStay (Dfs.desc r) x := by
  simp only [dfsPhase, h]
  exact if_neg h2

lemma dfsPhase_scanCur_false {l x : Option A} {r : R} (h : N.step l r x = Sum.inl false) :
    dfsPhase N l (Dfs.scanCur r) x = dfsStay (Dfs.scanNext r) x := by
  simp only [dfsPhase, h]

lemma dfsPhase_scanCur_move {l x : Option A} {r : R} {y : R × Bool} (h : N.step l r x = Sum.inr y) :
    dfsPhase N l (Dfs.scanCur r) x = dfsStay (Dfs.scanNext r) x := by
  simp only [dfsPhase, h]

lemma dfsPhase_scanNext_succ {l x : Option A} {r r' : R} (h : rSucc r = some r') :
    dfsPhase N l (Dfs.scanNext r) x = dfsStay (Dfs.scanCur r') x := by
  simp only [dfsPhase, h]

lemma dfsPhase_scanNext_none {l : Option A} {r : R} {a : A} (h : rSucc r = none) :
    dfsPhase N l (Dfs.scanNext r) (some a)
      = Sum.inr (Sum.inl (Dfs.scanCur (rFirst N.init)), true) := by
  simp only [dfsPhase, h]

lemma dfsPhase_scanNext_end {l : Option A} {r : R} (h : rSucc r = none) :
    dfsPhase N l (Dfs.scanNext r) (none : Option A) = Sum.inl false := by
  simp only [dfsPhase, h]

lemma dfsPhase_desc_left {x : Option A} {r : R} {a : A} :
    dfsPhase N (some a) (Dfs.desc r) x
      = Sum.inr (Sum.inl (Dfs.chk r (rFirst N.init) true), false) := by
  simp only [dfsPhase]

lemma dfsPhase_desc_right {r : R} {a : A} :
    dfsPhase N none (Dfs.desc r) (some a)
      = Sum.inr (Sum.inl (Dfs.chk r (rFirst N.init) false), true) := by
  simp only [dfsPhase]

lemma dfsPhase_chk_init {l x : Option A} {q c : R} {s : Bool} (h : N.step l c x = Sum.inr (q, s))
    (h2 : l.isNone ∧ c = N.init) : dfsPhase N l (Dfs.chk q c s) x = Sum.inl true := by
  simp only [dfsPhase, if_pos h]
  exact if_pos h2

lemma dfsPhase_chk_desc {l x : Option A} {q c : R} {s : Bool} (h : N.step l c x = Sum.inr (q, s))
    (h2 : ¬(l.isNone ∧ c = N.init)) :
    dfsPhase N l (Dfs.chk q c s) x = dfsStay (Dfs.desc c) x := by
  simp only [dfsPhase, if_pos h]
  exact if_neg h2

lemma dfsPhase_chk_no {l x : Option A} {q c : R} {s : Bool} (h : N.step l c x ≠ Sum.inr (q, s)) :
    dfsPhase N l (Dfs.chk q c s) x = Sum.inr (Sum.inl (Dfs.cont q c s), s) := by
  simp only [dfsPhase, if_neg h]

lemma dfsPhase_cont_succ {l x : Option A} {q c c' : R} {s : Bool} (h : rSucc c = some c') :
    dfsPhase N l (Dfs.cont q c s) x = Sum.inr (Sum.inl (Dfs.chk q c' s), !s) := by
  simp only [dfsPhase, h]

lemma dfsPhase_cont_left_end {l : Option A} {q c : R} {a : A} (h : rSucc c = none) :
    dfsPhase N l (Dfs.cont q c true) (some a)
      = Sum.inr (Sum.inl (Dfs.chk q (rFirst N.init) false), true) := by
  simp only [dfsPhase, h]
  rfl

lemma dfsPhase_cont_left_none {l : Option A} {q c : R} (h : rSucc c = none) :
    dfsPhase N l (Dfs.cont q c true) (none : Option A) = dfsStay (Dfs.up q) (none : Option A) := by
  simp only [dfsPhase, h]
  rfl

lemma dfsPhase_cont_right {l x : Option A} {q c : R} (h : rSucc c = none) :
    dfsPhase N l (Dfs.cont q c false) x = dfsStay (Dfs.up q) x := by
  simp only [dfsPhase, h]
  rfl

lemma dfsPhase_up_true {l x : Option A} {q : R} (h : N.step l q x = Sum.inl true) :
    dfsPhase N l (Dfs.up q) x = dfsStay (Dfs.scanNext q) x := by
  simp only [dfsPhase, h]

lemma dfsPhase_up_false {l x : Option A} {q : R} (h : N.step l q x = Sum.inl false) :
    dfsPhase N l (Dfs.up q) x = Sum.inl false := by
  simp only [dfsPhase, h]

lemma dfsPhase_up_move {l x : Option A} {q q' : R} {d : Bool} (h : N.step l q x = Sum.inr (q', d)) :
    dfsPhase N l (Dfs.up q) x = Sum.inr (Sum.inl (Dfs.cont q' q d), d) := by
  simp only [dfsPhase, h]

variable (N w)

/-! ### The steps of the search -/

variable {N w}

lemma sreach_move_right (hne : w ≠ []) {p : ℕ} (hp : p < w.length) {ph ph' : Dfs R}
    (h : dfsPhase N (lftLet w p) ph w[p]? = Sum.inr (Sum.inl ph', true)) :
    SReach N w (p, ph) (Sum.inl (p + 1, ph')) :=
  SReach.one (N := N) (w := w) (next_right N w hp (by rw [dfsStep_inl N (not_both_none w hne (le_of_lt hp)), h]))

lemma sreach_move_left (hne : w ≠ []) {p : ℕ} (hp : 0 < p) (hple : p ≤ w.length) {ph ph' : Dfs R}
    (h : dfsPhase N (lftLet w p) ph w[p]? = Sum.inr (Sum.inl ph', false)) :
    SReach N w (p, ph) (Sum.inl (p - 1, ph')) :=
  SReach.one (N := N) (w := w) (next_left N w hp (by rw [dfsStep_inl N (not_both_none w hne hple), h]))

lemma sreach_answer (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {ph : Dfs R} {b : Bool}
    (h : dfsPhase N (lftLet w p) ph w[p]? = Sum.inl b) :
    SReach N w (p, ph) (Sum.inr b) :=
  SReach.one (N := N) (w := w) (next_answer N w (by rw [dfsStep_inl N (not_both_none w hne hp), h]))

variable (N w)

/-! ### The macro steps, phase by phase -/

lemma sreach_scanCur_init (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {r : R}
    (h : cstep N w p r = Sum.inl true) (h0 : p = 0) (hr : r = N.init) :
    SReach N w (p, Dfs.scanCur r) (Sum.inr true) := by
  refine sreach_answer hne hp (dfsPhase_scanCur_init h ⟨?_, hr⟩)
  rw [h0]
  rfl

lemma sreach_scanCur_desc (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {r : R}
    (h : cstep N w p r = Sum.inl true) (h2 : ¬(p = 0 ∧ r = N.init)) :
    SReach N w (p, Dfs.scanCur r) (Sum.inl (p, Dfs.desc r)) := by
  refine sreach_stay N w hne hp (dfsPhase_scanCur_desc h ?_)
  rintro ⟨hl, hr⟩
  exact h2 ⟨(lftLet_eq_none_iff w hp).1 (Option.isNone_iff_eq_none.1 hl), hr⟩

lemma sreach_scanCur_next (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {r : R}
    (h : cstep N w p r ≠ Sum.inl true) :
    SReach N w (p, Dfs.scanCur r) (Sum.inl (p, Dfs.scanNext r)) := by
  rcases hc : cstep N w p r with b | y
  · cases b with
    | true => exact absurd hc h
    | false => exact sreach_stay N w hne hp (dfsPhase_scanCur_false hc)
  · exact sreach_stay N w hne hp (dfsPhase_scanCur_move hc)

lemma sreach_scanNext_succ (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {r r' : R} (h : rSucc r = some r') :
    SReach N w (p, Dfs.scanNext r) (Sum.inl (p, Dfs.scanCur r')) :=
  sreach_stay N w hne hp (dfsPhase_scanNext_succ h)

lemma sreach_scanNext_move (hne : w ≠ []) {p : ℕ} (hp : p < w.length) {r : R} (h : rSucc r = none) :
    SReach N w (p, Dfs.scanNext r) (Sum.inl (p + 1, Dfs.scanCur (rFirst N.init))) := by
  refine sreach_move_right hne hp ?_
  rw [List.getElem?_eq_getElem hp]
  exact dfsPhase_scanNext_none h

lemma sreach_scanNext_end (hne : w ≠ []) {p : ℕ} (hp : p = w.length) {r : R} (h : rSucc r = none) :
    SReach N w (p, Dfs.scanNext r) (Sum.inr false) := by
  refine sreach_answer hne (le_of_eq hp) ?_
  rw [show w[p]? = none from (getElem?_eq_none_iff' w (le_of_eq hp)).2 hp]
  exact dfsPhase_scanNext_end h

lemma sreach_desc_left (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) (hp0 : 0 < p) {r : R} :
    SReach N w (p, Dfs.desc r) (Sum.inl (p - 1, Dfs.chk r (rFirst N.init) true)) := by
  refine sreach_move_left hne hp0 hp ?_
  rw [show lftLet w p = some w[p - 1] by
    rw [lftLet, if_neg (by omega), List.getElem?_eq_getElem (by omega)]]
  exact dfsPhase_desc_left

lemma sreach_desc_right (hne : w ≠ []) (hp : (0 : ℕ) < w.length) {r : R} :
    SReach N w (0, Dfs.desc r) (Sum.inl (0 + 1, Dfs.chk r (rFirst N.init) false)) := by
  refine sreach_move_right hne hp ?_
  rw [lftLet_zero, List.getElem?_eq_getElem hp]
  exact dfsPhase_desc_right

lemma sreach_chk_init (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {q c : R} {s : Bool}
    (h : cstep N w p c = Sum.inr (q, s)) (h0 : p = 0) (hc : c = N.init) :
    SReach N w (p, Dfs.chk q c s) (Sum.inr true) := by
  refine sreach_answer hne hp (dfsPhase_chk_init h ⟨?_, hc⟩)
  rw [h0]
  rfl

lemma sreach_chk_desc (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {q c : R} {s : Bool}
    (h : cstep N w p c = Sum.inr (q, s)) (h2 : ¬(p = 0 ∧ c = N.init)) :
    SReach N w (p, Dfs.chk q c s) (Sum.inl (p, Dfs.desc c)) := by
  refine sreach_stay N w hne hp (dfsPhase_chk_desc h ?_)
  rintro ⟨hl, hcc⟩
  exact h2 ⟨(lftLet_eq_none_iff w hp).1 (Option.isNone_iff_eq_none.1 hl), hcc⟩

lemma sreach_chk_no_left (hne : w ≠ []) {p : ℕ} (hp : p < w.length) {q c : R}
    (h : cstep N w p c ≠ Sum.inr (q, true)) :
    SReach N w (p, Dfs.chk q c true) (Sum.inl (p + 1, Dfs.cont q c true)) :=
  sreach_move_right hne hp (dfsPhase_chk_no h)

lemma sreach_chk_no_right (hne : w ≠ []) {p : ℕ} (hp0 : 0 < p) (hp : p ≤ w.length) {q c : R}
    (h : cstep N w p c ≠ Sum.inr (q, false)) :
    SReach N w (p, Dfs.chk q c false) (Sum.inl (p - 1, Dfs.cont q c false)) :=
  sreach_move_left hne hp0 hp (dfsPhase_chk_no h)

lemma sreach_cont_succ_left (hne : w ≠ []) {p : ℕ} (hp0 : 0 < p) (hp : p ≤ w.length) {q c c' : R}
    (h : rSucc c = some c') :
    SReach N w (p, Dfs.cont q c true) (Sum.inl (p - 1, Dfs.chk q c' true)) :=
  sreach_move_left hne hp0 hp (dfsPhase_cont_succ h)

lemma sreach_cont_succ_right (hne : w ≠ []) {p : ℕ} (hp : p < w.length) {q c c' : R} (h : rSucc c = some c') :
    SReach N w (p, Dfs.cont q c false) (Sum.inl (p + 1, Dfs.chk q c' false)) :=
  sreach_move_right hne hp (dfsPhase_cont_succ h)

lemma sreach_cont_left_switch (hne : w ≠ []) {p : ℕ} (hp : p < w.length) {q c : R} (h : rSucc c = none) :
    SReach N w (p, Dfs.cont q c true) (Sum.inl (p + 1, Dfs.chk q (rFirst N.init) false)) := by
  refine sreach_move_right hne hp ?_
  rw [List.getElem?_eq_getElem hp]
  exact dfsPhase_cont_left_end h

lemma sreach_cont_left_up (hne : w ≠ []) {p : ℕ} (hp : p = w.length) {q c : R} (h : rSucc c = none) :
    SReach N w (p, Dfs.cont q c true) (Sum.inl (p, Dfs.up q)) := by
  have hx : w[p]? = none := (getElem?_eq_none_iff' w (le_of_eq hp)).2 hp
  refine sreach_stay N w hne (le_of_eq hp) ?_
  rw [hx]
  exact dfsPhase_cont_left_none h

lemma sreach_cont_right_up (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {q c : R} (h : rSucc c = none) :
    SReach N w (p, Dfs.cont q c false) (Sum.inl (p, Dfs.up q)) :=
  sreach_stay N w hne hp (dfsPhase_cont_right h)

lemma sreach_up_root (hne : w ≠ []) {p : ℕ} (hp : p ≤ w.length) {q : R} (h : cstep N w p q = Sum.inl true) :
    SReach N w (p, Dfs.up q) (Sum.inl (p, Dfs.scanNext q)) :=
  sreach_stay N w hne hp (dfsPhase_up_true h)

lemma sreach_up_right (hne : w ≠ []) {p : ℕ} (hp : p < w.length) {q q' : R}
    (h : cstep N w p q = Sum.inr (q', true)) :
    SReach N w (p, Dfs.up q) (Sum.inl (p + 1, Dfs.cont q' q true)) :=
  sreach_move_right hne hp (dfsPhase_up_move h)

lemma sreach_up_left (hne : w ≠ []) {p : ℕ} (hp0 : 0 < p) (hp : p ≤ w.length) {q q' : R}
    (h : cstep N w p q = Sum.inr (q', false)) :
    SReach N w (p, Dfs.up q) (Sum.inl (p - 1, Dfs.cont q' q false)) :=
  sreach_move_left hne hp0 hp (dfsPhase_up_move h)

end Run
end Exercises
end Transducers
