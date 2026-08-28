/-
A two-way deterministic automaton that performs a fixed sequence of left-to-right passes.

This is the shape of automaton that the author's solution to Exercise `exer:2dfa-complexity` of the
chapter *Two-way transducers* (`2dfa.tex`) of *Transducers* (M. Bojańczyk) builds, and it is the
shape used by `RequestProject/Exercises/TwoDFAExp.lean` as well: the automaton runs one one-way
deterministic automaton after another over the input, rewinding to the left end between two
consecutive passes, and accepts when every pass accepts.  It is the state-economical form of the
closure of two-way languages under intersection (Exercise `exer:2dfa-boolean`): checking `k + 1`
conditions costs the *sum* of the numbers of states, plus one rewinding state per condition, and not
their product.

The input is required to be non-empty, because a pass has to move the head in order to begin and to
end.

`passAut` is the automaton, `card_passSt` counts its states, and `passAut_accepts` says that it
accepts exactly the non-empty inputs on which every pass accepts.
-/
import RequestProject.PartC.TwoDFA

namespace Transducers
namespace Exercises

open Transducers

/-! ## Steps of a two-way automaton -/

section Steps

variable {A R : Type}

/-- An unfolding of one step of a two-way automaton at a head position. -/
lemma twoDFA_next_inl (N : TwoDFA A R) (w : List A) (p : ℕ) (r : R) :
    N.next w (Sum.inl (p, r)) =
      match N.step (if p = 0 then none else w[p - 1]?) r w[p]? with
      | Sum.inl b => Sum.inr b
      | Sum.inr (r', true) => if p < w.length then Sum.inl (p + 1, r') else Sum.inr false
      | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false := rfl

/-- A step that moves the head to the right. -/
lemma twoDFA_next_right (N : TwoDFA A R) (w : List A) (p : ℕ) (r r' : R)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inr (r', true))
    (hp : p < w.length) : N.next w (Sum.inl (p, r)) = Sum.inl (p + 1, r') := by
  rw [twoDFA_next_inl, h]; exact if_pos hp

/-- A step that moves the head to the left. -/
lemma twoDFA_next_left (N : TwoDFA A R) (w : List A) (p : ℕ) (r r' : R)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inr (r', false))
    (hp : 0 < p) : N.next w (Sum.inl (p, r)) = Sum.inl (p - 1, r') := by
  rw [twoDFA_next_inl, h]; exact if_pos hp

/-- A halting step. -/
lemma twoDFA_next_halt (N : TwoDFA A R) (w : List A) (p : ℕ) (r : R) (b : Bool)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inl b) :
    N.next w (Sum.inl (p, r)) = Sum.inr b := by
  rw [twoDFA_next_inl, h]

end Steps

/-! ## A family of one-way passes -/

variable {A S : Type} {k : ℕ}

/-- A family of `k + 1` one-way deterministic automata over the alphabet `A`, all with the same
state set `S`: `init i` is the initial state of the `i`-th one, `tr i a` its transition on the
letter `a`, and `acc i` its acceptance condition. -/
structure PassFam (A S : Type) (k : ℕ) where
  /-- The initial state of the `i`-th pass. -/
  init : Fin (k + 1) → S
  /-- The transition function of the `i`-th pass. -/
  tr : Fin (k + 1) → A → S → S
  /-- The acceptance condition of the `i`-th pass. -/
  acc : Fin (k + 1) → S → Bool

/-- The states of the multi-pass automaton: either a *scanning* state, carrying the index of the
pass under way and the state of that pass, or a *rewinding* state, which walks back to the left end
of the input before the pass with the given index begins. -/
abbrev PassSt (S : Type) (k : ℕ) := (Fin (k + 1) × S) ⊕ Fin (k + 1)

/-- The transition function of the multi-pass automaton. -/
def passStep (F : PassFam A S k) :
    Option A → PassSt S k → Option A → Bool ⊕ (PassSt S k × Bool)
  | l, Sum.inr i, r =>
      match l with
      | some _ => Sum.inr (Sum.inr i, false)
      | none =>
          match r with
          | some a => Sum.inr (Sum.inl (i, F.tr i a (F.init i)), true)
          | none => Sum.inl false
  | _, Sum.inl (i, s), r =>
      match r with
      | some a => Sum.inr (Sum.inl (i, F.tr i a s), true)
      | none =>
          if F.acc i s then
            if h : (i : ℕ) + 1 < k + 1 then Sum.inr (Sum.inr ⟨(i : ℕ) + 1, h⟩, false)
            else Sum.inl true
          else Sum.inl false

/-- The multi-pass automaton: it runs the passes of `F` one after another, rewinding to the left end
of the input between two consecutive passes, and accepts when all of them accept. -/
def passAut (F : PassFam A S k) : TwoDFA A (PassSt S k) where
  init := Sum.inr 0
  step := passStep F

/-- The number of states of the multi-pass automaton: the *sum* of the numbers of states of the
passes, plus one rewinding state per pass. -/
lemma card_passSt [Fintype S] :
    Fintype.card (PassSt S k) = (k + 1) * Fintype.card S + (k + 1) := by
  simp [PassSt]

/-- The state reached by the `i`-th pass after reading `u`, starting from `s`. -/
def passFold (F : PassFam A S k) (i : Fin (k + 1)) (u : List A) (s : S) : S :=
  u.foldl (fun s a => F.tr i a s) s

@[simp] lemma passFold_nil (F : PassFam A S k) (i : Fin (k + 1)) (s : S) :
    passFold F i [] s = s := rfl

@[simp] lemma passFold_cons (F : PassFam A S k) (i : Fin (k + 1)) (a : A) (u : List A) (s : S) :
    passFold F i (a :: u) s = passFold F i u (F.tr i a s) := rfl

/-- The state in which the `i`-th pass finishes on the input `w`. -/
def passRun (F : PassFam A S k) (i : Fin (k + 1)) (w : List A) : S :=
  passFold F i w (F.init i)

/-! ## The run of the multi-pass automaton -/

section Run

variable (F : PassFam A S k) (w : List A)

/-- Rewinding: from the rewinding state at the position `j` the run reaches the left end. -/
lemma pass_rewind (i : Fin (k + 1)) :
    ∀ j, j ≤ w.length → ((passAut F).next w)^[j] (Sum.inl (j, Sum.inr i))
      = Sum.inl (0, Sum.inr i) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply]
      have hl : w[j]? = some (w[j]'(by omega)) := List.getElem?_eq_getElem (by omega)
      have hstep : (passAut F).step (if j + 1 = 0 then none else w[j + 1 - 1]?)
          (Sum.inr i) w[j + 1]? = Sum.inr (Sum.inr i, false) := by
        rw [if_neg (Nat.succ_ne_zero j)]
        simp only [Nat.add_sub_cancel, hl]
        rfl
      rw [twoDFA_next_left _ _ _ _ _ hstep (by omega)]
      simpa using ih (by omega)

/-- Scanning: from the scanning state at the position `j` the run reaches the right end, having fed
the rest of the input to the pass. -/
lemma pass_scan (i : Fin (k + 1)) :
    ∀ d j (s : S), j + d = w.length →
      ((passAut F).next w)^[d] (Sum.inl (j, Sum.inl (i, s)))
        = Sum.inl (w.length, Sum.inl (i, passFold F i (w.drop j) s)) := by
  intro d
  induction d with
  | zero =>
      intro j s hj
      rw [show j = w.length by omega]
      simp
  | succ d ih =>
      intro j s hj
      have hjlt : j < w.length := by omega
      rw [Function.iterate_succ_apply]
      have hr : w[j]? = some (w[j]'hjlt) := List.getElem?_eq_getElem hjlt
      have hstep : (passAut F).step (if j = 0 then none else w[j - 1]?)
          (Sum.inl (i, s)) w[j]?
          = Sum.inr (Sum.inl (i, F.tr i (w[j]'hjlt) s), true) := by
        rw [hr]; rfl
      rw [twoDFA_next_right _ _ _ _ _ hstep hjlt]
      rw [ih (j + 1) _ (by omega)]
      congr 1
      congr 1
      congr 1
      rw [List.drop_eq_getElem_cons hjlt]
      rfl

/-- Starting a pass: at the left end of a non-empty input the run enters the scanning state. -/
lemma pass_start (i : Fin (k + 1)) (hne : w ≠ []) :
    (passAut F).next w (Sum.inl (0, Sum.inr i))
      = Sum.inl (1, Sum.inl (i, F.tr i (w[0]'(List.length_pos_iff.2 hne)) (F.init i))) := by
  have h0 : 0 < w.length := List.length_pos_iff.2 hne
  have hr : w[0]? = some (w[0]'h0) := List.getElem?_eq_getElem h0
  have hstep : (passAut F).step (if (0 : ℕ) = 0 then none else w[0 - 1]?)
      (Sum.inr i) w[0]?
      = Sum.inr (Sum.inl (i, F.tr i (w[0]'h0) (F.init i)), true) := by
    rw [if_pos rfl, hr]; rfl
  exact twoDFA_next_right _ _ _ _ _ hstep h0

/-- One pass: from the rewinding state at the left end the run reaches the right end with the pass
finished. -/
lemma pass_phase (i : Fin (k + 1)) (hne : w ≠ []) :
    ((passAut F).next w)^[w.length] (Sum.inl (0, Sum.inr i))
      = Sum.inl (w.length, Sum.inl (i, passRun F i w)) := by
  have h0 : 0 < w.length := List.length_pos_iff.2 hne
  have hw : (w[0]'h0) :: w.drop 1 = w := by simpa using (List.drop_eq_getElem_cons h0).symm
  have key : passFold F i (w.drop 1) (F.tr i (w[0]'h0) (F.init i)) = passRun F i w := by
    rw [passRun, ← passFold_cons]
    congr 1
  have hlen : w.length = (w.length - 1) + 1 := by omega
  conv_lhs => rw [hlen]
  rw [Function.iterate_succ_apply, pass_start F w i hne,
    pass_scan F w i (w.length - 1) 1 _ (by omega), key]

/-- The end of a pass: the run either rejects, or goes on to the next pass, or accepts. -/
lemma pass_end (i : Fin (k + 1)) (hne : w ≠ []) (s : S) :
    (passAut F).next w (Sum.inl (w.length, Sum.inl (i, s)))
      = if F.acc i s then
          (if h : (i : ℕ) + 1 < k + 1 then Sum.inl (w.length - 1, Sum.inr ⟨(i : ℕ) + 1, h⟩)
           else Sum.inr true)
        else Sum.inr false := by
  have h0 : 0 < w.length := List.length_pos_iff.2 hne
  have hr : w[w.length]? = none := by simp
  have hstep : (passAut F).step (if w.length = 0 then none else w[w.length - 1]?)
      (Sum.inl (i, s)) w[w.length]?
      = if F.acc i s then
          (if h : (i : ℕ) + 1 < k + 1 then Sum.inr ((Sum.inr ⟨(i : ℕ) + 1, h⟩ : PassSt S k), false)
           else Sum.inl true)
        else Sum.inl false := by
    rw [hr]
    by_cases hacc : F.acc i s
    · simp only [hacc, if_true]
      by_cases hi : (i : ℕ) + 1 < k + 1
      · simp only [dif_pos hi]
        show (if F.acc i s then _ else _) = _
        simp [hacc, hi]
      · simp only [dif_neg hi]
        show (if F.acc i s then _ else _) = _
        simp [hacc, hi]
    · simp only [hacc, if_false, Bool.false_eq_true]
      show (if F.acc i s then _ else _) = _
      simp [hacc]
  by_cases hacc : F.acc i s
  · simp only [hacc, if_true] at hstep ⊢
    by_cases hi : (i : ℕ) + 1 < k + 1
    · simp only [dif_pos hi] at hstep ⊢
      exact twoDFA_next_left _ _ _ _ _ hstep h0
    · simp only [dif_neg hi] at hstep ⊢
      exact twoDFA_next_halt _ _ _ _ _ hstep
  · simp only [hacc, if_false, Bool.false_eq_true] at hstep ⊢
    exact twoDFA_next_halt _ _ _ _ _ hstep

/-- If the first `i` passes accept, the run reaches the left end ready to begin the `i`-th one. -/
lemma pass_reach (hne : w ≠ []) : ∀ i : Fin (k + 1),
    (∀ i' : Fin (k + 1), (i' : ℕ) < (i : ℕ) → F.acc i' (passRun F i' w) = true) →
      ∃ t, ((passAut F).next w)^[t] (Sum.inl (0, Sum.inr (0 : Fin (k + 1)))) =
        Sum.inl (0, Sum.inr i) := by
  have h0 : 0 < w.length := List.length_pos_iff.2 hne
  intro i
  obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m := ⟨_, rfl⟩
  induction m generalizing i with
  | zero =>
      intro _
      refine ⟨0, ?_⟩
      have : i = 0 := Fin.ext (by simpa using hm)
      rw [this]
      rfl
  | succ m ih =>
      intro hacc
      have hmlt : m < k + 1 := by omega
      have hprev : (∀ i' : Fin (k + 1), (i' : ℕ) < m → F.acc i' (passRun F i' w) = true) :=
        fun i' hi' => hacc i' (by omega)
      obtain ⟨t, ht⟩ := ih ⟨m, hmlt⟩ rfl hprev
      have hm' : F.acc (⟨m, hmlt⟩ : Fin (k + 1)) (passRun F ⟨m, hmlt⟩ w) = true :=
        hacc ⟨m, hmlt⟩ (by simp [hm])
      refine ⟨(w.length - 1) + (1 + (w.length + t)), ?_⟩
      rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply, ht,
        pass_phase F w _ hne, Function.iterate_one, pass_end F w _ hne, if_pos hm']
      have hi1 : m + 1 < k + 1 := by omega
      rw [dif_pos (show ((⟨m, hmlt⟩ : Fin (k + 1)) : ℕ) + 1 < k + 1 from hi1)]
      have hii : (⟨m + 1, hi1⟩ : Fin (k + 1)) = i := Fin.ext (by simpa using hm.symm)
      rw [pass_rewind F w (⟨m + 1, hi1⟩ : Fin (k + 1)) (w.length - 1) (by omega), hii]

/-- **The language of the multi-pass automaton.**  It accepts exactly the non-empty inputs on which
every pass accepts. -/
theorem passAut_accepts : (passAut F).Accepts w ↔ w ≠ [] ∧ ∀ i, F.acc i (passRun F i w) = true := by
  constructor
  · rintro ⟨t, ht⟩
    have hne : w ≠ [] := by
      rintro rfl
      have hstep : (passAut F).step (if (0 : ℕ) = 0 then none else ([] : List A)[0 - 1]?)
          (Sum.inr (0 : Fin (k + 1))) ([] : List A)[0]? = Sum.inl false := by
        rw [if_pos rfl]; rfl
      have h1 : ((passAut F).next ([] : List A))^[1]
          (Sum.inl (0, (passAut F).init)) = Sum.inr false := by
        rw [Function.iterate_one]
        exact twoDFA_next_halt _ _ _ _ _ hstep
      exact Bool.noConfusion (TwoDFA.answer_unique ht h1)
    refine ⟨hne, ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨i0, hi0⟩ := hcon
    -- take the least index at which a pass fails
    classical
    let P : ℕ → Prop := fun m => ∃ h : m < k + 1, F.acc ⟨m, h⟩ (passRun F ⟨m, h⟩ w) ≠ true
    have hP : ∃ m, P m := ⟨(i0 : ℕ), i0.isLt, by simpa using hi0⟩
    obtain ⟨hlt, hfail⟩ := Nat.find_spec (p := P) hP
    set m := Nat.find (p := P) hP with hmdef
    have hmin : ∀ i' : Fin (k + 1), (i' : ℕ) < m → F.acc i' (passRun F i' w) = true := by
      intro i' hi'
      by_contra hc
      have : P (i' : ℕ) := ⟨i'.isLt, by simpa using hc⟩
      exact absurd (Nat.find_le (h := hP) this) (by omega)
    obtain ⟨t0, ht0⟩ := pass_reach F w hne ⟨m, hlt⟩ hmin
    have hfalse : ((passAut F).next w)^[1 + (w.length + t0)]
        (Sum.inl (0, (passAut F).init)) = Sum.inr false := by
      rw [Function.iterate_add_apply, Function.iterate_add_apply]
      show ((passAut F).next w)^[1] (((passAut F).next w)^[w.length]
        (((passAut F).next w)^[t0] (Sum.inl (0, Sum.inr (0 : Fin (k + 1)))))) = _
      rw [ht0, pass_phase F w _ hne, Function.iterate_one, pass_end F w _ hne,
        if_neg (by simpa using hfail)]
    exact Bool.noConfusion (TwoDFA.answer_unique ht hfalse)
  · rintro ⟨hne, hacc⟩
    have hk : ((⟨k, by omega⟩ : Fin (k + 1)) : ℕ) = k := rfl
    obtain ⟨t, ht⟩ := pass_reach F w hne ⟨k, by omega⟩ (fun i' _ => hacc i')
    refine ⟨1 + (w.length + t), ?_⟩
    rw [Function.iterate_add_apply, Function.iterate_add_apply]
    show ((passAut F).next w)^[1] (((passAut F).next w)^[w.length]
      (((passAut F).next w)^[t] (Sum.inl (0, Sum.inr (0 : Fin (k + 1)))))) = _
    rw [ht, pass_phase F w _ hne, Function.iterate_one, pass_end F w _ hne,
      if_pos (hacc _), dif_neg (by rw [hk]; omega)]

end Run

end Exercises
end Transducers
