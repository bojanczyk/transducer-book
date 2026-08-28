/-
Exercise `exer:2dfa-complexity` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk).

The exercise asks for a deterministic two-way automaton whose shortest accepted string is
*exponential* in the number of states, and the author's solution proposes to check divisibility of
the input length by each of `p₁, …, pₙ`, using about `p₁ + ⋯ + pₙ` states, so that the shortest
accepted string has length `p₁ ⋯ pₙ`.

That construction is the one formalised here, for an arbitrary family of moduli and over a
one-letter input alphabet: `Transducers.Exercises.divAut` is the automaton, `divAut_accepts` says
that it accepts exactly the non-empty inputs whose length is divisible by every modulus,
`card_divSt` counts its states, and `divAut_shortest` identifies the shortest accepted string, whose
length is the least common multiple of the moduli.

**It does not prove the claim of the exercise**, and this file does not pretend that it does.  For
*distinct* moduli — and repeated moduli contribute nothing — the number of states `s` and the
shortest accepted string are related by

  `shortest ≤ s ^ √(2 s)`     (`divAut_shortest_le`),

because there are at most `√(2 s)` distinct moduli when they sum to at most `s`, and each of them is
at most `s`.  The right-hand side is `2 ^ O(√s · log s)`, which is superpolynomial in `s` but not
exponential in it: the author's family of automata does not exhibit an exponential shortest accepted
string.  (Specialising to distinct primes, as the solution does, changes nothing: the bound above
holds for any distinct moduli.)

The statement of the exercise is nevertheless true, by constructions that the book does not give;
nothing here is a counterexample to the exercise.  What is recorded is exactly what the author's
argument establishes.  Accordingly the exercise is *not* aliased in `RequestProject/Labels.lean`,
and `EXERCISES.md` continues to list it as not formalised, with the divergence spelled out.
-/
import RequestProject.PartC.TwoDFA
import Mathlib.Data.ZMod.Basic

namespace Transducers
namespace Exercises

open Transducers

/-- An unfolding of one step of a two-way automaton, convenient for computing runs. -/
private lemma next_inl {A R : Type} (N : TwoDFA A R) (w : List A) (p : ℕ) (r : R) :
    N.next w (Sum.inl (p, r)) =
      match N.step (if p = 0 then none else w[p - 1]?) r w[p]? with
      | Sum.inl b => Sum.inr b
      | Sum.inr (r', true) => if p < w.length then Sum.inl (p + 1, r') else Sum.inr false
      | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false := rfl

/-! ## The automaton of the author's solution -/

variable {k : ℕ}

/-- The states of the automaton that checks divisibility of the input length by each of the moduli
`q i + 1`: either a *scanning* state, which remembers the index `i` of the modulus being checked and
the length of the prefix read so far modulo `q i + 1`, or a *rewinding* state, which walks back to
the left end of the input before the check of the modulus with index `i` starts.

The moduli are written `q i + 1` so that they are positive; the family is indexed by `Fin (k + 1)`,
so that there is at least one of them. -/
abbrev DivSt (q : Fin (k + 1) → ℕ) : Type :=
  (Σ i : Fin (k + 1), ZMod (q i + 1)) ⊕ Fin (k + 1)

/-- The transition function of the author's automaton. -/
def divStep (q : Fin (k + 1) → ℕ) :
    Option Unit → DivSt q → Option Unit → Bool ⊕ (DivSt q × Bool)
  | l, Sum.inr i, _ =>
      match l with
      | some _ => Sum.inr (Sum.inr i, false)
      | none => Sum.inr (Sum.inl ⟨i, (1 : ZMod (q i + 1))⟩, true)
  | l, Sum.inl ⟨i, c⟩, r =>
      match r with
      | some _ => Sum.inr (Sum.inl ⟨i, c + 1⟩, true)
      | none =>
          if c ≠ 0 then Sum.inl false
          else
            match l with
            | none => Sum.inl false
            | some _ =>
                if h : (i : ℕ) + 1 < k + 1 then Sum.inr (Sum.inr ⟨(i : ℕ) + 1, h⟩, false)
                else Sum.inl true

/-- **The automaton of the author's solution to Exercise `exer:2dfa-complexity`.**  Over a
one-letter input alphabet it checks, one modulus after another, that the length of the input is
divisible by `q i + 1`, rewinding to the left end between two checks; the input is also required to
be non-empty. -/
def divAut (q : Fin (k + 1) → ℕ) : TwoDFA Unit (DivSt q) where
  init := Sum.inr 0
  step := divStep q

/-- The number of states of the automaton: the sum of the moduli, plus one rewinding state per
modulus.  This is the author's "proportional to the sum of the prime numbers". -/
lemma card_divSt (q : Fin (k + 1) → ℕ) :
    Fintype.card (DivSt q) = (∑ i, (q i + 1)) + (k + 1) := by
  simp [DivSt, Fintype.card_sigma]

/-! ## The run of the automaton -/

section Run

variable (q : Fin (k + 1) → ℕ) (m : ℕ)

/-- The input: `m` copies of the only letter. -/
private def inp (m : ℕ) : List Unit := List.replicate m ()

private lemma inp_length : (inp m).length = m := by simp [inp]

private lemma inp_get (p : ℕ) : (inp m)[p]? = if p < m then some () else none := by
  simp [inp, List.getElem?_replicate]

variable {q m}

/-- A step that moves the head to the right. -/
private lemma next_right {A R : Type} (N : TwoDFA A R) (w : List A) (p : ℕ) (r r' : R)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inr (r', true))
    (hp : p < w.length) : N.next w (Sum.inl (p, r)) = Sum.inl (p + 1, r') := by
  rw [next_inl, h]; exact if_pos hp

/-- A step that moves the head to the left. -/
private lemma next_left {A R : Type} (N : TwoDFA A R) (w : List A) (p : ℕ) (r r' : R)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inr (r', false))
    (hp : 0 < p) : N.next w (Sum.inl (p, r)) = Sum.inl (p - 1, r') := by
  rw [next_inl, h]; exact if_pos hp

/-- A step that would move the head out of the input to the right. -/
private lemma next_right_out {A R : Type} (N : TwoDFA A R) (w : List A) (p : ℕ) (r r' : R)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inr (r', true))
    (hp : ¬ p < w.length) : N.next w (Sum.inl (p, r)) = Sum.inr false := by
  rw [next_inl, h]; exact if_neg hp

/-- A halting step. -/
private lemma next_halt {A R : Type} (N : TwoDFA A R) (w : List A) (p : ℕ) (r : R) (b : Bool)
    (h : N.step (if p = 0 then none else w[p - 1]?) r w[p]? = Sum.inl b) :
    N.next w (Sum.inl (p, r)) = Sum.inr b := by
  rw [next_inl, h]

/-- Rewinding: from the rewinding state at the cut `j` the run reaches the left end. -/
private lemma rewind (i : Fin (k + 1)) :
    ∀ j, j ≤ m → ((divAut q).next (inp m))^[j] (Sum.inl (j, Sum.inr i))
      = Sum.inl (0, Sum.inr i) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      rw [Function.iterate_succ_apply]
      have hl : (inp m)[j]? = some () := by rw [inp_get]; exact if_pos (by omega)
      have hstep : (divAut q).step (if j + 1 = 0 then none else (inp m)[j + 1 - 1]?)
          (Sum.inr i) (inp m)[j + 1]? = Sum.inr (Sum.inr i, false) := by
        rw [if_neg (Nat.succ_ne_zero j)]
        simp only [Nat.add_sub_cancel, hl]
        rfl
      rw [next_left _ _ _ _ _ hstep (by omega)]
      simpa using ih (by omega)

/-- Scanning: from the scanning state at the cut `j`, with the counter at `j` modulo the modulus,
the run reaches the right end with the counter at `m` modulo the modulus. -/
private lemma scan (i : Fin (k + 1)) :
    ∀ d j, j + d = m → ((divAut q).next (inp m))^[d]
        (Sum.inl (j, Sum.inl ⟨i, ((j : ℕ) : ZMod (q i + 1))⟩))
      = Sum.inl (m, Sum.inl ⟨i, ((m : ℕ) : ZMod (q i + 1))⟩) := by
  intro d
  induction d with
  | zero => intro j hj; rw [show j = m by omega]; rfl
  | succ d ih =>
      intro j hj
      rw [Function.iterate_succ_apply]
      have hr : (inp m)[j]? = some () := by rw [inp_get]; exact if_pos (by omega)
      have hstep : (divAut q).step (if j = 0 then none else (inp m)[j - 1]?)
          (Sum.inl ⟨i, ((j : ℕ) : ZMod (q i + 1))⟩) (inp m)[j]?
          = Sum.inr (Sum.inl ⟨i, ((j : ℕ) : ZMod (q i + 1)) + 1⟩, true) := by
        rw [hr]; rfl
      rw [next_right _ _ _ _ _ hstep (by rw [inp_length]; omega)]
      have hcast : ((j : ℕ) : ZMod (q i + 1)) + 1 = (((j + 1 : ℕ)) : ZMod (q i + 1)) := by
        push_cast; ring
      rw [hcast]
      exact ih (j + 1) (by omega)

/-- Starting a check: at the left end of a non-empty input the run enters the scanning state. -/
private lemma startPhase (i : Fin (k + 1)) (hm : 0 < m) :
    (divAut q).next (inp m) (Sum.inl (0, Sum.inr i))
      = Sum.inl (1, Sum.inl ⟨i, ((1 : ℕ) : ZMod (q i + 1))⟩) := by
  have hstep : (divAut q).step (if (0 : ℕ) = 0 then none else (inp m)[0 - 1]?)
      (Sum.inr i) (inp m)[0]? = Sum.inr (Sum.inl ⟨i, (1 : ZMod (q i + 1))⟩, true) := by
    rw [if_pos rfl]; rfl
  have := next_right (divAut q) (inp m) 0 (Sum.inr i) _ hstep (by rw [inp_length]; omega)
  rw [this]
  norm_num

/-- The end of a check: the run either rejects, or goes on to the next modulus, or accepts. -/
private lemma endPhase (i : Fin (k + 1)) (hm : 0 < m) (c : ZMod (q i + 1)) :
    (divAut q).next (inp m) (Sum.inl (m, Sum.inl ⟨i, c⟩))
      = if c ≠ 0 then Sum.inr false
        else if h : (i : ℕ) + 1 < k + 1 then Sum.inl (m - 1, Sum.inr ⟨(i : ℕ) + 1, h⟩)
        else Sum.inr true := by
  have hr : (inp m)[m]? = none := by rw [inp_get]; exact if_neg (by omega)
  have hl : (inp m)[m - 1]? = some () := by rw [inp_get]; exact if_pos (by omega)
  have hstep : (divAut q).step (if m = 0 then none else (inp m)[m - 1]?)
      (Sum.inl ⟨i, c⟩) (inp m)[m]?
      = if c ≠ 0 then Sum.inl false
        else if h : (i : ℕ) + 1 < k + 1 then Sum.inr (Sum.inr ⟨(i : ℕ) + 1, h⟩, false)
        else Sum.inl true := by
    rw [if_neg (by omega), hl, hr]
    rfl
  by_cases hc : c ≠ 0
  · rw [if_pos hc]
    exact next_halt _ _ _ _ _ (by rw [hstep, if_pos hc])
  · rw [if_neg hc]
    by_cases h : (i : ℕ) + 1 < k + 1
    · rw [dif_pos h]
      exact next_left _ _ _ _ _ (by rw [hstep, if_neg hc, dif_pos h]) hm
    · rw [dif_neg h]
      exact next_halt _ _ _ _ _ (by rw [hstep, if_neg hc, dif_neg h])

/-- The whole of one check, when the modulus divides the length: the run returns to the left end,
ready for the next modulus. -/
private lemma phase_pass (i : Fin (k + 1)) (hm : 0 < m) (hdvd : (q i + 1) ∣ m)
    (h : (i : ℕ) + 1 < k + 1) :
    ((divAut q).next (inp m))^[(m - 1) + (1 + ((m - 1) + 1))] (Sum.inl (0, Sum.inr i))
      = Sum.inl (0, Sum.inr ⟨(i : ℕ) + 1, h⟩) := by
  have hzero : ((m : ℕ) : ZMod (q i + 1)) = 0 := (ZMod.natCast_eq_zero_iff m _).mpr hdvd
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_one, startPhase i hm, scan i (m - 1) 1 (by omega), hzero,
    endPhase i hm, if_neg (by simp), dif_pos h]
  exact rewind _ (m - 1) (by omega)

/-- The last check, when the modulus divides the length: the run accepts. -/
private lemma phase_accept (i : Fin (k + 1)) (hm : 0 < m) (hdvd : (q i + 1) ∣ m)
    (h : ¬ ((i : ℕ) + 1 < k + 1)) :
    ((divAut q).next (inp m))^[1 + ((m - 1) + 1)] (Sum.inl (0, Sum.inr i)) = Sum.inr true := by
  have hzero : ((m : ℕ) : ZMod (q i + 1)) = 0 := (ZMod.natCast_eq_zero_iff m _).mpr hdvd
  rw [Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_one, startPhase i hm, scan i (m - 1) 1 (by omega), hzero,
    endPhase i hm, if_neg (by simp), dif_neg h]

/-- A check that fails: the run rejects. -/
private lemma phase_fail (i : Fin (k + 1)) (hm : 0 < m) (hdvd : ¬ ((q i + 1) ∣ m)) :
    ((divAut q).next (inp m))^[1 + ((m - 1) + 1)] (Sum.inl (0, Sum.inr i)) = Sum.inr false := by
  have hzero : ((m : ℕ) : ZMod (q i + 1)) ≠ 0 := by
    intro hc
    exact hdvd ((ZMod.natCast_eq_zero_iff m _).mp hc)
  rw [Function.iterate_add_apply, Function.iterate_add_apply,
    Function.iterate_one, startPhase i hm, scan i (m - 1) 1 (by omega),
    endPhase i hm, if_pos hzero]

/-- On the empty input the run rejects. -/
private lemma run_nil : ((divAut q).next (inp 0))^[1] (Sum.inl (0, (divAut q).init))
    = Sum.inr false := by
  rw [Function.iterate_one]
  have hstep : (divAut q).step (if (0 : ℕ) = 0 then none else (inp 0)[0 - 1]?)
      (Sum.inr (0 : Fin (k + 1))) (inp 0)[0]?
      = Sum.inr (Sum.inl ⟨0, (1 : ZMod (q 0 + 1))⟩, true) := by
    rw [if_pos rfl]; rfl
  exact next_right_out (divAut q) (inp 0) 0 _ _ hstep (by rw [inp_length]; omega)

/-- If every remaining modulus divides the length, the run accepts. -/
private lemma accept_from (hm : 0 < m) :
    ∀ d (i : ℕ) (hi : i < k + 1), i + d = k →
      (∀ (j : ℕ) (hj : j < k + 1), i ≤ j → (q ⟨j, hj⟩ + 1) ∣ m) →
      ∃ t, ((divAut q).next (inp m))^[t] (Sum.inl (0, Sum.inr ⟨i, hi⟩)) = Sum.inr true := by
  intro d
  induction d with
  | zero =>
      intro i hi hik hall
      exact ⟨1 + ((m - 1) + 1), phase_accept ⟨i, hi⟩ hm (hall i hi (le_refl i))
        (fun hc => absurd (show i + 1 < k + 1 from hc) (by omega))⟩
  | succ d ih =>
      intro i hi hik hall
      have hlt : i + 1 < k + 1 := by omega
      obtain ⟨t, ht⟩ := ih (i + 1) hlt (by omega) (fun j hj hij => hall j hj (by omega))
      refine ⟨t + ((m - 1) + (1 + ((m - 1) + 1))), ?_⟩
      rw [Function.iterate_add_apply]
      have := phase_pass (q := q) ⟨i, hi⟩ hm (hall i hi (le_refl i)) (by simpa using hlt)
      rw [this]
      exact ht

/-- If some remaining modulus does not divide the length, the run rejects. -/
private lemma reject_from (hm : 0 < m) :
    ∀ d (i : ℕ) (hi : i < k + 1), i + d = k →
      (∃ (j : ℕ) (hj : j < k + 1), i ≤ j ∧ ¬ ((q ⟨j, hj⟩ + 1) ∣ m)) →
      ∃ t, ((divAut q).next (inp m))^[t] (Sum.inl (0, Sum.inr ⟨i, hi⟩)) = Sum.inr false := by
  intro d
  induction d with
  | zero =>
      intro i hi hik hbad
      obtain ⟨j, hj, hij, hnd⟩ := hbad
      have : j = i := by omega
      subst this
      exact ⟨1 + ((m - 1) + 1), phase_fail ⟨j, hi⟩ hm (by simpa using hnd)⟩
  | succ d ih =>
      intro i hi hik hbad
      by_cases hi0 : (q ⟨i, hi⟩ + 1) ∣ m
      · obtain ⟨j, hj, hij, hnd⟩ := hbad
        have hne : i ≠ j := by
          intro hc; subst hc; exact hnd hi0
        have hlt : i + 1 < k + 1 := by omega
        obtain ⟨t, ht⟩ := ih (i + 1) hlt (by omega) ⟨j, hj, by omega, hnd⟩
        refine ⟨t + ((m - 1) + (1 + ((m - 1) + 1))), ?_⟩
        rw [Function.iterate_add_apply]
        rw [phase_pass (q := q) ⟨i, hi⟩ hm hi0 (by simpa using hlt)]
        exact ht
      · exact ⟨1 + ((m - 1) + 1), phase_fail ⟨i, hi⟩ hm hi0⟩

end Run

/-! ## What the automaton accepts -/

/-- **The automaton of the author's solution accepts exactly the non-empty inputs whose length is
divisible by every modulus.** -/
theorem divAut_accepts (q : Fin (k + 1) → ℕ) (w : List Unit) :
    (divAut q).Accepts w ↔ (0 < w.length ∧ ∀ i, (q i + 1) ∣ w.length) := by
  have hw : ∀ v : List Unit, v = inp v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons a v ih =>
        cases a
        show _ = List.replicate (v.length + 1) ()
        rw [List.replicate_succ]
        exact congrArg _ ih
  obtain ⟨m, rfl⟩ : ∃ m, w = inp m := ⟨w.length, hw w⟩
  rw [inp_length]
  constructor
  · intro hacc
    by_contra hcon
    obtain ⟨t, ht⟩ := hacc
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact absurd (TwoDFA.answer_unique ht run_nil) (by simp)
    · have hbad : ∃ (j : ℕ) (hj : j < k + 1), 0 ≤ j ∧ ¬ ((q ⟨j, hj⟩ + 1) ∣ m) := by
        by_contra hall
        push_neg at hall
        refine hcon ⟨hpos, fun i => ?_⟩
        have := hall (i : ℕ) i.isLt (Nat.zero_le _)
        simpa using this
      obtain ⟨t', ht'⟩ := reject_from (q := q) (m := m) hpos k 0 (by omega) (by omega) hbad
      have hinit : ((divAut q).init) = Sum.inr (⟨0, by omega⟩ : Fin (k + 1)) := rfl
      rw [hinit] at ht
      exact absurd (TwoDFA.answer_unique ht ht') (by simp)
  · rintro ⟨hpos, hall⟩
    obtain ⟨t, ht⟩ := accept_from (q := q) (m := m) hpos k 0 (by omega) (by omega)
      (fun j hj _ => hall ⟨j, hj⟩)
    exact ⟨t, ht⟩

/-- The least common multiple of the moduli. -/
noncomputable def divLcm (q : Fin (k + 1) → ℕ) : ℕ :=
  (Finset.univ : Finset (Fin (k + 1))).lcm (fun i => q i + 1)

lemma divLcm_pos (q : Fin (k + 1) → ℕ) : 0 < divLcm q := by
  refine Nat.pos_of_ne_zero (fun h => ?_)
  rw [divLcm, Finset.lcm_eq_zero_iff] at h
  obtain ⟨i, -, hi⟩ := h
  omega

lemma dvd_divLcm_iff (q : Fin (k + 1) → ℕ) (x : ℕ) :
    (∀ i, (q i + 1) ∣ x) ↔ divLcm q ∣ x := by
  constructor
  · intro h
    exact Finset.lcm_dvd (fun i _ => h i)
  · intro h i
    exact dvd_trans (Finset.dvd_lcm (f := fun i => q i + 1) (Finset.mem_univ i)) h

/-- **The shortest accepted string.**  The automaton accepts a string exactly when its length is a
positive multiple of the least common multiple of the moduli; so the shortest accepted string
consists of `divLcm q` letters.  For pairwise coprime moduli, as in the author's solution, this is
their product. -/
theorem divAut_shortest (q : Fin (k + 1) → ℕ) :
    (divAut q).Accepts (List.replicate (divLcm q) ()) ∧
      ∀ w : List Unit, (divAut q).Accepts w → divLcm q ≤ w.length := by
  constructor
  · rw [divAut_accepts]
    refine ⟨by simpa using divLcm_pos q, fun i => ?_⟩
    simpa using (dvd_divLcm_iff q (divLcm q)).mpr dvd_rfl i
  · intro w hw
    rw [divAut_accepts] at hw
    exact Nat.le_of_dvd hw.1 ((dvd_divLcm_iff q w.length).mp hw.2)

/-! ## The divergence: the author's construction is not exponential -/

/-- A finite set of positive natural numbers has at most `√(2 s)` elements, where `s` is its sum:
its `N` elements are distinct positive integers, so their sum is at least `N (N + 1) / 2`. -/
lemma card_sq_le_two_mul_sum (S : Finset ℕ) (hS : ∀ x ∈ S, 0 < x) :
    S.card * S.card ≤ 2 * ∑ x ∈ S, x := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simp
      · obtain ⟨M, hM, hmax⟩ := S.exists_max_image id hne
        have hsub : S.erase M ⊂ S := Finset.erase_ssubset hM
        have hcard : (S.erase M).card + 1 = S.card := by
          rw [Finset.card_erase_of_mem hM]
          have : 0 < S.card := Finset.card_pos.mpr hne
          omega
        have hih := ih (S.erase M) hsub (fun x hx => hS x (Finset.mem_of_mem_erase hx))
        have hMcard : S.card ≤ M := by
          have hsub2 : S ⊆ Finset.Icc 1 M := by
            intro x hx
            exact Finset.mem_Icc.mpr ⟨hS x hx, hmax x hx⟩
          have := Finset.card_le_card hsub2
          simpa using this
        have hsum : ∑ x ∈ S, x = M + ∑ x ∈ S.erase M, x := by
          rw [← Finset.sum_erase_add S _ hM]
          omega
        rw [hsum]
        nlinarith [hih, hMcard, hcard]

/-- **The divergence.**  For *distinct* moduli the shortest accepted string of the author's
automaton is at most `s ^ √(2 s)`, where `s` is the number of states.  This is `2 ^ O(√s log s)`:
superpolynomial in the number of states, but not exponential in it, so the author's construction
does not establish the claim of the exercise. -/
theorem divAut_shortest_le (q : Fin (k + 1) → ℕ)
    (hinj : Function.Injective (fun i => q i + 1)) :
    divLcm q ≤ (Fintype.card (DivSt q)) ^ Nat.sqrt (2 * Fintype.card (DivSt q)) := by
  classical
  set s := Fintype.card (DivSt q) with hs
  have hcard : s = (∑ i, (q i + 1)) + (k + 1) := card_divSt q
  -- the moduli, as a finite set
  set S : Finset ℕ := Finset.image (fun i => q i + 1) Finset.univ with hSdef
  have hScard : S.card = k + 1 := by
    rw [hSdef, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hSsum : ∑ x ∈ S, x = ∑ i, (q i + 1) := by
    rw [hSdef, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rw [hSdef, Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    omega
  -- the number of moduli is at most `√(2 s)`
  have hNsq : (k + 1) * (k + 1) ≤ 2 * s := by
    have := card_sq_le_two_mul_sum S hSpos
    rw [hScard, hSsum] at this
    omega
  have hN : k + 1 ≤ Nat.sqrt (2 * s) := Nat.le_sqrt.mpr hNsq
  -- each modulus is at most `s`
  have hmod : ∀ i, q i + 1 ≤ s := by
    intro i
    have : q i + 1 ≤ ∑ j, (q j + 1) :=
      Finset.single_le_sum (f := fun j => q j + 1) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hspos : 0 < s := by
    have := hmod 0
    omega
  -- the least common multiple divides the product
  have hdvd : divLcm q ∣ ∏ i, (q i + 1) :=
    Finset.lcm_dvd (fun i _ => Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hprodpos : 0 < ∏ i, (q i + 1) :=
    Finset.prod_pos (fun i _ => Nat.succ_pos _)
  have hle : divLcm q ≤ ∏ i, (q i + 1) := Nat.le_of_dvd hprodpos hdvd
  have hprod : ∏ i, (q i + 1) ≤ s ^ (k + 1) := by
    calc ∏ i, (q i + 1) ≤ ∏ _i : Fin (k + 1), s :=
          Finset.prod_le_prod' (fun i _ => hmod i)
      _ = s ^ (k + 1) := by simp
  exact hle.trans (hprod.trans (Nat.pow_le_pow_right hspos hN))

end Exercises
end Transducers
