/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): the tree of the configurations that reach the answer *true*.

The searching automaton of `RequestProject/Exercises/TwoDFASipserDef.lean` explores that tree.  The
facts about it that the exploration needs are collected here: a configuration reaching the answer
*true* does not lie on a cycle, so the configurations strictly below a given one form a set that
strictly decreases when one passes to a child, which is what makes the depth-first search
terminate.
-/
import RequestProject.Exercises.TwoDFASipserRun

namespace Transducers
namespace Exercises

open Transducers

variable {A R : Type}

section Tree

variable (N : TwoDFA A R) (w : List A)

/-- The configuration `c` of `N` reaches the answer *true*. -/
def RT (c : ℕ × R) : Prop := ∃ k, (N.next w)^[k] (Sum.inl c) = Sum.inr true

/-- The configuration `c` reaches the configuration `c'` in a positive number of steps. -/
def CRs (c c' : ℕ × R) : Prop := ∃ k, 0 < k ∧ (N.next w)^[k] (Sum.inl c) = Sum.inl c'

variable {N w}

/-! ### The one-step transition, read off the transition function -/

lemma next_inl_eq (p : ℕ) (r : R) :
    N.next w (Sum.inl (p, r)) =
      match cstep N w p r with
      | Sum.inl b => Sum.inr b
      | Sum.inr (r', true) => if p < w.length then Sum.inl (p + 1, r') else Sum.inr false
      | Sum.inr (r', false) => if 0 < p then Sum.inl (p - 1, r') else Sum.inr false := rfl

lemma next_eq_answer {p : ℕ} {r : R} {b : Bool} (h : cstep N w p r = Sum.inl b) :
    N.next w (Sum.inl (p, r)) = Sum.inr b := by
  rw [next_inl_eq, h]

lemma next_eq_inl_right {p : ℕ} {r r' : R} (h : cstep N w p r = Sum.inr (r', true))
    (hp : p < w.length) : N.next w (Sum.inl (p, r)) = Sum.inl (p + 1, r') := by
  rw [next_inl_eq, h]
  exact if_pos hp

lemma next_eq_inl_left {p : ℕ} {r r' : R} (h : cstep N w p r = Sum.inr (r', false))
    (hp : 0 < p) : N.next w (Sum.inl (p, r)) = Sum.inl (p - 1, r') := by
  rw [next_inl_eq, h]
  exact if_pos hp

lemma next_eq_inr_of_right {p : ℕ} {r r' : R} (h : cstep N w p r = Sum.inr (r', true))
    (hp : ¬ p < w.length) : N.next w (Sum.inl (p, r)) = Sum.inr false := by
  rw [next_inl_eq, h]
  exact if_neg hp

lemma next_eq_inr_of_left {p : ℕ} {r r' : R} (h : cstep N w p r = Sum.inr (r', false))
    (hp : ¬ 0 < p) : N.next w (Sum.inl (p, r)) = Sum.inr false := by
  rw [next_inl_eq, h]
  exact if_neg hp

/-- A configuration is reached in one step either from the left or from the right. -/
lemma next_eq_inl_cases {p p' : ℕ} {r r' : R} (h : N.next w (Sum.inl (p, r)) = Sum.inl (p', r')) :
    (cstep N w p r = Sum.inr (r', true) ∧ p < w.length ∧ p' = p + 1) ∨
      (cstep N w p r = Sum.inr (r', false) ∧ 0 < p ∧ p' = p - 1) := by
  rcases hc : cstep N w p r with b | ⟨s, d⟩
  · rw [next_eq_answer hc] at h; exact absurd h (by simp)
  · cases d with
    | true =>
        by_cases hp : p < w.length
        · rw [next_eq_inl_right hc hp] at h
          simp only [Sum.inl.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          subst h2
          exact Or.inl ⟨rfl, hp, rfl⟩
        · rw [next_eq_inr_of_right hc hp] at h; exact absurd h (by simp)
    | false =>
        by_cases hp : 0 < p
        · rw [next_eq_inl_left hc hp] at h
          simp only [Sum.inl.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          subst h2
          exact Or.inr ⟨rfl, hp, rfl⟩
        · rw [next_eq_inr_of_left hc hp] at h; exact absurd h (by simp)

/-- The last configuration of an accepting run answers *true* at once. -/
lemma cstep_eq_inl_true {p : ℕ} {r : R} (h : N.next w (Sum.inl (p, r)) = Sum.inr true) :
    cstep N w p r = Sum.inl true := by
  rcases hc : cstep N w p r with b | ⟨s, d⟩
  · rw [next_eq_answer hc] at h
    rw [Sum.inr_injective h]
  · cases d with
    | true =>
        by_cases hp : p < w.length
        · rw [next_eq_inl_right hc hp] at h; exact absurd h (by simp)
        · rw [next_eq_inr_of_right hc hp] at h; exact absurd h (by simp)
    | false =>
        by_cases hp : 0 < p
        · rw [next_eq_inl_left hc hp] at h; exact absurd h (by simp)
        · rw [next_eq_inr_of_left hc hp] at h; exact absurd h (by simp)

/-- The head never leaves the input. -/
lemma pos_le_of_next {p p' : ℕ} {r r' : R} (hp : p ≤ w.length)
    (h : N.next w (Sum.inl (p, r)) = Sum.inl (p', r')) : p' ≤ w.length := by
  rcases next_eq_inl_cases h with ⟨-, h1, h2⟩ | ⟨-, -, h2⟩ <;> omega

lemma pos_le_of_iterate : ∀ (k p : ℕ) (r : R) (p' : ℕ) (r' : R), p ≤ w.length →
    (N.next w)^[k] (Sum.inl (p, r)) = Sum.inl (p', r') → p' ≤ w.length := by
  intro k
  induction k with
  | zero => intro p r p' r' hp h; cases Sum.inl_injective h; exact hp
  | succ k ih =>
      intro p r p' r' hp h
      rw [Function.iterate_succ_apply] at h
      rcases hn : N.next w (Sum.inl (p, r)) with ⟨p₁, r₁⟩ | b
      · rw [hn] at h; exact ih p₁ r₁ p' r' (pos_le_of_next hp hn) h
      · rw [hn, TwoDFA.iterate_next_inr] at h; exact absurd h (by simp)

/-! ### Reaching the answer *true* -/

lemma RT.step {c c' : ℕ × R} (h : N.next w (Sum.inl c) = Sum.inl c') (hc : RT N w c) :
    RT N w c' := by
  obtain ⟨k, hk⟩ := hc
  cases k with
  | zero => exact absurd hk (by simp)
  | succ k => exact ⟨k, by rw [Function.iterate_succ_apply, h] at hk; exact hk⟩

lemma RT.of_step {c c' : ℕ × R} (h : N.next w (Sum.inl c) = Sum.inl c') (hc : RT N w c') :
    RT N w c := by
  obtain ⟨k, hk⟩ := hc
  exact ⟨k + 1, by rw [Function.iterate_succ_apply, h]; exact hk⟩

lemma RT.of_answer {c : ℕ × R} (h : N.next w (Sum.inl c) = Sum.inr true) : RT N w c :=
  ⟨1, by simpa using h⟩

/-! ### Reachability in a positive number of steps -/

lemma CRs.of_step {c c' : ℕ × R} (h : N.next w (Sum.inl c) = Sum.inl c') : CRs N w c c' :=
  ⟨1, Nat.one_pos, by simpa using h⟩

lemma CRs.trans {c d e : ℕ × R} (h1 : CRs N w c d) (h2 : CRs N w d e) : CRs N w c e := by
  obtain ⟨k1, hk1, h1⟩ := h1
  obtain ⟨k2, hk2, h2⟩ := h2
  exact ⟨k2 + k1, by omega, by rw [Function.iterate_add_apply, h1]; exact h2⟩

/-- Iterating a cycle stays on it. -/
private lemma iterate_mul_of_cycle {c : ℕ × R} {k : ℕ}
    (h : (N.next w)^[k] (Sum.inl c) = Sum.inl c) :
    ∀ j, (N.next w)^[j * k] (Sum.inl c) = Sum.inl c := by
  intro j
  induction j with
  | zero => simp
  | succ j ih => rw [show (j + 1) * k = j * k + k by ring, Function.iterate_add_apply, h, ih]

/-- A configuration that reaches the answer *true* does not lie on a cycle. -/
lemma not_CRs_self {c : ℕ × R} (h : RT N w c) : ¬ CRs N w c c := by
  rintro ⟨k, hk, hc⟩
  obtain ⟨m, hm⟩ := h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm; exact absurd hm (by simp)
    · exact h0
  have h1 : (N.next w)^[m * k] (Sum.inl c) = Sum.inl c := iterate_mul_of_cycle hc m
  have h2 : m ≤ m * k := Nat.le_mul_of_pos_right m hk
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h2
  rw [hd, show m + d = d + m by omega, Function.iterate_add_apply, hm,
    TwoDFA.iterate_next_inr] at h1
  exact absurd h1 (by simp)

/-! ### The configurations below a given one -/

variable (N w)

/-- The configurations of `N` that lie strictly below `c` in the configuration graph. -/
def Below (c : ℕ × R) : Set (ℕ × R) := {d | d.1 ≤ w.length ∧ CRs N w d c}

variable {N w}

lemma finite_below [Finite R] (c : ℕ × R) : (Below N w c).Finite := by
  have hsub : Below N w c ⊆ (Set.Iic w.length) ×ˢ (Set.univ : Set R) := by
    rintro d ⟨hd, -⟩
    exact ⟨hd, Set.mem_univ _⟩
  exact Set.Finite.subset ((Set.finite_Iic _).prod Set.finite_univ) hsub

/-- Passing to a child strictly decreases the set of configurations below. -/
lemma ncard_below_lt [Finite R] {c d : ℕ × R} (hd : d.1 ≤ w.length)
    (hstep : N.next w (Sum.inl d) = Sum.inl c) (hRT : RT N w c) :
    (Below N w d).ncard < (Below N w c).ncard := by
  have hsub : Below N w d ⊆ Below N w c := by
    rintro e ⟨he, hce⟩
    exact ⟨he, hce.trans (CRs.of_step hstep)⟩
  have hmem : d ∈ Below N w c := ⟨hd, CRs.of_step hstep⟩
  have hnot : d ∉ Below N w d := fun h => not_CRs_self (RT.of_step hstep hRT) h.2
  exact Set.ncard_lt_ncard ⟨hsub, fun hcon => hnot (hcon hmem)⟩ (finite_below c)

end Tree

end Exercises
end Transducers
