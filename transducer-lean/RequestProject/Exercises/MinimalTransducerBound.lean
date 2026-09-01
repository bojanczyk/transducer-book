/-
The lower bound on the number of states in Exercise `exer:non-minimal-automaton`
of the chapter on machine independent characterisations (`myhill-nerode.tex`) of
*Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.MinimalTransducer

/-!
# How many states an unambiguous transducer for `evenParity` needs

`RequestProject/Exercises/MinimalTransducer.lean` gives two non-isomorphic three-state
unambiguous transducers for `evenParity`, `endOut` and `startOut`.  What is missing there is the
lower bound: that no smaller unambiguous transducer computes `evenParity`.  This file supplies
it, and in doing so it corrects the statement of the exercise.

The point is the following discrepancy between the book's picture of a transducer and the model
of this formalisation.  In `def:nfa-with-output` as formalised here (`Transducers.NFAO`) a
transition is labelled by an *arbitrary* input string and an arbitrary output string.  With a
transition that reads two letters at once, two states are enough for `evenParity`:

* `Transducers.Exercises.wideStart` emits the parity bit first (guessing the parity, with an
  empty-input transition for even and a one-letter transition for odd) and then checks the guess
  with a self-loop that reads `aa`;
* `Transducers.Exercises.wideEnd` does the same in the other order.

Both are unambiguous and compute `evenParity`, so `MinimalUnambiguousSize evenParity 3` is
*false*: this is `Transducers.Exercises.not_minimalUnambiguousSize_evenParity_three`.  It is what
the hypothesis `EvenParityNeedsThreeStates` of the previous version of the exercise asserted, and
it cannot be discharged, because it does not hold.  Two states is the true minimum in this model
(`Transducers.Exercises.minimalUnambiguousSize_evenParity_two`), and `wideStart` and `wideEnd`
are two non-isomorphic unambiguous transducers of that minimal size, so the exercise itself is
still true as it stands, and is proved outright in
`Transducers.Exercises.non_minimal_automaton_wide`.

The book clearly has in mind transducers that read at most one letter per transition — this is
what the picture of `endOut` and `startOut` shows — and for those the answer of the exercise is
the expected one: three states are necessary
(`Transducers.Exercises.minimalLetterwiseUnambiguousSize_evenParity_three`), and `endOut` and
`startOut` are two non-isomorphic unambiguous transducers of that minimal size
(`Transducers.Exercises.non_minimal_automaton`).

The lower bound argument, for a transducer `M` computing `evenParity`, is:

* no state is both initial and final, since the empty run would then be accepting and would
  output nothing, while `evenParity ε = 1`;
* hence the run over `ε`, whose output is the bit `1`, goes from an initial state `i` to a
  distinct final state `f`, and if there are at most two states then `Q = {i, f}`, the initial
  states are exactly `{i}` and the final ones exactly `{f}`;
* so the run over `a` also goes from `i` to `f`, and there are runs `i → f` reading `ε` and
  writing `1`, and reading `a` and writing `0`;
* no transition leaves `f`: composing the `ε`-run with it and, if it comes back to `i`, with the
  `a`-run, gives an accepting run whose output is either too long or begins with the wrong bit —
  except for a transition `f → f` reading and writing nothing, which is excluded by
  unambiguity, since it can be inserted into the run over `ε`;
* no transition goes from `i` to `i`, for the same reasons;
* so every accepting run consists of a single transition, which reads at most one letter, and
  there is no run over `aa`.
-/

namespace Transducers.Exercises

open Transducers

/-! ## Preliminaries -/

/-- The type of transitions of the two-state transducers below. -/
abbrev WideTrans := Bool × List Unit × List Bool × Bool

/-- Two lists over a one-letter alphabet with the same length are equal. -/
lemma unit_list_eq_of_length_eq {u v : List Unit} (h : u.length = v.length) : u = v := by
  rw [unit_list_eq_replicate u, unit_list_eq_replicate v, h]

lemma labAut_inputOf_append {A L Q : Type} (ts ts' : List (Q × List A × L × Q)) :
    LabAut.inputOf (ts ++ ts') = LabAut.inputOf ts ++ LabAut.inputOf ts' := by
  simp [LabAut.inputOf]

lemma nfao_outputOf_append {A B Q : Type} (ts ts' : List (Q × List A × List B × Q)) :
    NFAO.outputOf (ts ++ ts') = NFAO.outputOf ts ++ NFAO.outputOf ts' := by
  simp [NFAO.outputOf, LabAut.labelsOf]

lemma par_eq_true_of_even {n : ℕ} (h : n % 2 = 0) : par n = true := by simp [par, h]

lemma par_eq_false_of_odd {n : ℕ} (h : n % 2 = 1) : par n = false := by simp [par, h]

/-! ## Two states suffice when a transition may read two letters -/

/-- The first two-state transducer: the parity bit is produced at the start, and the loop that
reads two letters at a time checks the guess. -/
def wideStart : NFAO Unit Bool Bool where
  init := {false}
  final := {true}
  δ := {(false, [], [true], true), (false, [()], [false], true), (true, [(), ()], [], true)}
  δ_finite := Set.toFinite _

/-- The second two-state transducer: the same, with the parity bit produced at the end. -/
def wideEnd : NFAO Unit Bool Bool where
  init := {false}
  final := {true}
  δ := {(false, [(), ()], [], false), (false, [], [true], true), (false, [()], [false], true)}
  δ_finite := Set.toFinite _

/-- The transition that produces the parity bit `b`: it reads nothing if `b` is `true`, and one
letter if `b` is `false`.  Both transducers use it, `wideStart` at the start of the run and
`wideEnd` at the end. -/
def wideHead (b : Bool) : WideTrans := (false, (if b then [] else [()]), [b], true)

@[simp] lemma wideHead_true : wideHead true = (false, [], [true], true) := rfl

@[simp] lemma wideHead_false : wideHead false = (false, [()], [false], true) := rfl

/-! ### The transducer that guesses the parity first -/

/-- `k` iterations of the loop of `wideStart`, which reads `aa` and writes nothing. -/
def wideLoop : ℕ → List WideTrans
  | 0 => []
  | k + 1 => (true, [(), ()], [], true) :: wideLoop k

@[simp] lemma wideLoop_zero : wideLoop 0 = [] := rfl

@[simp] lemma wideLoop_succ (k : ℕ) :
    wideLoop (k + 1) = (true, [(), ()], [], true) :: wideLoop k := rfl

@[simp] lemma wideLoop_length (k : ℕ) : (wideLoop k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wideLoop_succ, List.length_cons, ih]

lemma wideLoop_input_length (k : ℕ) : (LabAut.inputOf (wideLoop k)).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [wideLoop_succ, LabAut.inputOf_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

@[simp] lemma wideLoop_output (k : ℕ) : NFAO.outputOf (wideLoop k) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wideLoop_succ, NFAO.outputOf_cons, ih]; rfl

lemma wideLoop_path (k : ℕ) : wideStart.Path true (wideLoop k) true := by
  induction k with
  | zero => exact LabAut.Path.nil _
  | succ k ih => exact LabAut.Path.cons (by simp [wideStart]) ih

/-- The accepting run of `wideStart` over an input of length `n`. -/
def widePath (n : ℕ) : List WideTrans := wideHead (par n) :: wideLoop (n / 2)

lemma widePath_eq (b : Bool) (k : ℕ) :
    widePath ((if b then 0 else 1) + 2 * k) = wideHead b :: wideLoop k := by
  cases b with
  | true =>
      have h1 : par (0 + 2 * k) = true := par_eq_true_of_even (by omega)
      have h2 : (0 + 2 * k) / 2 = k := by omega
      show wideHead (par (0 + 2 * k)) :: wideLoop ((0 + 2 * k) / 2) = _
      rw [h1, h2]
  | false =>
      have h1 : par (1 + 2 * k) = false := par_eq_false_of_odd (by omega)
      have h2 : (1 + 2 * k) / 2 = k := by omega
      show wideHead (par (1 + 2 * k)) :: wideLoop ((1 + 2 * k) / 2) = _
      rw [h1, h2]

lemma wideHead_mem_wideStart (b : Bool) : wideHead b ∈ wideStart.δ := by
  cases b <;> simp [wideStart]

lemma widePath_path (n : ℕ) : wideStart.Path false (widePath n) true := by
  have h : wideHead (par n) = (false, (wideHead (par n)).2.1, (wideHead (par n)).2.2.1, true) := by
    cases hb : par n <;> rfl
  rw [widePath]
  refine h ▸ LabAut.Path.cons (h ▸ wideHead_mem_wideStart (par n)) (wideLoop_path _)

lemma widePath_input_length (n : ℕ) : (LabAut.inputOf (widePath n)).length = n := by
  rw [widePath, LabAut.inputOf_cons, List.length_append, wideLoop_input_length]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [par_eq_true_of_even h]
    simp only [wideHead_true, List.length_nil]
    omega
  · rw [par_eq_false_of_odd h]
    simp only [wideHead_false, List.length_cons, List.length_nil]
    omega

@[simp] lemma widePath_output (n : ℕ) : NFAO.outputOf (widePath n) = [par n] := by
  rw [widePath, NFAO.outputOf_cons, wideLoop_output]
  cases hb : par n <;> simp [wideHead]

/-- The transitions of `wideStart`. -/
lemma wideStart_mem_delta {q0 q1 : Bool} {u : List Unit} {l : List Bool}
    (h : (q0, u, l, q1) ∈ wideStart.δ) :
    (q0 = false ∧ u = [] ∧ l = [true] ∧ q1 = true) ∨
      (q0 = false ∧ u = [()] ∧ l = [false] ∧ q1 = true) ∨
      (q0 = true ∧ u = [(), ()] ∧ l = [] ∧ q1 = true) := by
  have h' : (q0, u, l, q1) = (false, [], [true], true) ∨
      (q0, u, l, q1) = (false, [()], [false], true) ∨
      (q0, u, l, q1) = (true, [(), ()], [], true) := by
    simpa [wideStart] using h
  rcases h' with h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

/-- Every run of `wideStart` from the second state to itself is a power of the loop. -/
lemma wideStart_loop_eq : ∀ (ts : List WideTrans), wideStart.Path true ts true →
    ts = wideLoop ts.length := by
  intro ts
  induction ts with
  | nil => intro _; rfl
  | cons t ts ih =>
      obtain ⟨q0, u, l, q1⟩ := t
      intro h
      cases h with
      | cons ht hrest =>
          rcases wideStart_mem_delta ht with ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩ | ⟨-, rfl, rfl, rfl⟩
          · exact absurd h0 (by simp)
          · exact absurd h0 (by simp)
          · rw [List.length_cons, wideLoop_succ]
            exact congrArg _ (ih hrest)

lemma wideStart_path_eq : ∀ (ts : List WideTrans), wideStart.Path false ts true →
    ts = widePath (LabAut.inputOf ts).length := by
  intro ts h
  cases ts with
  | nil => cases h
  | cons t ts =>
      obtain ⟨q0, u, l, q1⟩ := t
      cases h with
      | cons ht hrest =>
          have hts : ts = wideLoop ts.length := wideStart_loop_eq ts (by
            rcases wideStart_mem_delta ht with ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨h0, -, -, -⟩
            · exact hrest
            · exact hrest
            · exact absurd h0 (by simp))
          have hlen : (LabAut.inputOf ts).length = 2 * ts.length := by
            conv_lhs => rw [hts]
            rw [wideLoop_input_length]
          rcases wideStart_mem_delta ht with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ |
            ⟨h0, -, -, -⟩
          · have hin : (LabAut.inputOf ((false, ([] : List Unit), [true], true) :: ts)).length
                = (if true then 0 else 1) + 2 * ts.length := by
              rw [LabAut.inputOf_cons, List.length_append, hlen]
              simp
            rw [hin, widePath_eq true ts.length, wideHead_true]
            exact congrArg _ hts
          · have hin : (LabAut.inputOf ((false, [()], [false], true) :: ts)).length
                = (if false then 0 else 1) + 2 * ts.length := by
              rw [LabAut.inputOf_cons, List.length_append, hlen]
              simp
            rw [hin, widePath_eq false ts.length, wideHead_false]
            exact congrArg _ hts
          · exact absurd h0 (by simp)

lemma wideStart_accepting_iff (ts : List WideTrans) :
    wideStart.Accepting ts ↔ wideStart.Path false ts true := by
  constructor
  · rintro ⟨q, hq, p, hp, hpath⟩
    have hq' : q = false := hq
    have hp' : p = true := hp
    subst hq'; subst hp'; exact hpath
  · intro h
    exact ⟨false, rfl, true, rfl, h⟩

lemma wideStart_rel (w : List Unit) (v : List Bool) : wideStart.rel w v ↔ v = evenParity w := by
  constructor
  · rintro ⟨ts, hacc, rfl, rfl⟩
    rw [wideStart_accepting_iff] at hacc
    conv_lhs => rw [wideStart_path_eq ts hacc]
    rw [widePath_output, evenParity_eq_par]
  · rintro rfl
    refine ⟨widePath w.length, (wideStart_accepting_iff _).2 (widePath_path w.length), ?_, ?_⟩
    · exact unit_list_eq_of_length_eq (by rw [widePath_input_length])
    · rw [widePath_output, evenParity_eq_par]

lemma wideStart_unambiguous : wideStart.Unambiguous := by
  intro w
  refine ⟨widePath w.length,
    ⟨(wideStart_accepting_iff _).2 (widePath_path w.length), ?_⟩, ?_⟩
  · exact unit_list_eq_of_length_eq (by rw [widePath_input_length])
  · rintro ts ⟨hacc, rfl⟩
    rw [wideStart_accepting_iff] at hacc
    exact wideStart_path_eq ts hacc

/-! ### The transducer that produces the parity bit at the end -/

/-- `k` iterations of the loop of `wideEnd`, which reads `aa` and writes nothing. -/
def wideLoopE : ℕ → List WideTrans
  | 0 => []
  | k + 1 => (false, [(), ()], [], false) :: wideLoopE k

@[simp] lemma wideLoopE_zero : wideLoopE 0 = [] := rfl

@[simp] lemma wideLoopE_succ (k : ℕ) :
    wideLoopE (k + 1) = (false, [(), ()], [], false) :: wideLoopE k := rfl

lemma wideLoopE_input_length (k : ℕ) : (LabAut.inputOf (wideLoopE k)).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [wideLoopE_succ, LabAut.inputOf_cons, List.length_append, ih]
      simp only [List.length_cons, List.length_nil]
      omega

@[simp] lemma wideLoopE_output (k : ℕ) : NFAO.outputOf (wideLoopE k) = [] := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wideLoopE_succ, NFAO.outputOf_cons, ih]; rfl

lemma wideLoopE_path (k : ℕ) : wideEnd.Path false (wideLoopE k) false := by
  induction k with
  | zero => exact LabAut.Path.nil _
  | succ k ih => exact LabAut.Path.cons (by simp [wideEnd]) ih

/-- The accepting run of `wideEnd` over an input of length `n`. -/
def widePathE (n : ℕ) : List WideTrans := wideLoopE (n / 2) ++ [wideHead (par n)]

lemma wideHead_mem_wideEnd (b : Bool) : wideHead b ∈ wideEnd.δ := by
  cases b <;> simp [wideEnd]

lemma widePathE_path (n : ℕ) : wideEnd.Path false (widePathE n) true := by
  have h : wideHead (par n) = (false, (wideHead (par n)).2.1, (wideHead (par n)).2.2.1, true) := by
    cases hb : par n <;> rfl
  refine (wideLoopE_path _).append ?_
  exact h ▸ LabAut.Path.cons (h ▸ wideHead_mem_wideEnd (par n)) (LabAut.Path.nil _)

lemma widePathE_input_length (n : ℕ) : (LabAut.inputOf (widePathE n)).length = n := by
  rw [widePathE, labAut_inputOf_append, List.length_append, wideLoopE_input_length,
    LabAut.inputOf_cons, LabAut.inputOf_nil, List.append_nil]
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [par_eq_true_of_even h]
    simp only [wideHead_true, List.length_nil]
    omega
  · rw [par_eq_false_of_odd h]
    simp only [wideHead_false, List.length_cons, List.length_nil]
    omega

@[simp] lemma widePathE_output (n : ℕ) : NFAO.outputOf (widePathE n) = [par n] := by
  rw [widePathE, nfao_outputOf_append, wideLoopE_output, NFAO.outputOf_cons, NFAO.outputOf_nil]
  cases hb : par n <;> simp [wideHead]

/-- The transitions of `wideEnd`. -/
lemma wideEnd_mem_delta {q0 q1 : Bool} {u : List Unit} {l : List Bool}
    (h : (q0, u, l, q1) ∈ wideEnd.δ) :
    (q0 = false ∧ u = [(), ()] ∧ l = [] ∧ q1 = false) ∨
      (q0 = false ∧ u = [] ∧ l = [true] ∧ q1 = true) ∨
      (q0 = false ∧ u = [()] ∧ l = [false] ∧ q1 = true) := by
  have h' : (q0, u, l, q1) = (false, [(), ()], [], false) ∨
      (q0, u, l, q1) = (false, [], [true], true) ∨
      (q0, u, l, q1) = (false, [()], [false], true) := by
    simpa [wideEnd] using h
  rcases h' with h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  · exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

/-- The final state of `wideEnd` has no outgoing transitions. -/
lemma wideEnd_path_from_true {ts : List WideTrans} (h : wideEnd.Path true ts true) : ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      obtain ⟨q0, u, l, q1⟩ := t
      cases h with
      | cons ht _ =>
          rcases wideEnd_mem_delta ht with ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩ <;>
            exact absurd h0 (by simp)

lemma widePathE_zero : widePathE 0 = [(false, [], [true], true)] := by
  simp [widePathE, par]

lemma widePathE_one : widePathE 1 = [(false, [()], [false], true)] := by
  simp [widePathE, par]

lemma widePathE_add_two (n : ℕ) :
    widePathE (n + 2) = (false, [(), ()], [], false) :: widePathE n := by
  have h1 : (n + 2) / 2 = n / 2 + 1 := by omega
  have h2 : par (n + 2) = par n := by simp [par, Nat.add_mod_right]
  rw [widePathE, widePathE, h1, h2, wideLoopE_succ, List.cons_append]

lemma wideEnd_path_eq : ∀ (ts : List WideTrans), wideEnd.Path false ts true →
    ts = widePathE (LabAut.inputOf ts).length := by
  intro ts
  induction ts with
  | nil => intro h; cases h
  | cons t ts ih =>
      obtain ⟨q0, u, l, q1⟩ := t
      intro h
      cases h with
      | cons ht hrest =>
          rcases wideEnd_mem_delta ht with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ |
            ⟨-, rfl, rfl, rfl⟩
          · have hlen : (LabAut.inputOf ((false, [(), ()], ([] : List Bool), false) :: ts)).length
                = (LabAut.inputOf ts).length + 2 := by
              rw [LabAut.inputOf_cons, List.length_append]
              simp only [List.length_cons, List.length_nil]
              omega
            rw [hlen, widePathE_add_two]
            exact congrArg _ (ih hrest)
          · rw [wideEnd_path_from_true hrest]
            simpa [LabAut.inputOf] using widePathE_zero.symm
          · rw [wideEnd_path_from_true hrest]
            simpa [LabAut.inputOf] using widePathE_one.symm

lemma wideEnd_accepting_iff (ts : List WideTrans) :
    wideEnd.Accepting ts ↔ wideEnd.Path false ts true := by
  constructor
  · rintro ⟨q, hq, p, hp, hpath⟩
    have hq' : q = false := hq
    have hp' : p = true := hp
    subst hq'; subst hp'; exact hpath
  · intro h
    exact ⟨false, rfl, true, rfl, h⟩

lemma wideEnd_rel (w : List Unit) (v : List Bool) : wideEnd.rel w v ↔ v = evenParity w := by
  constructor
  · rintro ⟨ts, hacc, rfl, rfl⟩
    rw [wideEnd_accepting_iff] at hacc
    conv_lhs => rw [wideEnd_path_eq ts hacc]
    rw [widePathE_output, evenParity_eq_par]
  · rintro rfl
    refine ⟨widePathE w.length, (wideEnd_accepting_iff _).2 (widePathE_path w.length), ?_, ?_⟩
    · exact unit_list_eq_of_length_eq (by rw [widePathE_input_length])
    · rw [widePathE_output, evenParity_eq_par]

lemma wideEnd_unambiguous : wideEnd.Unambiguous := by
  intro w
  refine ⟨widePathE w.length,
    ⟨(wideEnd_accepting_iff _).2 (widePathE_path w.length), ?_⟩, ?_⟩
  · exact unit_list_eq_of_length_eq (by rw [widePathE_input_length])
  · rintro ts ⟨hacc, rfl⟩
    rw [wideEnd_accepting_iff] at hacc
    exact wideEnd_path_eq ts hacc

/-- The two two-state transducers are not isomorphic: in `wideStart` the loop that reads two
letters is at the final state, in `wideEnd` it is at the initial state. -/
lemma wideStart_not_iso_wideEnd : ¬ NFAOIso wideStart wideEnd := by
  rintro ⟨e, hinit, -, hδ⟩
  have h0 : e false = false := (hinit false).1 rfl
  have h1 : e true = true := by
    have hne : e true ≠ e false := fun h => by simpa using e.injective h
    rw [h0] at hne
    revert hne
    cases e true <;> simp
  have h2 : (e true, [(), ()], ([] : List Bool), e true) ∈ wideEnd.δ :=
    (hδ true [(), ()] [] true).1 (by simp [wideStart])
  rw [h1] at h2
  simp only [wideEnd, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    Bool.true_eq_false, false_and, and_false, or_self] at h2

/-! ## Two states are necessary -/

section Lower

variable {Q : Type} {M : NFAO Unit Bool Q}

@[simp] lemma evenParity_nil : evenParity [] = [true] := rfl

@[simp] lemma evenParity_one : evenParity [()] = [false] := rfl

lemma evenParity_length (w : List Unit) : (evenParity w).length = 1 := rfl

/-- If a transducer computes `evenParity` then no state is both initial and final: otherwise the
empty run would be accepting and would produce no output. -/
lemma no_init_final (hrel : ∀ w v, M.rel w v ↔ v = evenParity w) {q : Q}
    (hi : q ∈ M.init) (hf : q ∈ M.final) : False := by
  have h : M.rel [] [] := (M.rel_iff_relFrom [] []).2 ⟨q, hi, q, hf, M.relFrom_nil q⟩
  have h' := (hrel [] []).1 h
  simp at h'

/-- The output of a run of a transducer computing `evenParity` from an initial to a final
state. -/
lemma output_eq_evenParity (hrel : ∀ w v, M.rel w v ↔ v = evenParity w) {i f : Q}
    (hi : i ∈ M.init) (hf : f ∈ M.final) {w : List Unit} {v : List Bool}
    (h : M.relFrom i w v f) : v = evenParity w :=
  (hrel w v).1 ((M.rel_iff_relFrom w v).2 ⟨i, hi, f, hf, h⟩)

end Lower

/-- **Two states are necessary** for an unambiguous transducer computing `evenParity`.  The
argument does not use unambiguity: the initial state of an accepting run over the empty input is
not final. -/
theorem minimalUnambiguousSize_evenParity_two : MinimalUnambiguousSize evenParity 2 := by
  intro Q hfin M _ hrel
  haveI := hfin
  obtain ⟨i, hi, f, hf, -⟩ := (M.rel_iff_relFrom [] (evenParity [])).1 ((hrel [] _).2 rfl)
  have hif : i ≠ f := by
    rintro rfl
    exact no_init_final hrel hi hf
  haveI : Nontrivial Q := ⟨i, f, hif⟩
  have h1 : 1 < Nat.card Q := Finite.one_lt_card_iff_nontrivial.mpr this
  omega

/-- Three states are *not* necessary: `wideStart` is an unambiguous transducer with two states
that computes `evenParity`.  This refutes the hypothesis `EvenParityNeedsThreeStates` of the
earlier version of Exercise `exer:non-minimal-automaton`; see the module documentation. -/
theorem not_minimalUnambiguousSize_evenParity_three :
    ¬ MinimalUnambiguousSize evenParity 3 := by
  intro h
  have h2 := h Bool inferInstance wideStart wideStart_unambiguous wideStart_rel
  rw [Nat.card_eq_fintype_card] at h2
  simp at h2

/-! ## Transducers that read at most one letter per transition -/

/-- A transducer is *letterwise* if each of its transitions reads at most one input letter.
This is the shape of transducer that the book draws, and the shape of `endOut` and
`startOut`. -/
def Letterwise {A B Q : Type} (M : NFAO A B Q) : Prop := ∀ t ∈ M.δ, t.2.1.length ≤ 1

/-- `n` states are necessary among letterwise transducers: every unambiguous letterwise
transducer computing `f` has at least `n` states. -/
def MinimalLetterwiseUnambiguousSize {A B : Type} (f : List A → List B) (n : ℕ) : Prop :=
  ∀ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), Letterwise M → M.Unambiguous →
    (∀ w v, M.rel w v ↔ v = f w) → n ≤ Nat.card Q

lemma endOut_letterwise : Letterwise endOut := by
  rintro ⟨q0, u, l, q1⟩ ht
  rcases endOut_mem_delta ht with ⟨b, -, rfl, -, -⟩ | ⟨b, -, rfl, -, -⟩ <;> simp

lemma startOut_letterwise : Letterwise startOut := by
  rintro ⟨q0, u, l, q1⟩ ht
  rcases startOut_mem_delta ht with ⟨g, -, rfl, -, -⟩ | ⟨c, -, rfl, -, -⟩ <;> simp

/-- A list over a one-letter alphabet of length at most one is empty or a single letter. -/
lemma unit_list_le_one : ∀ {u : List Unit}, u.length ≤ 1 → u = [] ∨ u = [()]
  | [], _ => Or.inl rfl
  | [()], _ => Or.inr rfl
  | _ :: _ :: _, h => by simp at h

/-- **Three states are necessary** for an unambiguous letterwise transducer computing
`evenParity`.  This is the lower bound of Exercise `exer:non-minimal-automaton`. -/
theorem minimalLetterwiseUnambiguousSize_evenParity_three :
    MinimalLetterwiseUnambiguousSize evenParity 3 := by
  intro Q hfin M hlet hun hrel
  haveI := hfin
  by_contra hcard
  push_neg at hcard
  -- the accepting run over the empty input
  obtain ⟨i, hi, f, hf, r0, hp0, hin0, hout0⟩ :
      ∃ i ∈ M.init, ∃ f ∈ M.final, ∃ ts, M.Path i ts f ∧ LabAut.inputOf ts = [] ∧
        NFAO.outputOf ts = [true] := by
    obtain ⟨q, hq, p, hp, ts, hts, h1, h2⟩ :=
      (M.rel_iff_relFrom [] (evenParity [])).1 ((hrel [] _).2 rfl)
    exact ⟨q, hq, p, hp, ts, hts, h1, by rw [h2]; rfl⟩
  have hif : i ≠ f := by
    rintro rfl
    exact no_init_final hrel hi hf
  -- there are exactly the two states `i` and `f`
  have hQ : ∀ q : Q, q = i ∨ q = f := by
    intro q
    by_contra hq
    push_neg at hq
    obtain ⟨hq1, hq2⟩ := hq
    have h3 : ({i, f, q} : Set Q).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hif, Ne.symm hq1]) (Set.toFinite _),
        Set.ncard_insert_of_notMem (by simp [Ne.symm hq2]) (Set.toFinite _),
        Set.ncard_singleton]
    have h4 : ({i, f, q} : Set Q).ncard ≤ Nat.card Q := by
      rw [← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
    omega
  have hinit : ∀ q ∈ M.init, q = i := by
    intro q hq
    rcases hQ q with h | h
    · exact h
    · exact absurd (no_init_final hrel (h ▸ hq) hf) id
  have hfinal : ∀ p ∈ M.final, p = f := by
    intro p hp
    rcases hQ p with h | h
    · exact absurd (no_init_final hrel hi (h ▸ hp)) id
    · exact h
  -- the two runs that have to be accommodated
  have hE : M.relFrom i [] [true] f := ⟨r0, hp0, hin0, hout0⟩
  have hD : M.relFrom i [()] [false] f := by
    obtain ⟨q, hq, p, hp, hpath⟩ :=
      (M.rel_iff_relFrom [()] (evenParity [()])).1 ((hrel [()] _).2 rfl)
    rw [hinit q hq, hfinal p hp] at hpath
    exact hpath
  -- no transition leaves the final state
  have hFout : ∀ (u : List Unit) (x : List Bool) (p : Q), (f, u, x, p) ∉ M.δ := by
    intro u x p ht
    have hu : u = [] ∨ u = [()] := unit_list_le_one (hlet _ ht)
    have hstep : M.relFrom f u x p := NFAO.relFrom_single ht
    rcases hQ p with hp | hp
    · rw [hp] at hstep
      have h2 : M.relFrom i (([] ++ u) ++ [()]) (([true] ++ x) ++ [false]) f :=
        NFAO.relFrom_trans (NFAO.relFrom_trans hE hstep) hD
      have h3 := output_eq_evenParity hrel hi hf h2
      have h4 := congrArg List.length h3
      rw [evenParity_length] at h4
      simp at h4
    · rw [hp] at hstep
      have h1 : M.relFrom i ([] ++ u) ([true] ++ x) f := NFAO.relFrom_trans hE hstep
      rcases hu with rfl | rfl
      · have h3 := output_eq_evenParity hrel hi hf h1
        have hx : x = [] := by simpa using h3
        subst hx
        obtain ⟨t, -, huniq⟩ := hun []
        have e1 := huniq r0 ⟨⟨i, hi, f, hf, hp0⟩, hin0⟩
        have e2 := huniq (r0 ++ [(f, [], [], f)])
          ⟨⟨i, hi, f, hf, hp0.append (LabAut.Path.cons (hp ▸ ht) (LabAut.Path.nil f))⟩, by
            rw [labAut_inputOf_append, hin0]
            simp [LabAut.inputOf]⟩
        rw [← e1] at e2
        have e3 := congrArg List.length e2
        simp at e3
      · have h3 := output_eq_evenParity hrel hi hf h1
        simp at h3
  -- no transition goes from the initial state to itself
  have hIloop : ∀ (u : List Unit) (x : List Bool), (i, u, x, i) ∉ M.δ := by
    intro u x ht
    have hu : u = [] ∨ u = [()] := unit_list_le_one (hlet _ ht)
    have h1 : M.relFrom i (u ++ []) (x ++ [true]) f :=
      NFAO.relFrom_trans (NFAO.relFrom_single ht) hE
    rcases hu with rfl | rfl
    · have h3 := output_eq_evenParity hrel hi hf h1
      have hx : x = [] := by
        have h4 := congrArg List.length h3
        rw [evenParity_length] at h4
        simp at h4
        exact h4
      subst hx
      obtain ⟨t, -, huniq⟩ := hun []
      have e1 := huniq r0 ⟨⟨i, hi, f, hf, hp0⟩, hin0⟩
      have e2 := huniq ((i, [], [], i) :: r0)
        ⟨⟨i, hi, f, hf, LabAut.Path.cons ht hp0⟩, by
          rw [LabAut.inputOf_cons, hin0]
          simp⟩
      rw [← e1] at e2
      have e3 := congrArg List.length e2
      simp at e3
    · have h3 := output_eq_evenParity hrel hi hf h1
      have hx : x = [] := by
        have h4 := congrArg List.length h3
        rw [evenParity_length] at h4
        simp at h4
        exact h4
      subst hx
      simp at h3
  -- so no accepting run reads two letters
  obtain ⟨q, hq, p, hp, ts, hts, hin, -⟩ :=
    (M.rel_iff_relFrom [(), ()] (evenParity [(), ()])).1 ((hrel [(), ()] _).2 rfl)
  rw [hinit q hq, hfinal p hp] at hts
  cases ts with
  | nil => simp at hin
  | cons t ts =>
      obtain ⟨q0, u, x, q1⟩ := t
      cases hts with
      | cons hmem hrest =>
          have hq1 : q1 = f := by
            rcases hQ q1 with h | h
            · exact absurd (h ▸ hmem) (hIloop u x)
            · exact h
          rw [hq1] at hrest
          cases hrest with
          | nil =>
              have hu : u.length ≤ 1 := hlet _ hmem
              have hu2 : u = [(), ()] := by simpa using hin
              rw [hu2] at hu
              simp at hu
          | cons hmem2 _ => exact absurd hmem2 (hFout _ _ _)

/-! ## The exercise -/

/-- **Exercise `exer:non-minimal-automaton`.**  There is a rational function with two
non-isomorphic unambiguous transducers of minimal size: the function `evenParity`, which maps
`aⁿ` to the bit saying whether `n` is even, is computed by the two three-state unambiguous
transducers `endOut` and `startOut`, which are not isomorphic, and three states is the least
possible size for a transducer that reads at most one letter per transition.

This is the statement of the exercise for the transducers that the book draws, in which a
transition reads at most one letter (`Letterwise`).  In the model of `def:nfa-with-output` as
formalised here a transition may read an arbitrary string, and then two states already suffice;
see `non_minimal_automaton_wide` for the exercise in that model. -/
theorem non_minimal_automaton :
    ∃ (f : List Unit → List Bool) (M₁ M₂ : NFAO Unit Bool (Option Bool)),
      IsRationalFun f ∧ Nat.card (Option Bool) = 3 ∧
      MinimalLetterwiseUnambiguousSize f 3 ∧
      Letterwise M₁ ∧ M₁.Unambiguous ∧ (∀ w v, M₁.rel w v ↔ v = f w) ∧
      Letterwise M₂ ∧ M₂.Unambiguous ∧ (∀ w v, M₂.rel w v ↔ v = f w) ∧
      ¬ NFAOIso M₁ M₂ :=
  ⟨evenParity, endOut, startOut,
    ⟨Option Bool, inferInstance, endOut, fun w v => (endOut_rel w v).symm⟩,
    card_option_bool, minimalLetterwiseUnambiguousSize_evenParity_three,
    endOut_letterwise, endOut_unambiguous, endOut_rel,
    startOut_letterwise, startOut_unambiguous, startOut_rel,
    endOut_not_iso_startOut⟩

/-- **Exercise `exer:non-minimal-automaton`, in the model of the formalisation.**  If a
transition may read an arbitrary string, as in `def:nfa-with-output` as formalised here, then the
minimal size of an unambiguous transducer for `evenParity` is two, and the two two-state
transducers `wideStart` and `wideEnd` — which again produce the parity bit at the beginning and
at the end of the input — are unambiguous, compute `evenParity`, and are not isomorphic. -/
theorem non_minimal_automaton_wide :
    ∃ (f : List Unit → List Bool) (M₁ M₂ : NFAO Unit Bool Bool),
      IsRationalFun f ∧ Nat.card Bool = 2 ∧
      MinimalUnambiguousSize f 2 ∧
      M₁.Unambiguous ∧ (∀ w v, M₁.rel w v ↔ v = f w) ∧
      M₂.Unambiguous ∧ (∀ w v, M₂.rel w v ↔ v = f w) ∧
      ¬ NFAOIso M₁ M₂ :=
  ⟨evenParity, wideStart, wideEnd,
    ⟨Bool, inferInstance, wideStart, fun w v => (wideStart_rel w v).symm⟩,
    by simp [Nat.card_eq_fintype_card], minimalUnambiguousSize_evenParity_two,
    wideStart_unambiguous, wideStart_rel, wideEnd_unambiguous, wideEnd_rel,
    wideStart_not_iso_wideEnd⟩

end Transducers.Exercises
