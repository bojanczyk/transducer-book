/-
Exercise `exer:non-minimal-automaton` of the chapter on machine independent
characterisations (`myhill-nerode.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.PartB.LabAut
import RequestProject.Exercises.MyhillNerode

/-!
# Minimal unambiguous transducers are not unique

Exercise `exer:non-minimal-automaton` asks for a rational function with two
non-isomorphic unambiguous transducers of minimal size, where the size is the
number of states.

The function of the book is the same parity function as in
`exer:non-minimal-bimachine`, namely `Transducers.Exercises.evenParity`, which
maps `aⁿ` to the single bit saying whether `n` is even.  The two transducers
differ in *where* the output letter is produced.

* `Transducers.Exercises.endOut` produces the bit at the end: two states track
  the parity of the number of letters read so far, and two transitions with
  empty input — one from each parity state — enter a common final state and
  produce the corresponding bit.
* `Transducers.Exercises.startOut` produces the bit at the beginning: two
  transitions with empty input leave the initial state, guessing the parity of
  the whole input and producing the corresponding bit, and lead to two states
  that check the guess.

Both have three states, both are unambiguous, both compute `evenParity`, and
they are not isomorphic: in the first one the two transitions with empty input
enter the same state, in the second one they leave the same state.  Formally we
use the invariant that in `endOut` the initial state has an outgoing transition
that reads a letter, while in `startOut` it does not.

The remaining half of the solution — that three states are *necessary* — is the
case analysis that the book itself only sketches ("a short case analysis on the
two remaining states"); it is taken here as the explicit hypothesis
`Transducers.Exercises.EvenParityNeedsThreeStates`, which is the only
assumption of the final statement `non_minimal_automaton`.
-/

namespace Transducers.Exercises

open Transducers

/-! ## Parity -/

/-- The parity bit of a natural number: `true` for even. -/
def par (n : ℕ) : Bool := decide (n % 2 = 0)

@[simp] lemma par_zero : par 0 = true := rfl

lemma par_succ (n : ℕ) : par (n + 1) = !par n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [par, Nat.add_mod, h]

lemma evenParity_eq_par (w : List Unit) : evenParity w = [par w.length] := rfl

/-- Every list over a one-letter alphabet is a block of that letter. -/
lemma unit_list_eq_replicate (w : List Unit) : w = List.replicate w.length () := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a; rw [List.length_cons, List.replicate_succ, ← ih]

/-- The type of transitions of the two transducers below. -/
abbrev ParTrans := Option Bool × List Unit × List Bool × Option Bool

/-! ## The transducer that produces the output at the end -/

/-- The first transducer: the states `some b` track the parity of the number of letters read so
far, and the final state `none` is entered by a transition with empty input which produces the
parity bit. -/
def endOut : NFAO Unit Bool (Option Bool) where
  init := {some true}
  final := {none}
  δ := {(some true, [()], [], some false), (some false, [()], [], some true),
        (some true, [], [true], none), (some false, [], [false], none)}
  δ_finite := Set.toFinite _

/-- The accepting run of `endOut` from the parity state `some b` over `n` letters. -/
def endPath : Bool → ℕ → List ParTrans
  | b, 0 => [(some b, [], [b], none)]
  | b, n + 1 => (some b, [()], [], some !b) :: endPath (!b) n

@[simp] lemma endPath_zero (b : Bool) : endPath b 0 = [(some b, [], [b], none)] := rfl

@[simp] lemma endPath_succ (b : Bool) (n : ℕ) :
    endPath b (n + 1) = (some b, [()], [], some !b) :: endPath (!b) n := rfl

lemma beq_par_succ (c : Bool) (n : ℕ) : (c == par (n + 1)) = ((!c) == par n) := by
  rw [par_succ]
  generalize par n = d
  cases c <;> cases d <;> rfl

lemma endPath_input (b : Bool) (n : ℕ) :
    LabAut.inputOf (endPath b n) = List.replicate n () := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => rw [endPath_succ, LabAut.inputOf_cons, ih, List.replicate_succ]; rfl

lemma endPath_length_input (b : Bool) (n : ℕ) : (LabAut.inputOf (endPath b n)).length = n := by
  rw [endPath_input, List.length_replicate]

lemma endPath_output (b : Bool) (n : ℕ) :
    NFAO.outputOf (endPath b n) = [b == par n] := by
  induction n generalizing b with
  | zero => cases b <;> rfl
  | succ n ih =>
      rw [endPath_succ, NFAO.outputOf_cons, ih, beq_par_succ]
      rfl

lemma endPath_path (b : Bool) (n : ℕ) : endOut.Path (some b) (endPath b n) none := by
  induction n generalizing b with
  | zero => cases b <;> exact LabAut.Path.cons (by simp [endOut]) (LabAut.Path.nil none)
  | succ n ih => cases b <;> exact LabAut.Path.cons (by simp [endOut]) (ih _)

/-- The transitions of `endOut`: either a letter is read and the parity state is flipped, or the
final state is entered with empty input and the parity bit is produced. -/
lemma endOut_mem_delta {q0 q1 : Option Bool} {u : List Unit} {l : List Bool}
    (h : (q0, u, l, q1) ∈ endOut.δ) :
    (∃ b : Bool, q0 = some b ∧ u = [()] ∧ l = [] ∧ q1 = some (!b)) ∨
      (∃ b : Bool, q0 = some b ∧ u = [] ∧ l = [b] ∧ q1 = none) := by
  have h' : (q0, u, l, q1) = (some true, [()], [], some false) ∨
      (q0, u, l, q1) = (some false, [()], [], some true) ∨
      (q0, u, l, q1) = (some true, [], [true], none) ∨
      (q0, u, l, q1) = (some false, [], [false], none) := by
    simpa [endOut] using h
  rcases h' with h' | h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  · exact Or.inl ⟨true, rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨false, rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨true, rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨false, rfl, rfl, rfl, rfl⟩

/-- The final state of `endOut` has no outgoing transitions. -/
lemma endOut_path_from_final {ts : List ParTrans} (h : endOut.Path none ts none) : ts = [] := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      obtain ⟨q0, u, l, q1⟩ := t
      cases h with
      | cons ht _ =>
          rcases endOut_mem_delta ht with ⟨b, hb, -, -, -⟩ | ⟨b, hb, -, -, -⟩ <;>
            exact absurd hb (by simp)

private lemma endPath_cons_letter (b : Bool) (ts : List ParTrans)
    (h : ts = endPath (!b) (LabAut.inputOf ts).length) :
    (some b, [()], ([] : List Bool), some (!b)) :: ts
      = endPath b (LabAut.inputOf ((some b, [()], ([] : List Bool), some (!b)) :: ts)).length := by
  have hlen : (LabAut.inputOf ((some b, [()], ([] : List Bool), some (!b)) :: ts)).length
      = (LabAut.inputOf ts).length + 1 := by
    rw [LabAut.inputOf_cons]; simp
  rw [hlen, endPath_succ]
  exact congrArg _ h

/-- Every accepting run of `endOut` from a parity state is one of the runs `endPath`. -/
lemma endOut_path_eq : ∀ (ts : List ParTrans) (b : Bool), endOut.Path (some b) ts none →
    ts = endPath b (LabAut.inputOf ts).length := by
  intro ts
  induction ts with
  | nil => intro b h; cases h
  | cons t ts ih =>
      obtain ⟨q0, u, l, q1⟩ := t
      intro b h
      cases h with
      | cons ht hrest =>
          rcases endOut_mem_delta ht with ⟨b', hb, rfl, rfl, rfl⟩ | ⟨b', hb, rfl, rfl, rfl⟩
          · injection hb with hb
            subst hb
            exact endPath_cons_letter _ ts (ih _ hrest)
          · injection hb with hb
            subst hb
            rw [endOut_path_from_final hrest]
            rfl

lemma endOut_accepting_iff (ts : List ParTrans) :
    endOut.Accepting ts ↔ endOut.Path (some true) ts none := by
  constructor
  · rintro ⟨q, hq, p, hp, hpath⟩
    have hq' : q = some true := hq
    have hp' : p = none := hp
    subst hq'; subst hp'; exact hpath
  · intro h
    exact ⟨some true, rfl, none, rfl, h⟩

lemma endOut_rel (w : List Unit) (v : List Bool) : endOut.rel w v ↔ v = evenParity w := by
  constructor
  · rintro ⟨ts, hacc, rfl, rfl⟩
    rw [endOut_accepting_iff] at hacc
    have hout : NFAO.outputOf ts = [par (LabAut.inputOf ts).length] := by
      conv_lhs => rw [endOut_path_eq ts true hacc]
      rw [endPath_output]
      simp
    rw [hout, evenParity_eq_par]
  · rintro rfl
    refine ⟨endPath true w.length, (endOut_accepting_iff _).2 (endPath_path true w.length), ?_, ?_⟩
    · rw [endPath_input]; exact (unit_list_eq_replicate w).symm
    · rw [endPath_output, evenParity_eq_par]; simp

lemma endOut_unambiguous : endOut.Unambiguous := by
  intro w
  refine ⟨endPath true w.length,
    ⟨(endOut_accepting_iff _).2 (endPath_path true w.length), ?_⟩, ?_⟩
  · rw [endPath_input]; exact (unit_list_eq_replicate w).symm
  · rintro ts ⟨hacc, rfl⟩
    rw [endOut_accepting_iff] at hacc
    exact endOut_path_eq ts true hacc

/-! ## The transducer that produces the output at the beginning -/

/-- The second transducer: from the initial state `none` two transitions with empty input guess
the parity of the whole input and produce the corresponding bit; the states `some b` then check
the guess, and only `some true` is final. -/
def startOut : NFAO Unit Bool (Option Bool) where
  init := {none}
  final := {some true}
  δ := {(none, [], [true], some true), (none, [], [false], some false),
        (some true, [()], [], some false), (some false, [()], [], some true)}
  δ_finite := Set.toFinite _

/-- The run of `startOut` that reads `n` letters from the checking state `some c`. -/
def letPath : Bool → ℕ → List ParTrans
  | _, 0 => []
  | c, n + 1 => (some c, [()], [], some !c) :: letPath (!c) n

@[simp] lemma letPath_zero (c : Bool) : letPath c 0 = [] := rfl

@[simp] lemma letPath_succ (c : Bool) (n : ℕ) :
    letPath c (n + 1) = (some c, [()], [], some !c) :: letPath (!c) n := rfl

lemma letPath_input (c : Bool) (n : ℕ) :
    LabAut.inputOf (letPath c n) = List.replicate n () := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [letPath_succ, LabAut.inputOf_cons, ih, List.replicate_succ]; rfl

lemma letPath_output (c : Bool) (n : ℕ) : NFAO.outputOf (letPath c n) = [] := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [letPath_succ, NFAO.outputOf_cons, ih]; rfl

lemma letPath_length (c : Bool) (n : ℕ) : (letPath c n).length = n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => rw [letPath_succ, List.length_cons, ih]

/-- The transitions of `startOut`: either the initial state is left with empty input, producing a
guessed bit, or a letter is read and the checking state is flipped. -/
lemma startOut_mem_delta {q0 q1 : Option Bool} {u : List Unit} {l : List Bool}
    (h : (q0, u, l, q1) ∈ startOut.δ) :
    (∃ g : Bool, q0 = none ∧ u = [] ∧ l = [g] ∧ q1 = some g) ∨
      (∃ c : Bool, q0 = some c ∧ u = [()] ∧ l = [] ∧ q1 = some (!c)) := by
  have h' : (q0, u, l, q1) = (none, [], [true], some true) ∨
      (q0, u, l, q1) = (none, [], [false], some false) ∨
      (q0, u, l, q1) = (some true, [()], [], some false) ∨
      (q0, u, l, q1) = (some false, [()], [], some true) := by
    simpa [startOut] using h
  rcases h' with h' | h' | h' | h' <;> simp only [Prod.mk.injEq] at h' <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
  · exact Or.inl ⟨true, rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨false, rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨true, rfl, rfl, rfl, rfl⟩
  · exact Or.inr ⟨false, rfl, rfl, rfl, rfl⟩

lemma letPath_path (c : Bool) (n : ℕ) :
    startOut.Path (some c) (letPath c n) (some (c == par n)) := by
  induction n generalizing c with
  | zero => cases c <;> exact LabAut.Path.nil _
  | succ n ih =>
      rw [letPath_succ, beq_par_succ]
      exact LabAut.Path.cons (by cases c <;> simp [startOut]) (ih (!c))

private lemma letPath_cons_letter (c : Bool) (ts : List ParTrans)
    (h : ts = letPath (!c) ts.length) :
    (some c, [()], ([] : List Bool), some (!c)) :: ts
      = letPath c ((some c, [()], ([] : List Bool), some (!c)) :: ts).length := by
  rw [List.length_cons, letPath_succ]
  exact congrArg _ h

/-- Every run of `startOut` between two checking states is one of the runs `letPath`, and its
length determines the state that it reaches. -/
lemma startOut_letter_path_eq : ∀ (ts : List ParTrans) (c d : Bool),
    startOut.Path (some c) ts (some d) → ts = letPath c ts.length ∧ d = (c == par ts.length) := by
  intro ts
  induction ts with
  | nil =>
      intro c d h
      cases h with
      | nil => exact ⟨rfl, by cases c <;> rfl⟩
  | cons t ts ih =>
      obtain ⟨q0, u, l, q1⟩ := t
      intro c d h
      cases h with
      | cons ht hrest =>
          rcases startOut_mem_delta ht with ⟨g, hg, -, -, -⟩ | ⟨c', hc, rfl, rfl, rfl⟩
          · exact absurd hg (by simp)
          · injection hc with hc
            subst hc
            obtain ⟨h1, h2⟩ := ih _ _ hrest
            refine ⟨letPath_cons_letter _ ts h1, ?_⟩
            rw [List.length_cons, beq_par_succ]
            exact h2

/-- The accepting run of `startOut` over an input of length `n`. -/
def startPath (n : ℕ) : List ParTrans :=
  (none, [], [par n], some (par n)) :: letPath (par n) n

lemma startPath_input (n : ℕ) : LabAut.inputOf (startPath n) = List.replicate n () := by
  rw [startPath, LabAut.inputOf_cons, letPath_input]; rfl

lemma startPath_output (n : ℕ) : NFAO.outputOf (startPath n) = [par n] := by
  rw [startPath, NFAO.outputOf_cons, letPath_output]; rfl

lemma startPath_path (n : ℕ) : startOut.Path none (startPath n) (some true) := by
  have h := letPath_path (par n) n
  rw [beq_self_eq_true] at h
  exact LabAut.Path.cons (by generalize par n = c; cases c <;> simp [startOut]) h

lemma startOut_accepting_iff (ts : List ParTrans) :
    startOut.Accepting ts ↔ startOut.Path none ts (some true) := by
  constructor
  · rintro ⟨q, hq, p, hp, hpath⟩
    have hq' : q = none := hq
    have hp' : p = some true := hp
    subst hq'; subst hp'; exact hpath
  · intro h
    exact ⟨none, rfl, some true, rfl, h⟩

private lemma startPath_cons (g : Bool) (ts : List ParTrans)
    (h1 : ts = letPath g ts.length) (hg : g = par ts.length) :
    (none, ([] : List Unit), [g], some g) :: ts
      = startPath (LabAut.inputOf ((none, ([] : List Unit), [g], some g) :: ts)).length := by
  have hin : LabAut.inputOf ts = List.replicate ts.length () := by
    conv_lhs => rw [h1]
    rw [letPath_input]
  have hlen : (LabAut.inputOf ((none, ([] : List Unit), [g], some g) :: ts)).length
      = ts.length := by
    rw [LabAut.inputOf_cons, hin]
    simp
  rw [hlen, startPath, ← hg]
  exact congrArg _ h1

lemma startOut_path_eq : ∀ (ts : List ParTrans), startOut.Path none ts (some true) →
    ts = startPath (LabAut.inputOf ts).length := by
  intro ts h
  cases ts with
  | nil => cases h
  | cons t ts =>
      obtain ⟨q0, u, l, q1⟩ := t
      cases h with
      | cons ht hrest =>
          rcases startOut_mem_delta ht with ⟨g, -, rfl, rfl, rfl⟩ | ⟨c, hc, -, -, -⟩
          · obtain ⟨h1, h2⟩ := startOut_letter_path_eq ts g true hrest
            exact startPath_cons g ts h1 (beq_iff_eq.1 h2.symm)
          · exact absurd hc (by simp)

lemma startOut_rel (w : List Unit) (v : List Bool) : startOut.rel w v ↔ v = evenParity w := by
  constructor
  · rintro ⟨ts, hacc, rfl, rfl⟩
    rw [startOut_accepting_iff] at hacc
    have hout : NFAO.outputOf ts = [par (LabAut.inputOf ts).length] := by
      conv_lhs => rw [startOut_path_eq ts hacc]
      rw [startPath_output]
    rw [hout, evenParity_eq_par]
  · rintro rfl
    refine ⟨startPath w.length, (startOut_accepting_iff _).2 (startPath_path w.length), ?_, ?_⟩
    · rw [startPath_input]; exact (unit_list_eq_replicate w).symm
    · rw [startPath_output, evenParity_eq_par]

lemma startOut_unambiguous : startOut.Unambiguous := by
  intro w
  refine ⟨startPath w.length,
    ⟨(startOut_accepting_iff _).2 (startPath_path w.length), ?_⟩, ?_⟩
  · rw [startPath_input]; exact (unit_list_eq_replicate w).symm
  · rintro ts ⟨hacc, rfl⟩
    rw [startOut_accepting_iff] at hacc
    exact startOut_path_eq ts hacc

/-! ## The two transducers are not isomorphic -/

/-- Isomorphism of automata with output: a bijection of the state sets that matches the initial
states, the final states and the transitions. -/
def NFAOIso {A B Q₁ Q₂ : Type} (M₁ : NFAO A B Q₁) (M₂ : NFAO A B Q₂) : Prop :=
  ∃ e : Q₁ ≃ Q₂, (∀ q, q ∈ M₁.init ↔ e q ∈ M₂.init) ∧ (∀ q, q ∈ M₁.final ↔ e q ∈ M₂.final) ∧
    (∀ q u x p, (q, u, x, p) ∈ M₁.δ ↔ (e q, u, x, e p) ∈ M₂.δ)

lemma endOut_not_iso_startOut : ¬ NFAOIso endOut startOut := by
  rintro ⟨e, hinit, -, hδ⟩
  have h1 : e (some true) = none := by
    have : e (some true) ∈ startOut.init := (hinit (some true)).1 rfl
    exact this
  have h2 : (e (some true), [()], ([] : List Bool), e (some false)) ∈ startOut.δ :=
    (hδ (some true) [()] [] (some false)).1 (by simp [endOut])
  rw [h1] at h2
  simp only [startOut, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq,
    reduceCtorEq, false_and, and_false, or_self] at h2

/-! ## The exercise -/

/-- `n` states are necessary: every unambiguous transducer computing `f` has at least `n`
states. -/
def MinimalUnambiguousSize {A B : Type} (f : List A → List B) (n : ℕ) : Prop :=
  ∀ (Q : Type) (_ : Finite Q) (M : NFAO A B Q), M.Unambiguous → (∀ w v, M.rel w v ↔ v = f w) →
    n ≤ Nat.card Q

/-- **Assumed.**  Three states are necessary for an unambiguous transducer computing
`evenParity`.

This is the last paragraph of the solution of `exer:non-minimal-automaton`, and it is the one
step of the solution that the book does not carry out: it says that the runs over the inputs
`a⁰` and `a¹` are disjoint and that "a short case analysis on the two remaining states, which
have to track the parity, shows that these two runs cannot be accommodated".  The case analysis
ranges over all unambiguous transducers with at most two states — an unbounded family, since the
transitions may read and write arbitrary strings — and is left here as an explicit hypothesis
rather than reconstructed.  Everything else in the exercise is proved outright. -/
def EvenParityNeedsThreeStates : Prop := MinimalUnambiguousSize evenParity 3

lemma card_option_bool : Nat.card (Option Bool) = 3 := by
  simp [Nat.card_eq_fintype_card]

/-- **Exercise `exer:non-minimal-automaton`.**  There is a rational function with two
non-isomorphic unambiguous transducers of minimal size: the function `evenParity`, which maps
`aⁿ` to the bit saying whether `n` is even, is computed by the two three-state unambiguous
transducers `endOut` and `startOut`, which are not isomorphic; and three states is the least
possible size, which is the assumption `EvenParityNeedsThreeStates`. -/
theorem non_minimal_automaton (h : EvenParityNeedsThreeStates) :
    ∃ (f : List Unit → List Bool) (M₁ M₂ : NFAO Unit Bool (Option Bool)),
      IsRationalFun f ∧ Nat.card (Option Bool) = 3 ∧
      MinimalUnambiguousSize f 3 ∧
      M₁.Unambiguous ∧ (∀ w v, M₁.rel w v ↔ v = f w) ∧
      M₂.Unambiguous ∧ (∀ w v, M₂.rel w v ↔ v = f w) ∧
      ¬ NFAOIso M₁ M₂ :=
  ⟨evenParity, endOut, startOut,
    ⟨Option Bool, inferInstance, endOut, fun w v => (endOut_rel w v).symm⟩,
    card_option_bool, h, endOut_unambiguous, endOut_rel, startOut_unambiguous, startOut_rel,
    endOut_not_iso_startOut⟩

end Transducers.Exercises
