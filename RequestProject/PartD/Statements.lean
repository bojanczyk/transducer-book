/-
Part D: Polyregular functions
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Part D and the statements of its
theorems and lemmas.  Proofs are left as `sorry`.

Not formalised here: Lemma `lem:reachability-pebble-automaton`, Claim
`claim:reachability-basic-run`, Lemma `lem:children-of-configuration-in-pebble-run` and Claims
`claim:from-configuration-to-child-configuration-graph`,
`claim:from-child-configuration-graph-to-children`, which are internal steps of the proofs of
Theorems `thm:pebble-are-continuous` and `thm:pebble-are-for`. They speak about the string
representation of configurations and configuration graphs of pebble transducers, an auxiliary
encoding used only inside those proofs. -/
import RequestProject.PartC.MSO
import RequestProject.PartD.MarkedSquare

namespace Transducers

/-! ## Polyregular functions (Definition `def:polyregular-functions`) -/

/-! **Example 33 (Marked squaring)** (`markedSquare`) is defined in
`RequestProject/PartD/MarkedSquare.lean`, together with the proof that it is continuous, which is
the main step in the proof of Theorem `thm:polyregular-functions-are-continuous` below. -/

/-- The family of prime polyregular functions: regular functions and marked
squaring. -/
def PolyregularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRegularFun f ∨
  (∃ (A₀ : Type) (e : A ≃ A₀) (e' : B ≃ A₀ ⊕ A₀),
      ∀ w, f w = (markedSquare A₀ (w.map e)).map e'.symm)

/-- **Definition `def:polyregular-functions` (Polyregular functions).**  A string-to-string function
is polyregular if it is a finite composition of regular functions and marked
squaring. -/
def IsPolyregular {A B : Type} (f : List A → List B) : Prop :=
  CompClosure PolyregularFam A B f

/-- **Theorem `thm:polyregular-functions-are-continuous`.**  Polyregular functions are continuous. -/
theorem polyregular_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPolyregular f) : Continuous f := by
  induction hf with
  | base h =>
      rcases h with hreg | ⟨A₀, e, e', hfe⟩
      · exact continuous_of_isRegularFun hreg
      · exact Continuous.congr
          ((continuous_map (e'.symm : A₀ ⊕ A₀ → _)).comp
            ((continuous_markedSquare A₀).comp (continuous_map (e : _ → A₀))))
          (fun w => (hfe w).symm)
  | id A => exact continuous_id
  | comp _ _ ihf ihg => exact ihg.comp ihf

/-! ## For-transducers -/

/-- Tests of a for-transducer: Boolean variables, equality and order tests on
position variables, and label tests. -/
inductive ForTest (A : Type) : Type
  /-- The value of a Boolean variable. -/
  | boolVar : ℕ → ForTest A
  /-- The equality test `x == y` on position variables. -/
  | eqPos : ℕ → ℕ → ForTest A
  /-- The order test `x <= y` on position variables. -/
  | lePos : ℕ → ℕ → ForTest A
  /-- The label test `w[x] == a`. -/
  | label : ℕ → A → ForTest A
  /-- Negation. -/
  | not : ForTest A → ForTest A
  /-- Conjunction. -/
  | and : ForTest A → ForTest A → ForTest A
  /-- Disjunction. -/
  | or : ForTest A → ForTest A → ForTest A

/-- Programs of a for-transducer.  Position variables are read-only and are
bound by the loops; Boolean variables are initialised to `false`. -/
inductive ForProg (A B : Type) : Type
  /-- The empty program. -/
  | skip : ForProg A B
  /-- `output('b')`: append the letter `b` to the output. -/
  | output : B → ForProg A B
  /-- `X = true` / `X = false`. -/
  | assign : ℕ → Bool → ForProg A B
  /-- Sequential composition `I ; J`. -/
  | seq : ForProg A B → ForProg A B → ForProg A B
  /-- A conditional. -/
  | ite : ForTest A → ForProg A B → ForProg A B → ForProg A B
  /-- `for x in positions(w)` (`true`) or `for x in positions_reverse(w)`
  (`false`). -/
  | loop : Bool → ℕ → ForProg A B → ForProg A B

namespace ForTest

variable {A : Type}

/-- The truth value of a test, given the input string and the valuations of the
position and Boolean variables. -/
def Holds (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) : ForTest A → Prop
  | boolVar i => bv i = true
  | eqPos i j => pos i = pos j
  | lePos i j => pos i ≤ pos j
  | label i a => w[pos i]? = some a
  | not t => ¬ Holds w pos bv t
  | and t s => Holds w pos bv t ∧ Holds w pos bv s
  | or t s => Holds w pos bv t ∨ Holds w pos bv s

end ForTest

/-- Running the body of a loop over a list of positions, threading the Boolean
valuation and concatenating the outputs. -/
def forLoopRun {B : Type} (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B) :
    List ℕ → (ℕ → Bool) → (ℕ → Bool) × List B
  | [], bv => (bv, [])
  | p :: ps, bv =>
      let r := body bv p
      let r' := forLoopRun body ps r.1
      (r'.1, r.2 ++ r'.2)

namespace ForProg

variable {A B : Type}

open scoped Classical in
/-- The semantics of a for-transducer program: the resulting Boolean valuation
and the produced output string. -/
noncomputable def exec (w : List A) :
    ForProg A B → (ℕ → ℕ) → (ℕ → Bool) → (ℕ → Bool) × List B
  | skip, _, bv => (bv, [])
  | output b, _, bv => (bv, [b])
  | assign i v, _, bv => (Function.update bv i v, [])
  | seq P Q, pos, bv =>
      let r := exec w P pos bv
      let r' := exec w Q pos r.1
      (r'.1, r.2 ++ r'.2)
  | ite t P Q, pos, bv =>
      if ForTest.Holds w pos bv t then exec w P pos bv else exec w Q pos bv
  | loop dir x P, pos, bv =>
      forLoopRun (fun bv' p => exec w P (Function.update pos x p) bv')
        (if dir then List.range w.length else (List.range w.length).reverse) bv

/-- The string-to-string function computed by a for-transducer. -/
noncomputable def eval (P : ForProg A B) (w : List A) : List B :=
  (exec w P (fun _ => 0) (fun _ => false)).2

/-- A program that contains no loops. -/
def LoopFree : ForProg A B → Prop
  | skip => True
  | output _ => True
  | assign _ _ => True
  | seq P Q => LoopFree P ∧ LoopFree Q
  | ite _ P Q => LoopFree P ∧ LoopFree Q
  | loop _ _ _ => False

/-- Nested loops `for x₁ in τ₁: ⋯ for x_k in τ_k: body`. -/
def nestLoops : List (Bool × ℕ) → ForProg A B → ForProg A B
  | [], body => body
  | (d, x) :: rest, body => ForProg.loop d x (nestLoops rest body)

/-- A program produces at most one output letter per execution. -/
def OutputsAtMostOne (P : ForProg A B) : Prop :=
  ∀ (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool), ((exec w P pos bv).2).length ≤ 1

/-- **Definition `def:prenex-normal-form-for-transducers` (Prenex form).**  A block of nested loops
whose body is loop-free and produces at most one output letter per iteration, followed by a
loop-free epilogue. -/
def PrenexForm (P : ForProg A B) : Prop :=
  ∃ (ls : List (Bool × ℕ)) (body epilogue : ForProg A B),
    LoopFree body ∧ LoopFree epilogue ∧ OutputsAtMostOne body ∧
    P = ForProg.seq (nestLoops ls body) epilogue

end ForProg

/-- A function computed by a for-transducer. -/
def IsForTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ P : ForProg A B, ∀ w, P.eval w = f w

/-! ### Equivalence with polyregular functions -/

/-- **Theorem `thm:for-transducers-are-polyregular`.**  A string-to-string function is polyregular
if and only if it is computed by a for-transducer. -/
theorem polyregular_iff_forTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f := by
  sorry

/-- **Lemma `lemma:prenex-normal-form`.**  Every for-transducer is equivalent to one in prenex
form. -/
theorem forTransducer_prenex {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w := by
  sorry

/-- **Lemma `lem:for-closed-under-composition`.**  String-to-string functions computed by
for-transducers are closed under composition. -/
theorem forTransducer_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f) := by
  sorry

/-! ## Pebble transducers -/

/-- The information available to a pebble transducer: for every pebble on the
stack (listed from the bottom), the two adjacent input letters and the set of
pebbles that are in the same place. -/
abbrev PebbleView (A : Type) := List ((Option A × Option A) × List Bool)

/-- The view of the input string from a stack of pebbles, which are gaps of the
input string (listed from the bottom of the stack). -/
def viewOf {A : Type} (w : List A) (st : List ℕ) : PebbleView A :=
  st.map (fun p => ((if p = 0 then none else w[p - 1]?, w[p]?),
    st.map (fun q => decide (q = p))))

/-- The actions of a pebble transducer. -/
inductive PebbleAction (B : Type) : Type
  /-- Output a letter. -/
  | out : B → PebbleAction B
  /-- Move the head one position to the right (`true`) or left (`false`). -/
  | move : Bool → PebbleAction B
  /-- Push the first input position onto the pebble stack. -/
  | push : PebbleAction B
  /-- Pop the topmost pebble. -/
  | pop : PebbleAction B
  /-- Terminate. -/
  | terminate : PebbleAction B

/-- A `k`-pebble transducer: a deterministic machine with a stack of at most `k`
pebbles pointing to gaps of the input string.  (Only the finitely many views
that arise from stacks of height at most `k` are relevant for the transition
function.) -/
structure Pebble (A B Q : Type) (k : ℕ) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Q → PebbleView A → Q × PebbleAction B

/-- A configuration of a pebble transducer: the state and the stack of pebbles
(listed from the bottom), or the halting vertex. -/
inductive PebbleCfg (Q : Type) : Type
  | conf : Q → List ℕ → PebbleCfg Q
  | halt : PebbleCfg Q

namespace Pebble

variable {A B Q : Type} {k : ℕ}

/-- One step of the computation: the produced output and the next
configuration, if any.  The step is undefined if the head moves out of the input
string, if the stack bound is exceeded, or if a pebble is popped from an empty
stack. -/
def stepCfg (M : Pebble A B Q k) (w : List A) : PebbleCfg Q → Option (List B × PebbleCfg Q)
  | PebbleCfg.halt => none
  | PebbleCfg.conf q st =>
      let r := M.step q (viewOf w st)
      match r.2 with
      | PebbleAction.out b => some ([b], PebbleCfg.conf r.1 st)
      | PebbleAction.terminate => some ([], PebbleCfg.halt)
      | PebbleAction.push =>
          if st.length < k then some ([], PebbleCfg.conf r.1 (st ++ [0])) else none
      | PebbleAction.pop =>
          if st = [] then none else some ([], PebbleCfg.conf r.1 st.dropLast)
      | PebbleAction.move dir =>
          match st.getLast? with
          | none => none
          | some p =>
              if dir then
                (if p < w.length then some ([], PebbleCfg.conf r.1 (st.dropLast ++ [p + 1]))
                 else none)
              else
                (if 0 < p then some ([], PebbleCfg.conf r.1 (st.dropLast ++ [p - 1]))
                 else none)

/-- Reachability in the configuration graph, recording the produced output. -/
inductive Reaches (M : Pebble A B Q k) (w : List A) :
    PebbleCfg Q → List B → PebbleCfg Q → Prop
  | refl (c : PebbleCfg Q) : Reaches M w c [] c
  | step {c c' c'' : PebbleCfg Q} {o o' : List B} :
      M.stepCfg w c = some (o, c') → Reaches M w c' o' c'' → Reaches M w c (o ++ o') c''

/-- The transducer produces the output `v` on the input `w`. -/
def Computes (M : Pebble A B Q k) (w : List A) (v : List B) : Prop :=
  M.Reaches w (PebbleCfg.conf M.init []) v PebbleCfg.halt

end Pebble

/-- A (total) function computed by a pebble transducer. -/
def IsPebbleTransducer {A B : Type} (f : List A → List B) : Prop :=
  ∃ (k : ℕ) (Q : Type) (_ : Finite Q) (M : Pebble A B Q k), ∀ w, M.Computes w (f w)

/-! ### Continuity -/

/-- **Theorem `thm:pebble-are-continuous`.**  Pebble transducers compute continuous functions. -/
theorem pebble_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPebbleTransducer f) : Continuous f := by
  sorry

/-! ### Equivalence with for-transducers -/

/-- **Theorem `thm:pebble-are-for`.**  Pebble transducers and for-transducers compute the same
string-to-string functions. -/
theorem pebble_iff_forTransducer {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsPebbleTransducer f ↔ IsForTransducer f := by
  sorry

end Transducers
