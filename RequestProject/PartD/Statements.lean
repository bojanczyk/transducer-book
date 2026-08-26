/-
Part D: Polyregular functions
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Part D and the statements of its
theorems and lemmas.  Theorem `thm:polyregular-functions-are-continuous` is proved; the five
remaining results (`thm:for-transducers-are-polyregular`, `lemma:prenex-normal-form`,
`lem:for-closed-under-composition`, `thm:pebble-are-continuous` and `thm:pebble-are-for`) are
statements only, with their proofs left as `sorry`.

Not formalised here: Lemma `lem:reachability-pebble-automaton`, Claim
`claim:reachability-basic-run`, Lemma `lem:children-of-configuration-in-pebble-run` and Claims
`claim:from-configuration-to-child-configuration-graph`,
`claim:from-child-configuration-graph-to-children`, which are internal steps of the proofs of
Theorems `thm:pebble-are-continuous` and `thm:pebble-are-for`. They speak about the string
representation of configurations and configuration graphs of pebble transducers, an auxiliary
encoding used only inside those proofs. -/
import RequestProject.PartC.MSO
import RequestProject.PartD.MarkedSquare
import RequestProject.PartD.ForPrenexTop

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

/-! ## For-transducers

The syntax and the semantics of the for-transducers -- `Transducers.ForTest`,
`Transducers.ForProg`, `Transducers.ForTest.Holds`, `Transducers.forLoopRun`,
`Transducers.ForProg.exec`, `Transducers.ForProg.eval`, `Transducers.ForProg.LoopFree`,
`Transducers.ForProg.nestLoops`, `Transducers.ForProg.OutputsAtMostOne`, Definition
`def:prenex-normal-form-for-transducers` (`Transducers.ForProg.PrenexForm`) and
`Transducers.IsForTransducer` -- are defined, unchanged, in
`RequestProject/PartD/ForDef.lean`, so that the constructions proving Lemma
`lemma:prenex-normal-form` can be developed before the statements below. -/

/-! ### Equivalence with polyregular functions -/

/-- **Theorem `thm:for-transducers-are-polyregular`.**  A string-to-string function is polyregular
if and only if it is computed by a for-transducer. -/
theorem polyregular_iff_forTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f := by
  sorry

/-- **Lemma `lemma:prenex-normal-form`.**  Every for-transducer is equivalent to one in prenex
form. -/
theorem forTransducer_prenex {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w :=
  forTransducer_prenex_aux P

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
