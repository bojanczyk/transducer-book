/-
Part D: Polyregular functions
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Part D and the statements of its
theorems and lemmas.  All of them are proved: Theorem
`thm:polyregular-functions-are-continuous`, Theorem `thm:for-transducers-are-polyregular`, Lemma
`lemma:prenex-normal-form`, Lemma `lem:for-closed-under-composition`, Theorem
`thm:pebble-are-continuous` and Theorem `thm:pebble-are-for`.

Not formalised here: Lemma `lem:reachability-pebble-automaton`, Claim
`claim:reachability-basic-run`, Lemma `lem:children-of-configuration-in-pebble-run` and Claims
`claim:from-configuration-to-child-configuration-graph`,
`claim:from-child-configuration-graph-to-children`, which are internal steps of the proofs of
Theorems `thm:pebble-are-continuous` and `thm:pebble-are-for`. They speak about the string
representation of configurations and configuration graphs of pebble transducers, an auxiliary
encoding used only inside those proofs.  The step of `thm:pebble-are-for` for which the book uses
them -- that a pebble transducer computes a polyregular function -- is proved instead by the
induction on the number of pebbles of `RequestProject/PartD/PebblePoly.lean`. -/
import RequestProject.PartC.MSO
import RequestProject.PartD.PolyDef
import RequestProject.PartD.ForCompTop
import RequestProject.PartD.PolyFor
import RequestProject.PartD.PebbleReg
import RequestProject.PartD.PebblePoly
import RequestProject.PartD.PebbleForTop

namespace Transducers

/-! ## Polyregular functions (Definition `def:polyregular-functions`) -/

/-! **Example 33 (Marked squaring)** (`markedSquare`) is defined in
`RequestProject/PartD/MarkedSquare.lean`, together with the proof that it is continuous, which is
the main step in the proof of Theorem `thm:polyregular-functions-are-continuous` below. -/

/-! The family of prime polyregular functions (`Transducers.PolyregularFam`) and Definition
`def:polyregular-functions` itself (`Transducers.IsPolyregular`) are defined, unchanged, in
`RequestProject/PartD/PolyDef.lean`, so that the constructions proving Theorem
`thm:for-transducers-are-polyregular` can be developed before the statements below. -/

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
`lemma:prenex-normal-form` and Lemma `lem:for-closed-under-composition` can be developed before
the statements below. -/

/-! ### Equivalence with polyregular functions -/

/-- **Theorem `thm:for-transducers-are-polyregular`.**  A string-to-string function is polyregular
if and only if it is computed by a for-transducer. -/
theorem polyregular_iff_forTransducer {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsPolyregular f ↔ IsForTransducer f :=
  ⟨fun hf => isForTransducer_of_isPolyregular hf ‹Finite A› ‹Finite B›,
    PolyEnum.isPolyregular_of_isForTransducer⟩

/-- **Lemma `lemma:prenex-normal-form`.**  Every for-transducer is equivalent to one in prenex
form. -/
theorem forTransducer_prenex {A B : Type} (P : ForProg A B) :
    ∃ P' : ForProg A B, P'.PrenexForm ∧ ∀ w, P'.eval w = P.eval w :=
  forTransducer_prenex_aux P

/-- **Lemma `lem:for-closed-under-composition`.**  String-to-string functions computed by
for-transducers are closed under composition. -/
theorem forTransducer_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsForTransducer f) (hg : IsForTransducer g) : IsForTransducer (g ∘ f) :=
  forTransducer_comp_aux hf hg

/-! ## Pebble transducers

The syntax and the semantics of the pebble transducers -- `Transducers.PebbleView`,
`Transducers.viewOf`, `Transducers.PebbleAction`, `Transducers.Pebble`,
`Transducers.PebbleCfg`, `Transducers.Pebble.stepCfg`, `Transducers.Pebble.Reaches`,
`Transducers.Pebble.Computes` and `Transducers.IsPebbleTransducer` -- are defined, unchanged, in
`RequestProject/PartD/PebbleDef.lean`, so that the constructions proving Theorem
`thm:pebble-are-continuous` can be developed before the statements below. -/

/-! ### Continuity -/

/-- **Theorem `thm:pebble-are-continuous`.**  Pebble transducers compute continuous functions. -/
theorem pebble_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsPebbleTransducer f) : Continuous f :=
  continuous_of_isPebbleTransducer hf

/-! ### Equivalence with for-transducers -/

/-- **Theorem `thm:pebble-are-for`.**  Pebble transducers and for-transducers compute the same
string-to-string functions. -/
theorem pebble_iff_forTransducer {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsPebbleTransducer f ↔ IsForTransducer f :=
  ⟨fun h => (polyregular_iff_forTransducer f).mp (isPolyregular_of_isPebbleTransducer h),
    PebFor.isPebbleTransducer_of_isForTransducer⟩

end Transducers
