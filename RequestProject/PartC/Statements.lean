/-
Part C: Regular functions (Sections C.1, C.2 and C.3)
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file contains the definitions of Sections C.1-C.3 and the statements of
their theorems, lemmas and claims.  Proofs are left as `sorry`.

Not formalised here: Lemmas C.2.3, C.2.4 and C.2.12, which are internal steps in
the proofs of Theorems C.2.2, C.2.5 and C.2.9.  They speak about the string
representation of the reachable configuration graph of a two-way transducer,
an auxiliary encoding that is used only inside those proofs.
-/
import RequestProject.PartB.WeightedStatements

namespace Transducers

/-! ## The prime regular functions (Definition C.0.14) -/

/-- The map reverse function `w₁ # ⋯ # wₙ ↦ reverse w₁ # ⋯ # reverse wₙ`. -/
def mapReverse (A : Type) : List (Option A) → List (Option A) := mapLift List.reverse

/-- The map duplicate function `w₁ # ⋯ # wₙ ↦ w₁w₁ # ⋯ # wₙwₙ`. -/
def mapDuplicate (A : Type) : List (Option A) → List (Option A) :=
  mapLift (fun w => w ++ w)

/-- The family of prime regular functions: rational functions, map reverse and
map duplicate.  The last two have type `(A + 1)* → (A + 1)*`, which is expressed
by the bijections `e` and `e'` with `Option A₀`. -/
def RegularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsRationalFun f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

/-- **Definition C.0.14 (Regular functions).**  A string-to-string function is
regular if it is a finite composition of rational functions, map reverse and map
duplicate. -/
def IsRegularFun {A B : Type} (f : List A → List B) : Prop := CompClosure RegularFam A B f

/-! ## C.1 The prime regular functions -/

/-- **Theorem C.1.1 (continuity).**  Regular functions are continuous. -/
theorem regular_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f := by
  sorry

/-- **Theorem C.1.1 (composition).**  Regular functions are closed under
composition. -/
theorem regular_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (g ∘ f) := by
  sorry

/-- **Lemma C.1.2.**  String reversal and string duplication are continuous. -/
theorem reverse_duplicate_continuous {A : Type} [Finite A] :
    Continuous (List.reverse : List A → List A) ∧
      Continuous (fun w : List A => w ++ w) := by
  sorry

/-- **Lemma C.1.3.**  If a string-to-string function is continuous, then the
same is true for its map lifting. -/
theorem mapLift_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f) := by
  sorry

/-! ## C.2 Two-way transducers -/

/-- **Definition C.2.1.**  A two-way transducer: based on the letters adjacent
to the head and the current state, it either produces an output string and
halts (`Sum.inl`), or produces an output string, changes state, and moves the
head left (`false`) or right (`true`). -/
structure TwoWay (A B Q : Type) where
  /-- The initial state. -/
  init : Q
  /-- The transition function. -/
  step : Option A → Q → Option A → List B ⊕ (Q × List B × Bool)

/-- A configuration of a two-way transducer: the input to the left of the head,
the state, and the input to the right of the head; plus a halting vertex. -/
inductive Cfg (A Q : Type) : Type
  | conf : List A → Q → List A → Cfg A Q
  | halt : Cfg A Q

namespace TwoWay

variable {A B Q : Type}

/-- One step of the computation: the produced output and the next
configuration, if any. -/
def stepCfg (M : TwoWay A B Q) : Cfg A Q → Option (List B × Cfg A Q)
  | Cfg.halt => none
  | Cfg.conf u q v =>
      match M.step u.getLast? q v.head? with
      | Sum.inl o => some (o, Cfg.halt)
      | Sum.inr (q', o, true) =>
          match v with
          | [] => none
          | a :: v' => some (o, Cfg.conf (u ++ [a]) q' v')
      | Sum.inr (q', o, false) =>
          match u.getLast? with
          | none => none
          | some a => some (o, Cfg.conf u.dropLast q' (a :: v))

/-- Reachability in the configuration graph, recording the produced output. -/
inductive Reaches (M : TwoWay A B Q) : Cfg A Q → List B → Cfg A Q → Prop
  | refl (c : Cfg A Q) : Reaches M c [] c
  | step {c c' c'' : Cfg A Q} {o o' : List B} :
      M.stepCfg c = some (o, c') → Reaches M c' o' c'' → Reaches M c (o ++ o') c''

/-- The transducer produces the output `v` on the input `w`: the run started in
the initial configuration reaches the halting vertex, producing `v`. -/
def Computes (M : TwoWay A B Q) (w : List A) (v : List B) : Prop :=
  M.Reaches (Cfg.conf [] M.init w) v Cfg.halt

end TwoWay

/-- A (total) function computed by a two-way transducer. -/
def IsTwoWay {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (M : TwoWay A B Q), ∀ w, M.Computes w (f w)

/-! ### C.2.1 Continuity -/

/-- **Theorem C.2.2.**  Every function computed by a two-way transducer is
continuous. -/
theorem twoWay_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : Continuous f := by
  sorry

/-! ### C.2.2 Closure under composition -/

/-- **Lemma C.2.6.**  Functions computed by two-way transducers are closed under
pre-composition with Mealy machines. -/
theorem twoWay_precomp_mealy {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) := by
  sorry

/-- **Corollary C.2.7.**  Functions computed by two-way transducers are closed
under pre-composition with rational functions. -/
theorem twoWay_precomp_rational {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsRationalFun f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) := by
  sorry

/-- **Theorem C.2.5.**  Functions computed by two-way transducers are closed
under composition. -/
theorem twoWay_comp {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsTwoWay f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) := by
  sorry

/-- **Corollary C.2.8.**  If a function is computed by a two-way transducer,
then it is regular. -/
theorem twoWay_isRegular {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f := by
  sorry

/-! ### C.2.3 Decidability of equivalence

Equivalence of regular functions (Theorem C.1.4) is decidable; the algorithm can
be run directly on two-way transducers.  A two-way transducer over the alphabet
`ℕ` is coded by a finite lookup table for its transition function, transitions
that are absent from the table halting with empty output. -/

/-- A finite description of a two-way transducer with states and letters coded
by natural numbers. -/
abbrev TwoWayCode := List ((Option ℕ × ℕ × Option ℕ) × (List ℕ ⊕ (ℕ × List ℕ × Bool)))

/-- The two-way transducer described by a code. -/
def twoWayCodeAut (c : TwoWayCode) : TwoWay ℕ ℕ ℕ where
  init := 0
  step := fun l q r =>
    match c.lookup (l, q, r) with
    | some x => x
    | none => Sum.inl []

/-- The relation computed by the two-way transducer described by a code. -/
def twoWayCodeRel (c : TwoWayCode) : List ℕ → List ℕ → Prop := (twoWayCodeAut c).Computes

/-- The promise that a code describes a transducer that computes a total
function. -/
def TwoWayCodeTotal (c : TwoWayCode) : Prop := ∀ w, ∃ v, twoWayCodeRel c w v

/-- **Theorem C.1.4.**  Equivalence is decidable for regular functions (here:
for the two-way transducers that compute them, cf. Theorem C.2.9). -/
theorem regular_equivalence_decidable :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2) := by
  sorry

/-! ### C.2.4 Decomposition into prime functions -/

/-- **Theorem C.2.9.**  Two-way transducers compute exactly the regular
functions. -/
theorem twoWay_iff_regular {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsTwoWay f ↔ IsRegularFun f := by
  sorry

open scoped Classical in
/-- **Lemma C.2.10.**  Regular functions are closed under map lifting,
concatenation, and conditionals over a regular language. -/
theorem regular_closure_properties {A B : Type} [Finite A] [Finite B]
    {f g : List A → List B} (hf : IsRegularFun f) (hg : IsRegularFun g) :
    IsRegularFun (mapLift f) ∧
      IsRegularFun (fun w => f w ++ g w) ∧
      ∀ L : Language A, L.IsRegular →
        IsRegularFun (fun w => if w ∈ L then f w else g w) := by
  sorry

/-- **Claim C.2.11.**  For regular functions `f₁ : A₁* → B₁*` and
`f₂ : A₂* → B₂*` with disjoint input and output alphabets, the function
`f₁ + f₂` is regular: it applies `f₁` to inputs using only letters of `A₁`,
`f₂` to inputs using only letters of `A₂`, and returns a fixed string `⊥` using
both output alphabets otherwise. -/
theorem sum_of_regular {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) := by
  sorry

/-! ## C.3 Streaming string transducers -/

/-- A register update is *copyless* if each register name occurs at most once in
the concatenation of the strings assigned to the registers. -/
def Copyless {X B : Type} [Fintype X] (u : X → List (X ⊕ B)) : Prop :=
  ((Finset.univ.toList.map u).flatten.filterMap
      (fun z => match z with | Sum.inl x => some x | Sum.inr _ => none)).Nodup

/-- **Definition C.3.1 (sst).**  A streaming string transducer. -/
structure SST (A B Q X : Type) [Fintype X] where
  /-- The initial state. -/
  init : Q
  /-- The transition function: a new state and a register update. -/
  step : Q → A → Q × (X → List (X ⊕ B))
  /-- Register updates are copyless. -/
  step_copyless : ∀ q a, Copyless (step q a).2
  /-- The final output function. -/
  final : Q → List (X ⊕ B)

namespace SST

variable {A B Q X : Type} [Fintype X]

/-- Substituting the contents of the registers into a string over `X + B`. -/
def subst (η : X → List B) (s : List (X ⊕ B)) : List B :=
  (s.map (fun z => match z with | Sum.inl x => η x | Sum.inr b => [b])).flatten

/-- Reading one input letter. -/
def stepConfig (T : SST A B Q X) (c : Q × (X → List B)) (a : A) : Q × (X → List B) :=
  ((T.step c.1 a).1, fun x => subst c.2 ((T.step c.1 a).2 x))

/-- The configuration reached after reading an input string. -/
def runConfig (T : SST A B Q X) (w : List A) : Q × (X → List B) :=
  w.foldl T.stepConfig (T.init, fun _ => [])

/-- The semantics of a streaming string transducer. -/
def eval (T : SST A B Q X) (w : List A) : List B :=
  subst (T.runConfig w).2 (T.final (T.runConfig w).1)

end SST

/-- A function computed by a streaming string transducer. -/
def IsSST {A B : Type} (f : List A → List B) : Prop :=
  ∃ (Q X : Type) (_ : Finite Q) (instX : Fintype X) (T : @SST A B Q X instX), T.eval = f

/-- **Theorem C.3.2.**  Streaming string transducers compute exactly the regular
functions. -/
theorem sst_iff_regular {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSST f ↔ IsRegularFun f := by
  sorry

end Transducers
