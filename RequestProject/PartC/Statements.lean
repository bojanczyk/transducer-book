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
import RequestProject.PartC.ContAux
import RequestProject.PartC.TwoWayCont
import RequestProject.PartC.TwoWayPrecomp
import RequestProject.PartC.TwoWayRat
import RequestProject.PartC.TwoWayCompFinal
import RequestProject.PartC.TwoWayRegular

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

/-- The map reverse function is continuous. -/
lemma continuous_mapReverse (A : Type) : Continuous (mapReverse A) :=
  continuous_mapLift continuous_reverse

/-- The map duplicate function is continuous. -/
lemma continuous_mapDuplicate (A : Type) : Continuous (mapDuplicate A) :=
  continuous_mapLift continuous_dup

/-- Regular functions are continuous (Theorem C.1.1; no finiteness assumption on
the alphabets is needed, since the prime regular functions are continuous over
any alphabets). -/
theorem continuous_of_isRegularFun {A B : Type} {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f := by
  induction hf with
  | base h =>
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact continuous_of_isRationalFun hrat
      · exact Continuous.congr
          (((continuous_map (e'.symm : Option A₀ → _)).comp
            ((continuous_mapReverse A₀).comp (continuous_map (e : _ → Option A₀)))))
          (fun w => (hfe w).symm)
      · exact Continuous.congr
          (((continuous_map (e'.symm : Option A₀ → _)).comp
            ((continuous_mapDuplicate A₀).comp (continuous_map (e : _ → Option A₀)))))
          (fun w => (hfe w).symm)
  | id A => exact continuous_id
  | comp _ _ ihf ihg => exact ihg.comp ihf

/-- **Theorem C.1.1 (continuity).**  Regular functions are continuous. -/
theorem regular_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : Continuous f :=
  continuous_of_isRegularFun hf

/-- **Theorem C.1.1 (composition).**  Regular functions are closed under
composition. -/
theorem regular_comp {A B C : Type} [Finite B] {f : List A → List B} {g : List B → List C}
    (hf : IsRegularFun f) (hg : IsRegularFun g) : IsRegularFun (g ∘ f) :=
  CompClosure.comp hf hg

/-- **Lemma C.1.2.**  String reversal and string duplication are continuous. -/
theorem reverse_duplicate_continuous {A : Type} [Finite A] :
    Continuous (List.reverse : List A → List A) ∧
      Continuous (fun w : List A => w ++ w) :=
  ⟨continuous_reverse, continuous_dup⟩

/-- **Lemma C.1.3.**  If a string-to-string function is continuous, then the
same is true for its map lifting. -/
theorem mapLift_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : Continuous f) : Continuous (mapLift f) :=
  continuous_mapLift hf

/-! ## C.2 Two-way transducers -/

/-! **Definition C.2.1 (two-way transducers)** (`TwoWay`, `Cfg`,
`TwoWay.stepCfg`, `TwoWay.Reaches`, `TwoWay.Computes` and `IsTwoWay`) is in
`RequestProject/PartC/TwoWayCont.lean`, together with the proof of
Theorem C.2.2 below. -/

/-! ### C.2.1 Continuity -/

/-- **Theorem C.2.2.**  Every function computed by a two-way transducer is
continuous. -/
theorem twoWay_continuous {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : Continuous f :=
  twoWay_continuous_aux hf

/-! ### C.2.2 Closure under composition -/

/-- **Lemma C.2.6.**  Functions computed by two-way transducers are closed under
pre-composition with Mealy machines. -/
theorem twoWay_precomp_mealy {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsMealy f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) :=
  isTwoWay_comp_compClosure (krohn_rhodes hf) hg

/-- **Corollary C.2.7.**  Functions computed by two-way transducers are closed
under pre-composition with rational functions. -/
theorem twoWay_precomp_rational {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsRationalFun f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) :=
  isTwoWay_comp_rational hf hg

/-- **Theorem C.2.5.**  Functions computed by two-way transducers are closed
under composition. -/
theorem twoWay_comp {A B C : Type} [Finite A] [Finite B] [Finite C]
    {f : List A → List B} {g : List B → List C}
    (hf : IsTwoWay f) (hg : IsTwoWay g) : IsTwoWay (g ∘ f) :=
  isTwoWay_comp_twoWay hf hg

/-! **Corollary C.2.8.**  The corollary is *printed* in the book as the inclusion
`two-way ⊆ regular`:

```
theorem twoWay_isRegular {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f
```

*Discrepancy with the book (a typo in the printed statement).*  The proof given
for the corollary -- "two-way transducers can compute all rational functions by
Corollary C.2.7, and they can compute map reverse and map duplicate by
Example C.2.4; finally, they are closed under composition thanks to
Theorem C.2.5" -- establishes the opposite inclusion `regular ⊆ two-way`, and
the sentence that follows the corollary in the book announces "the converse
inclusion" (that two-way transducers can be decomposed into the prime regular
functions) as Theorem C.2.9.  So the direction printed in the statement of the
corollary is a typo: what is a corollary of Theorem C.2.5 is the inclusion
`regular ⊆ two-way`, which is formalised and proved in full immediately below,
as `Transducers.isTwoWay_of_isRegularFun` and `Transducers.regularFun_isTwoWay`.

The inclusion `two-way ⊆ regular` as printed is exactly the hard half of
Theorem C.2.9; it is stated (and still open) below as the left-to-right
implication of `Transducers.twoWay_iff_regular`, and is therefore not duplicated
here. -/

/-- **Corollary C.2.8** (corrected): every regular function is computed by a
two-way transducer.  This is the statement that the book's proof of
Corollary C.2.8 establishes; see the discussion in the note above.

The auxiliary form carries the finiteness of the two alphabets as explicit
hypotheses, so that the induction on the composition tree has access to the
finiteness of the intermediate alphabets. -/
theorem isTwoWay_of_isRegularFun {A B : Type} {f : List A → List B}
    (hf : IsRegularFun f) : Finite A → Finite B → IsTwoWay f := by
  induction hf with
  | @base A B f h =>
      intro hA hB
      haveI := hA; haveI := hB
      rcases h with hrat | ⟨A₀, e, e', hfe⟩ | ⟨A₀, e, e', hfe⟩
      · exact isTwoWay_of_rational hrat
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 : IsTwoWay (mapReverse A₀) := isTwoWay_mapLift_reverse A₀
        have h3 := isTwoWay_precomp_map (isTwoWay_postMap h1 (e'.symm : Option A₀ → B))
          (e : A → Option A₀)
        exact (funext hfe : f = _) ▸ h3
      · haveI : Finite (Option A₀) := Finite.of_equiv A e
        haveI : Finite A₀ := Finite.of_injective (some : A₀ → Option A₀) (Option.some_injective _)
        have h1 : IsTwoWay (mapDuplicate A₀) := isTwoWay_mapLift_dup A₀
        have h3 := isTwoWay_precomp_map (isTwoWay_postMap h1 (e'.symm : Option A₀ → B))
          (e : A → Option A₀)
        exact (funext hfe : f = _) ▸ h3
  | id A => intro hA _; exact isTwoWay_id
  | @comp A B C hB f g _ _ ihf ihg =>
      intro hA hC
      haveI := hA; haveI := hB; haveI := hC
      exact isTwoWay_comp_twoWay (ihf hA hB) (ihg hB hC)

/-- **Corollary C.2.8** (corrected): every regular function is computed by a
two-way transducer. -/
theorem regularFun_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRegularFun f) : IsTwoWay f :=
  isTwoWay_of_isRegularFun hf ‹_› ‹_›

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
functions.

The right-to-left implication is Corollary C.2.8 (`regularFun_isTwoWay`, proved
above).  The left-to-right implication, which is the inclusion printed in the
statement of Corollary C.2.8 in the book, is the hard half and is still open. -/
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
