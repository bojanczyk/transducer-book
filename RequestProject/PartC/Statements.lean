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
import RequestProject.PartC.RegClosure
import RequestProject.PartC.SnakeReg
import RequestProject.PartC.SSTRegular
import RequestProject.PartC.SSTTwoWay
import RequestProject.PartC.WeightedRegClosure
import RequestProject.PartC.RegEqDec

namespace Transducers

/-! ## The prime regular functions (Definition C.0.14)

The definitions `Transducers.mapReverse`, `Transducers.mapDuplicate`,
`Transducers.RegularFam` and `Transducers.IsRegularFun` (Definition C.0.14) used
to be given here; they have been moved, unchanged, to
`RequestProject/PartC/RegularDef.lean`, which this file imports, so that the
constructions used in the proofs of Lemma C.2.10 and Claim C.2.11 could be
developed before this file. -/

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

/-! ### Equivalence (Theorem C.1.4)

The book proves Theorem C.1.4 by a reduction to zeroness -- equivalently, to
equivalence -- of weighted automata over the field of rationals, and the
reduction uses the *prime decomposition* of a regular function: the class of
functions that can be post-composed with weighted automata is closed under
composition, contains the rational functions by Lemma B.3.5
(`Transducers.weighted_precomp_rational`), and contains map reverse and map
duplicate, for which the book gives the two constructions with triples of
states.

That proof is formalised in `RequestProject/PartC/WeightedRegClosure.lean` and
`RequestProject/PartC/WeightedMapLift.lean`, on linear representations of
weighted automata rather than on the automata themselves:

* `Transducers.isWeighted_comp_mapReverse` -- the map reverse construction,
  where running a block backwards is transposition of the matrices of the
  representation (this is where commutativity of the semiring is used, as the
  book points out);
* `Transducers.isWeighted_comp_mapDuplicate` -- the map duplicate construction,
  where the weight of a transition of the new automaton is a product of the
  weights of two transitions of the original one, realised by the Kronecker
  square of the matrices;
* `Transducers.isWeighted_comp_regular` -- the induction on the prime
  decomposition, i.e. the statement that weighted automata are closed under
  pre-composition with regular functions;
* `Transducers.exists_injective_weighted` -- observation (a) of the book:
  output strings are represented injectively by rational numbers, by a weighted
  automaton;
* `Transducers.regularFun_eq_iff_weighted_eq` -- the reduction itself: two
  regular functions are equal if and only if the two weighted automata over `ℚ`
  obtained by post-composing them with the injective automaton are equal;
* `Transducers.regularFun_eq_of_short` -- the resulting decision procedure in
  semantic form: two regular functions over finite alphabets are equal as soon
  as they agree on the finitely many inputs of length at most a bound supplied
  by the zeroness criterion for weighted automata over a field
  (`Transducers.weighted_eq_of_short`, the mathematical content of
  Theorems B.3.3 and B.3.7).

The statement of the decidability on *finite descriptions* of transducers is
`Transducers.regular_equivalence_decidable` in Section C.2.3 below; see its
docstring. -/

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
Theorem C.2.9; it is stated (and proved) below as
`Transducers.twoWay_isRegular`, the left-to-right implication of
`Transducers.twoWay_iff_regular`, and is therefore not duplicated here. -/

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

/-  The definitions `Transducers.TwoWayCode`, `Transducers.twoWayCodeAut`,
`Transducers.twoWayCodeRel` and `Transducers.TwoWayCodeTotal` used to be given
here; they have been moved, unchanged, to
`RequestProject/PartC/RegCodeSan.lean`, which this file imports, so that the
decision procedure below could be developed before this file. -/

/-  The unconditional form of Theorem C.1.4 is

theorem regular_equivalence_decidable :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2) := by
  sorry

The mathematical content of the book's proof -- the reduction to equivalence of
weighted automata over the field of rationals through the prime decomposition,
including the constructions for map reverse and map duplicate -- is proved in
`RequestProject/PartC/WeightedRegClosure.lean`; see the note at the end of
Section C.1 above, and in particular `Transducers.regularFun_eq_of_short`, which
reduces the equivalence of two regular functions to a finite check.  What is
missing for the unconditional statement is only the *effective* form of that
chain on codes: a code has to be turned into a linear representation over `ℚ`
and the bound has to be computed from it, and, as for Theorems B.3.3 and B.3.7,
this runs into the absence of arithmetic on `ℤ` and `ℚ` in Mathlib's
`Primrec`/`Computable` API (see `RequestProject/PartB/Effective.lean`).

That missing ingredient is isolated in `RequestProject/PartC/EffectiveReg.lean`
as the two hypotheses `Transducers.EffectiveTwoWayEvalEq` (two coded two-way
transducers can be compared effectively on a given input) and
`Transducers.EffectiveTwoWayBound` (an equivalence bound can be computed from
the two codes; that such a bound *exists* is
`Transducers.exists_twoWayCode_bound`, proved from the book's argument).  The
version below takes them as explicit assumptions, exactly as Theorems B.3.3,
B.3.4, B.3.7 and B.4.2 take `Transducers.EffectiveWeightedEvalEq` as an explicit
assumption and Theorem B.1.6 takes the undecidability of the Post correspondence
problem as an explicit assumption.  Everything else -- that the finitely many
inputs to be tested may be taken over the letters of the two codes together with
one fresh letter, and the assembly of the decision procedure -- is discharged in
full in `RequestProject/PartC/RegEqDec.lean`. -/

/-- **Theorem C.1.4.**  Equivalence is decidable for regular functions (here:
for the two-way transducers that compute them, cf. Theorem C.2.9).

Proved from the effectivity hypotheses `EffectiveTwoWayEvalEq` and
`EffectiveTwoWayBound` of `RequestProject/PartC/EffectiveReg.lean`; see the
comment above. -/
theorem regular_equivalence_decidable (hEval : EffectiveTwoWayEvalEq)
    (hBound : EffectiveTwoWayBound) :
    DecidableUnderPromise
      (fun p : TwoWayCode × TwoWayCode => TwoWayCodeTotal p.1 ∧ TwoWayCodeTotal p.2)
      (fun p => twoWayCodeRel p.1 = twoWayCodeRel p.2) :=
  regular_equivalence_decidable_aux hEval hBound

/-! ### C.2.4 Decomposition into prime functions -/

/-- **Theorem C.2.9, left-to-right implication** (equivalently, the inclusion as
it is *printed* in Corollary C.2.8): every function computed by a two-way
transducer is regular, i.e. it can be decomposed into prime functions.

This is the hard half of Theorem C.2.9.  It is reduced, in
`RequestProject/PartC/SnakeReg.lean`, to the book's snake lemma
`Transducers.boundedWidth_isRegular`, whose base cases `k = 0` and `k = 1` are
proved in `RequestProject/PartC/SnakeBase.lean` and whose induction step
`Transducers.boundedWidth_isRegular_step` is proved in
`RequestProject/PartC/SnakeReg.lean`: a run that halts visits every column at most `|Q|` times
(`TwoWay.widthLe_card`), so the function computed by a two-way transducer with
state set `Q` is its own width-`|Q|` output function `TwoWay.widthOut M |Q|`,
and it remains to see that the width-`k` output function of a two-way transducer
is regular for every `k`.

The book proves the snake lemma by induction on the width, decomposing a run of
width `k` into *looping* parts and *progressing* parts along the
*record-breaking* columns; the parts have width at most `k - 1`, they are cut
out of the input by rational functions, and they are glued back together with
the three closure properties of `regular_closure_properties` (Lemma C.2.10)
below.  The two closure ingredients that the book's argument rests on
(Lemma C.2.10 and Claim C.2.11) are proved, as is the reduction to snakes and
the combinatorics of the width induction:
`RequestProject/PartC/SnakeWalk.lean`, `RequestProject/PartC/SnakeRec.lean` and
`RequestProject/PartC/SnakeLoop.lean` prove that a halting run of width at most
`k ≥ 2` splits into finitely many consecutive pieces of width at most `k - 1`
whose outputs concatenate to the output of the run
(`TwoWay.runOutput_splits`).  The machine-theoretic half of the induction step
-- that the output of such a piece is the value of a width-`(k-1)` snake
function on a factor of the input cut out by a rational function -- is supplied
by the `RequestProject/PartC/SnakeChk*.lean` family, which builds the rational
annotation marking the record-breaking columns. -/
theorem twoWay_isRegular {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f :=
  isRegularFun_of_isTwoWay hf

/-- **Theorem C.2.9.**  Two-way transducers compute exactly the regular
functions.

The right-to-left implication is Corollary C.2.8 (`regularFun_isTwoWay`, proved
above).  The left-to-right implication is `twoWay_isRegular` above, the hard
half; see the discussion in its docstring. -/
theorem twoWay_iff_regular {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsTwoWay f ↔ IsRegularFun f :=
  ⟨fun hf => twoWay_isRegular hf, fun hf => regularFun_isTwoWay hf⟩

open scoped Classical in
/-- **Lemma C.2.10.**  Regular functions are closed under map lifting,
concatenation, and conditionals over a regular language. -/
theorem regular_closure_properties {A B : Type} [Finite A] [Finite B]
    {f g : List A → List B} (hf : IsRegularFun f) (hg : IsRegularFun g) :
    IsRegularFun (mapLift f) ∧
      IsRegularFun (fun w => f w ++ g w) ∧
      ∀ L : Language A, L.IsRegular →
        IsRegularFun (fun w => if w ∈ L then f w else g w) :=
  ⟨isRegularFun_mapLift hf, isRegularFun_concat hf hg,
    fun _ hL => isRegularFun_cond hf hg hL⟩

/-  **Claim C.2.11** as printed in the book is *false* on the empty input: the
empty string uses only letters of `A₁` and, at the same time, only letters of
`A₂`, so the first two requirements below conflict on it unless `f₁ ε` and
`f₂ ε` are both empty (see `Transducers.not_sum_of_regular_nil`, a
counterexample with `f₁` constant and `f₂` the identity).  The original
statement is kept here, commented out, and the corrected statement -- which
asks for the two requirements on *nonempty* inputs only, and leaves the value
on the empty input unspecified -- follows it.  The correction is harmless for
the use made of the claim in the book: in the proof of Lemma C.2.10 the blocks
that the sum is applied to are always nonempty.

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
-/

/-- **Claim C.2.11** (corrected on the empty input; see the note above).  For
regular functions `f₁ : A₁* → B₁*` and `f₂ : A₂* → B₂*` with disjoint input and
output alphabets, the function `f₁ + f₂` is regular: it applies `f₁` to the
nonempty inputs using only letters of `A₁`, `f₂` to the nonempty inputs using
only letters of `A₂`, and returns a fixed string `⊥` using both output alphabets
otherwise.  The output alphabets are assumed to be nonempty, as they must be for
`⊥` to exist. -/
theorem sum_of_regular {A₁ A₂ B₁ B₂ : Type} [Finite A₁] [Finite A₂] [Finite B₁] [Finite B₂]
    [Nonempty B₁] [Nonempty B₂]
    {f₁ : List A₁ → List B₁} {f₂ : List A₂ → List B₂}
    (hf₁ : IsRegularFun f₁) (hf₂ : IsRegularFun f₂) :
    ∃ (bot : List (B₁ ⊕ B₂)) (F : List (A₁ ⊕ A₂) → List (B₁ ⊕ B₂)),
      (∃ b₁, Sum.inl b₁ ∈ bot) ∧ (∃ b₂, Sum.inr b₂ ∈ bot) ∧
      IsRegularFun F ∧
      (∀ u : List A₁, u ≠ [] → F (u.map Sum.inl) = (f₁ u).map Sum.inl) ∧
      (∀ u : List A₂, u ≠ [] → F (u.map Sum.inr) = (f₂ u).map Sum.inr) ∧
      (∀ w, (¬ ∃ u : List A₁, w = u.map Sum.inl) → (¬ ∃ u : List A₂, w = u.map Sum.inr) →
        F w = bot) :=
  sum_of_regular_aux hf₁ hf₂

/-! ## C.3 Streaming string transducers -/

/-! The definitions `Transducers.Copyless`, `Transducers.SST` (Definition C.3.1),
its semantics `Transducers.SST.subst`, `Transducers.SST.stepConfig`,
`Transducers.SST.runConfig`, `Transducers.SST.eval` and `Transducers.IsSST` used
to be given here; they have been moved, unchanged, to
`RequestProject/PartC/SSTDef.lean`, which this file imports (through
`RequestProject/PartC/SSTRegular.lean`), so that the constructions used in the
proof of Theorem C.3.2 could be developed before this file. -/

/-- **Theorem C.3.2.**  Streaming string transducers compute exactly the regular
functions.

The right-to-left implication is `isSST_of_isRegularFun`
(`RequestProject/PartC/SSTRegular.lean`): sst's are closed under
post-composition with the prime regular functions, so they contain every
composition of primes.  The left-to-right implication goes through
Theorem C.2.9: an sst is simulated by a two-way transducer
(`isTwoWay_of_isSST`, `RequestProject/PartC/SSTTwoWay.lean`), and a two-way
transducer computes a regular function (`twoWay_isRegular`). -/
theorem sst_iff_regular {A B : Type} [Finite A] [Finite B] (f : List A → List B) :
    IsSST f ↔ IsRegularFun f :=
  ⟨fun hf => twoWay_isRegular (isTwoWay_of_isSST hf), fun hf => isSST_of_isRegularFun hf⟩

end Transducers
