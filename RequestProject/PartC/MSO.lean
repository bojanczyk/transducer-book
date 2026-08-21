/-
Part C, Section C.4: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

Monadic second-order logic over strings, mso relabellings, mso transductions
and the first-order fragment, together with the statements of the theorems of
Section C.4.  Proofs are left as `sorry`.

Two conventions are used.

* Variables are named by natural numbers; a valuation assigns a position to
  every first-order variable and a set of positions to every second-order
  variable.  A formula with `k` free first-order variables is used with the
  variables `0, …, k-1`.
* The book uses an extended syntax in which first-order variables have
  polynomial types `τ = n^{d₁} + ⋯ + n^{d_k}` (Section C.4.3).  For the linear
  types `τ = k · n + c` that are used in mso transductions, quantification over
  an element of `τ (w)` is the same as a case distinction over the `k + c`
  variants, and a variable of type `2^τ` is the same as `k` set variables plus
  `c` Booleans.  Accordingly, `MSOTransduction` below is presented by families
  of ordinary mso formulas indexed by the variants, which is equivalent to the
  presentation in Definition C.4.7.

Not formalised here: Claim C.4.5, Lemma C.4.9 and Claim C.4.14, which are
internal steps of the proofs of Theorems C.4.4, C.4.8 and C.4.11.
-/
import RequestProject.PartC.Statements
import RequestProject.PartC.KTypes

namespace Transducers

/-! ## C.4.1 Monadic second-order logic -/

/-- Formulas of monadic second-order logic over strings with letters in `A`.
First-order variables range over positions, second-order variables over sets of
positions; both kinds of variables are named by natural numbers. -/
inductive MSO (A : Type) : Type
  /-- The order test `x_i ≤ x_j`. -/
  | le : ℕ → ℕ → MSO A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → MSO A
  /-- The membership test `x_i ∈ X_j`. -/
  | mem : ℕ → ℕ → MSO A
  /-- Negation. -/
  | not : MSO A → MSO A
  /-- Conjunction. -/
  | and : MSO A → MSO A → MSO A
  /-- Disjunction. -/
  | or : MSO A → MSO A → MSO A
  /-- First-order existential quantification `∃ x_i`. -/
  | exFO : ℕ → MSO A → MSO A
  /-- Second-order existential quantification `∃ X_i`. -/
  | exSO : ℕ → MSO A → MSO A

namespace MSO

variable {A : Type}

/-- Satisfaction of a formula in a string, under a valuation of the first-order
variables (by positions) and of the second-order variables (by sets of
positions). -/
def Sat (w : List A) : (ℕ → ℕ) → (ℕ → Set ℕ) → MSO A → Prop
  | fo, _, le i j => fo i ≤ fo j
  | fo, _, lab a i => w[fo i]? = some a
  | fo, so, mem i j => fo i ∈ so j
  | fo, so, not φ => ¬ Sat w fo so φ
  | fo, so, and φ ψ => Sat w fo so φ ∧ Sat w fo so ψ
  | fo, so, or φ ψ => Sat w fo so φ ∨ Sat w fo so ψ
  | fo, so, exFO i φ => ∃ p < w.length, Sat w (Function.update fo i p) so φ
  | fo, so, exSO i φ => ∃ S ⊆ {p | p < w.length}, Sat w fo (Function.update so i S) φ

/-- A formula is first-order if it uses neither set quantification nor set
membership. -/
def IsFO : MSO A → Prop
  | le _ _ => True
  | lab _ _ => True
  | mem _ _ => False
  | not φ => IsFO φ
  | and φ ψ => IsFO φ ∧ IsFO ψ
  | or φ ψ => IsFO φ ∧ IsFO ψ
  | exFO _ φ => IsFO φ
  | exSO _ _ => False

/-- The quantifier rank of a formula: the maximal number of nested
quantifiers. -/
def qrank : MSO A → ℕ
  | le _ _ => 0
  | lab _ _ => 0
  | mem _ _ => 0
  | not φ => qrank φ
  | and φ ψ => max (qrank φ) (qrank ψ)
  | or φ ψ => max (qrank φ) (qrank ψ)
  | exFO _ φ => qrank φ + 1
  | exSO _ φ => qrank φ + 1

/-- The free first-order variables of a formula. -/
def freeFO : MSO A → Set ℕ
  | le i j => {i, j}
  | lab _ i => {i}
  | mem i _ => {i}
  | not φ => freeFO φ
  | and φ ψ => freeFO φ ∪ freeFO ψ
  | or φ ψ => freeFO φ ∪ freeFO ψ
  | exFO i φ => freeFO φ \ {i}
  | exSO _ φ => freeFO φ

/-- The free second-order variables of a formula. -/
def freeSO : MSO A → Set ℕ
  | le _ _ => ∅
  | lab _ _ => ∅
  | mem _ j => {j}
  | not φ => freeSO φ
  | and φ ψ => freeSO φ ∪ freeSO ψ
  | or φ ψ => freeSO φ ∪ freeSO ψ
  | exFO _ φ => freeSO φ
  | exSO i φ => freeSO φ \ {i}

end MSO

/-- A language is definable in monadic second-order logic. -/
def MSODefinable {A : Type} (L : Language A) : Prop :=
  ∃ φ : MSO A, ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L

/-- A language is definable in first-order logic. -/
def FODefinable {A : Type} (L : Language A) : Prop :=
  ∃ φ : MSO A, φ.IsFO ∧
    ∀ (w : List A) (fo : ℕ → ℕ) (so : ℕ → Set ℕ), MSO.Sat w fo so φ ↔ w ∈ L

/-- **Theorem C.4.1.**  A language is regular if and only if it is definable in
monadic second-order logic. -/
theorem regular_iff_msoDefinable {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L := by
  sorry

open scoped Classical in
/-- The annotation `w ⊗ {x₁} ⊗ ⋯ ⊗ {x_k} ⊗ X₁ ⊗ ⋯ ⊗ X_l` of a string by the
values of `k` first-order and `l` second-order variables. -/
noncomputable def annotate {A : Type} (k l : ℕ) (w : List A)
    (fo : Fin k → ℕ) (so : Fin l → Set ℕ) : List (A × (Fin k → Bool) × (Fin l → Bool)) :=
  w.zipIdx.map (fun z => (z.1, fun i => decide (fo i = z.2), fun j => decide (z.2 ∈ so j)))

/-- Extend a valuation of the variables `0, …, k-1` to all variables. -/
def extFO (k : ℕ) (fo : Fin k → ℕ) : ℕ → ℕ :=
  fun i => if h : i < k then fo ⟨i, h⟩ else 0

/-- Extend a valuation of the set variables `0, …, l-1` to all variables. -/
def extSO (l : ℕ) (so : Fin l → Set ℕ) : ℕ → Set ℕ :=
  fun j => if h : j < l then so ⟨j, h⟩ else ∅

/-- **Lemma C.4.2.**  For an mso formula whose free variables are among
`x₁, …, x_k, X₁, …, X_l`, the set of annotated strings that satisfy it is a
regular language over the alphabet `A × 2^{k+l}`. -/
theorem mso_annotated_regular {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} := by
  sorry

/-! ## C.4.2 Rational functions in terms of logic -/

/-- **Definition C.4.3 (mso relabelling).**  A finite family of mso formulas
with one free first-order variable (the variable `0`), exactly one of which
holds in each position, together with an output string for each formula and an
output string for the empty input. -/
structure MSORelabelling (A B : Type) where
  /-- The (finite) index set of the formulas. -/
  Idx : Type
  /-- Finiteness of the index set. -/
  finIdx : Finite Idx
  /-- The formulas, each with one free first-order variable `x₀`. -/
  form : Idx → MSO A
  /-- The output string of each formula. -/
  out : Idx → List B
  /-- The output string for the empty input. -/
  emptyOut : List B
  /-- In every position of every input string exactly one formula holds. -/
  unique : ∀ (w : List A) (p : ℕ), p < w.length →
    ∃! i : Idx, MSO.Sat w (fun _ => p) (fun _ => ∅) (form i)

namespace MSORelabelling

variable {A B : Type}

/-- The function defined by an mso relabelling: each position contributes the
output string of the unique formula that holds in it. -/
def Relabels (R : MSORelabelling A B) (w : List A) (v : List B) : Prop :=
  (w = [] ∧ v = R.emptyOut) ∨
  (w ≠ [] ∧ ∃ g : ℕ → R.Idx,
    (∀ p < w.length, MSO.Sat w (fun _ => p) (fun _ => ∅) (R.form (g p))) ∧
    v = ((List.range w.length).map (fun p => R.out (g p))).flatten)

/-- All formulas of the relabelling are first-order. -/
def AllFO (R : MSORelabelling A B) : Prop := ∀ i, (R.form i).IsFO

end MSORelabelling

/-- A function defined by an mso relabelling. -/
def IsMSORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, ∀ w, R.Relabels w (f w)

/-- A function defined by a first-order relabelling. -/
def IsFORelabelling {A B : Type} (f : List A → List B) : Prop :=
  ∃ R : MSORelabelling A B, R.AllFO ∧ ∀ w, R.Relabels w (f w)

/-- **Theorem C.4.4.**  A string-to-string function is rational if and only if
it is definable by an mso relabelling. -/
theorem rational_iff_msoRelabelling {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ IsMSORelabelling f := by
  sorry

/-- **Claim C.4.6.**  For an mso relabelling, the language of strings over the
alphabet `A × Φ` in which every position is labelled by a formula that holds in
that position is regular. -/
theorem msoRelabelling_annotation_regular {A B : Type} [Finite A] (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)} := by
  sorry

/-- **Lemma C.4.10.**  For a finite set of mso formulas with one or two free
first-order variables there is a letter-to-letter rational function `f : A* → C*`
such that the formulas with one free variable correspond to sets of letters of
the output, and the formulas with two free variables correspond to regular
languages of infixes of the output. -/
theorem mso_formulas_via_rational {A : Type} [Finite A]
    (Φ₁ Φ₂ : Set (MSO A)) (hΦ₁ : Φ₁.Finite) (hΦ₂ : Φ₂.Finite) :
    ∃ (C : Type) (_ : Finite C) (f : List A → List C),
      IsRationalFun f ∧ LengthPreserving f ∧
      (∀ φ ∈ Φ₁, ∃ F : Set C, ∀ (w : List A) (x : ℕ), x < w.length →
        (MSO.Sat w (fun _ => x) (fun _ => ∅) φ ↔ ∃ c ∈ F, (f w)[x]? = some c)) ∧
      (∀ φ ∈ Φ₂, ∃ L : Language C, L.IsRegular ∧ ∀ (w : List A) (x y : ℕ),
        x ≤ y → y < w.length →
        (MSO.Sat w (fun i => if i = 0 then x else y) (fun _ => ∅) φ ↔
          ((f w).drop x).take (y - x + 1) ∈ L)) := by
  sorry

/-! ## C.4.3 Regular functions in terms of logic -/

/-- **Definition C.4.7 (string-to-string mso transduction).**  The elements of
the output universe come from a linear type `τ = k · n + c`: `k` copies of the
positions of the input string, and `c` extra elements.  The universe, letter and
order formulas are given by families indexed by the variants of `τ`. -/
structure MSOTransduction (A B : Type) where
  /-- The number of copies of the input positions. -/
  copies : ℕ
  /-- The number of extra (constant) elements. -/
  extra : ℕ
  /-- Universe formulas for the copies of the positions; free variable `x₀`. -/
  univP : Fin copies → MSO A
  /-- Universe formulas for the extra elements; sentences. -/
  univC : Fin extra → MSO A
  /-- Letter formulas for the copies of the positions; free variable `x₀`. -/
  labP : Fin copies → B → MSO A
  /-- Letter formulas for the extra elements; sentences. -/
  labC : Fin extra → B → MSO A
  /-- Order formulas between two copies of positions; free variables `x₀, x₁`. -/
  ordPP : Fin copies → Fin copies → MSO A
  /-- Order formulas between a copy of a position and an extra element. -/
  ordPC : Fin copies → Fin extra → MSO A
  /-- Order formulas between an extra element and a copy of a position. -/
  ordCP : Fin extra → Fin copies → MSO A
  /-- Order formulas between two extra elements. -/
  ordCC : Fin extra → Fin extra → MSO A

namespace MSOTransduction

variable {A B : Type}

/-- The elements of the type `τ = k · n + c`, before selection by the universe
formulas. -/
abbrev Elt (T : MSOTransduction A B) : Type := (Fin T.copies × ℕ) ⊕ Fin T.extra

/-- The elements selected by the universe formulas. -/
def selected (T : MSOTransduction A B) (w : List A) : T.Elt → Prop
  | Sum.inl (i, p) => p < w.length ∧ MSO.Sat w (fun _ => p) (fun _ => ∅) (T.univP i)
  | Sum.inr j => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.univC j)

/-- The order defined by the order formulas. -/
def ordRel (T : MSOTransduction A B) (w : List A) : T.Elt → T.Elt → Prop
  | Sum.inl (i, p), Sum.inl (i', p') =>
      MSO.Sat w (fun v => if v = 0 then p else p') (fun _ => ∅) (T.ordPP i i')
  | Sum.inl (i, p), Sum.inr j => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordPC i j)
  | Sum.inr j, Sum.inl (i, p) => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.ordCP j i)
  | Sum.inr j, Sum.inr j' => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.ordCC j j')

/-- The labelling defined by the letter formulas. -/
def labRel (T : MSOTransduction A B) (w : List A) : T.Elt → B → Prop
  | Sum.inl (i, p), b => MSO.Sat w (fun _ => p) (fun _ => ∅) (T.labP i b)
  | Sum.inr j, b => MSO.Sat w (fun _ => 0) (fun _ => ∅) (T.labC j b)

/-- The semantics of an mso transduction: the output string consists of the
selected elements, ordered by the order formula and labelled by the letter
formulas. -/
def Outputs (T : MSOTransduction A B) (w : List A) (v : List B) : Prop :=
  ∃ es : List T.Elt,
    es.Nodup ∧
    (∀ x, x ∈ es ↔ T.selected w x) ∧
    (∀ (i j : ℕ) (hi : i < es.length) (hj : j < es.length),
      i < j → T.ordRel w (es.get ⟨i, hi⟩) (es.get ⟨j, hj⟩)) ∧
    es.length = v.length ∧
    ∀ (i : ℕ) (hi : i < es.length) (hi' : i < v.length),
      T.labRel w (es.get ⟨i, hi⟩) (v.get ⟨i, hi'⟩)

/-- All formulas of the transduction are first-order. -/
def AllFO (T : MSOTransduction A B) : Prop :=
  (∀ i, (T.univP i).IsFO) ∧ (∀ j, (T.univC j).IsFO) ∧
  (∀ i b, (T.labP i b).IsFO) ∧ (∀ j b, (T.labC j b).IsFO) ∧
  (∀ i i', (T.ordPP i i').IsFO) ∧ (∀ i j, (T.ordPC i j).IsFO) ∧
  (∀ j i, (T.ordCP j i).IsFO) ∧ (∀ j j', (T.ordCC j j').IsFO)

end MSOTransduction

/-- A function defined by a string-to-string mso transduction. -/
def IsMSOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, ∀ w, T.Outputs w (f w)

/-- A function defined by a first-order transduction. -/
def IsFOTransduction {A B : Type} (f : List A → List B) : Prop :=
  ∃ T : MSOTransduction A B, T.AllFO ∧ ∀ w, T.Outputs w (f w)

/-- **Theorem C.4.8.**  String-to-string mso transductions define exactly the
regular functions. -/
theorem msoTransduction_iff_regular {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsMSOTransduction f ↔ IsRegularFun f := by
  sorry

/-! ## C.4.4 The first-order fragment -/

/-- **Theorem C.4.11.**  A language is definable in first-order logic if and
only if it is recognised by an aperiodic dfa. -/
theorem foDefinable_iff_aperiodic_dfa {A : Type} [Finite A] (L : Language A) :
    FODefinable L ↔
      ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L := by
  sorry

/-! **Definition C.4.12 (k-types)** (`TpType` and `tp`) is in
`RequestProject/PartC/KTypes.lean`, together with the proof of Lemma C.4.15
below. -/

/-- **Lemma C.4.13.**  Two strings have the same `k`-type if and only if they
satisfy the same first-order sentences of quantifier rank at most `k`. -/
theorem tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ)) := by
  sorry

/-- **Lemma C.4.15.**  Refinement, congruence and aperiodicity of `k`-types. -/
theorem tp_properties {A : Type} (k : ℕ) :
    (∀ w v : List A, tp (k + 1) w = tp (k + 1) v → tp k w = tp k v) ∧
    (∀ w w' v v' : List A, tp k w = tp k w' → tp k v = tp k v' →
      tp k (w ++ v) = tp k (w' ++ v')) ∧
    (∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)) :=
  tp_properties_aux k

/-- **Theorem C.4.16.**  A string-to-string function is a first-order
relabelling if and only if it is computed by an aperiodic bimachine. -/
theorem foRelabelling_iff_aperiodicBimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFORelabelling f ↔ IsAperiodicBimachine f := by
  sorry

/-- The family of prime first-order regular functions: first-order rational
functions (equivalently, first-order relabellings), map reverse and map
duplicate. -/
def FORegularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsFORelabelling f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

/-- **Theorem C.4.17.**  A string-to-string function is a first-order
transduction if and only if it can be obtained by composing map reverse, map
duplicate and first-order rational functions. -/
theorem foTransduction_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFOTransduction f ↔ CompClosure FORegularFam A B f := by
  sorry

end Transducers
