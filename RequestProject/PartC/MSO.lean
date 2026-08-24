/-
Part C, Section C.4: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

The numbered results of Section C.4 that are proved: Theorem C.4.1,
Lemma C.4.2, Theorem C.4.4, Claim C.4.6, Theorem C.4.8, Lemma C.4.10,
Theorem C.4.11, Lemma C.4.13, Lemma C.4.15 and Theorem C.4.16.  Every
proof in this file is complete.

The definitions they speak about (monadic second-order logic, mso relabellings,
mso transductions and the first-order fragment) are in
`RequestProject/PartC/MSODef.lean`, the constructions used in their proofs in
`RequestProject/PartC/MSOSyntax.lean`, `RequestProject/PartC/RegAut.lean`,
`RequestProject/PartC/MSOAnnot.lean`, `RequestProject/PartC/MSOBuchi.lean`,
`RequestProject/PartC/MSORelab.lean`, `RequestProject/PartC/KTypes.lean`,
`RequestProject/PartC/MarkStr.lean`, `RequestProject/PartC/MarkLogic.lean`,
`RequestProject/PartC/MarkBimach.lean`, `RequestProject/PartC/MarkDelay.lean`,
`RequestProject/PartC/MSORatRelab.lean` and
`RequestProject/PartC/MSOPrecomp.lean`.

Theorem C.4.11 and Lemma C.4.13 are proved below, out of
`RequestProject/PartC/FORel.lean`, `RequestProject/PartC/FOSeg.lean`,
`RequestProject/PartC/FOComp.lean`, `RequestProject/PartC/FORename.lean`,
`RequestProject/PartC/FOHintikka.lean`, `RequestProject/PartC/FOTypeDFA.lean`,
`RequestProject/PartC/FOSubstRel.lean`, `RequestProject/PartC/FOFlipFlop.lean`
and `RequestProject/PartC/FOMealy.lean`.

Theorem C.4.16 is proved below, out of `RequestProject/PartC/FORev.lean`,
`RequestProject/PartC/FOPos.lean`, `RequestProject/PartC/FORelabBimach.lean`
(first-order relabellings are computed by aperiodic bimachines) and
`RequestProject/PartC/FOBimachRelab.lean` (the converse).

The only numbered result of Section C.4 that is still open (Theorem C.4.17) is
stated in `RequestProject/PartC/MSOOpen.lean`, which this file imports; so
importing `RequestProject.PartC.MSO` gives, as before, all the statements of
Section C.4.

Not formalised: Claim C.4.5, Lemma C.4.9 and Claim C.4.14, which are internal
steps of the proofs of Theorems C.4.4, C.4.8 and C.4.11.
-/
import RequestProject.PartC.MSOBuchi
import RequestProject.PartC.MSORelab
import RequestProject.PartC.MSOOpen
import RequestProject.PartC.MSORatRelab
import RequestProject.PartC.MSOPrecomp
import RequestProject.PartC.MSOReg
import RequestProject.PartC.FOHintikka
import RequestProject.PartC.FOTypeDFA
import RequestProject.PartC.FOMealy
import RequestProject.PartC.FORelabBimach
import RequestProject.PartC.FOBimachRelab

namespace Transducers

/-! ## C.4.1 Monadic second-order logic -/

/-- **Theorem C.4.1.**  A language is regular if and only if it is definable in
monadic second-order logic. -/
theorem regular_iff_msoDefinable {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L :=
  regular_iff_msoDefinable_aux L

/-- **Lemma C.4.2.**  For an mso formula whose free variables are among
`x₁, …, x_k, X₁, …, X_l`, the set of annotated strings that satisfy it is a
regular language over the alphabet `A × 2^{k+l}`. -/
theorem mso_annotated_regular {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} :=
  mso_annotated_regular_aux φ k l hfo hso

/-! ## C.4.2 Rational functions in terms of logic -/

/-- **Theorem C.4.4.**  A string-to-string function is rational if and only if
it is definable by an mso relabelling. -/
theorem rational_iff_msoRelabelling {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsRationalFun f ↔ IsMSORelabelling f :=
  rational_iff_msoRelabelling_aux f

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
          ((f w).drop x).take (y - x + 1) ∈ L)) :=
  mso_formulas_via_rational_aux Φ₁ Φ₂ hΦ₁ hΦ₂

/-! ## C.4.3 Regular functions in terms of logic -/

/-- **Theorem C.4.8.**  String-to-string mso transductions define exactly the
regular functions. -/
theorem msoTransduction_iff_regular {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsMSOTransduction f ↔ IsRegularFun f :=
  ⟨fun h => isRegularFun_of_isMSOTransduction h,
    fun h => isMSOTransduction_of_isTwoWay (regularFun_isTwoWay h)⟩

/-- **Claim C.4.6.**  For an mso relabelling, the language of strings over the
alphabet `A × Φ` in which every position is labelled by a formula that holds in
that position is regular. -/
theorem msoRelabelling_annotation_regular {A B : Type} [Finite A] (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)} :=
  msoRelabelling_annotation_regular_aux R

/-! ## C.4.4 The first-order fragment

**Definition C.4.12 (k-types)** (`TpType` and `tp`) is in
`RequestProject/PartC/KTypes.lean`, together with the proof of Lemma C.4.15
below. -/

/-- **Theorem C.4.11.**  A language is definable in first-order logic if and
only if it is recognised by an aperiodic dfa. -/
theorem foDefinable_iff_aperiodic_dfa {A : Type} [Finite A] (L : Language A) :
    FODefinable L ↔
      ∃ (σ : Type) (_ : Finite σ) (M : DFA A σ), TransAperiodic M.step ∧ M.accepts = L := by
  refine ⟨aperiodic_dfa_of_foDefinable L, ?_⟩
  rintro ⟨σ, hσ, M, hap, rfl⟩
  haveI := hσ
  exact foDefinable_of_aperiodic_dfa M hap

/-- **Lemma C.4.13.**  Two strings have the same `k`-type if and only if they
satisfy the same first-order sentences of quantifier rank at most `k`. -/
theorem tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ)) := by
  constructor
  · intro h φ hfo hfree hq
    constructor
    · intro hw fo so
      exact (sat_iff_of_tp_eq h φ hfo hq hfree (fun _ => 0) fo (fun _ => ∅) so).mp
        (hw (fun _ => 0) (fun _ => ∅))
    · intro hv fo so
      exact (sat_iff_of_tp_eq h.symm φ hfo hq hfree (fun _ => 0) fo (fun _ => ∅) so).mp
        (hv (fun _ => 0) (fun _ => ∅))
  · intro h
    refine tp_eq_of_fo_equiv k w v (fun φ hfo hfree hq => ?_)
    have hw : (∀ fo so, MSO.Sat w fo so φ) ↔ MSO.Sat w (fun _ => 0) (fun _ => ∅) φ :=
      ⟨fun hs => hs _ _, fun hs fo so => (MSO.sat_sentence_congr hfo hfree w _ _ _ _).mp hs⟩
    have hv : (∀ fo so, MSO.Sat v fo so φ) ↔ MSO.Sat v (fun _ => 0) (fun _ => ∅) φ :=
      ⟨fun hs => hs _ _, fun hs fo so => (MSO.sat_sentence_congr hfo hfree v _ _ _ _).mp hs⟩
    exact hw.symm.trans ((h φ hfo hfree hq).trans hv)

/-- **Theorem C.4.16.**  A string-to-string function is a first-order
relabelling if and only if it is computed by an aperiodic bimachine. -/
theorem foRelabelling_iff_aperiodicBimachine {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFORelabelling f ↔ IsAperiodicBimachine f :=
  ⟨isAperiodicBimachine_of_isFORelabelling, isFORelabelling_of_isAperiodicBimachine⟩

/-- **Lemma C.4.15.**  Refinement, congruence and aperiodicity of `k`-types. -/
theorem tp_properties {A : Type} (k : ℕ) :
    (∀ w v : List A, tp (k + 1) w = tp (k + 1) v → tp k w = tp k v) ∧
    (∀ w w' v v' : List A, tp k w = tp k w' → tp k v = tp k v' →
      tp k (w ++ v) = tp k (w' ++ v')) ∧
    (∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)) :=
  tp_properties_aux k

end Transducers
