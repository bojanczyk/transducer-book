/-
Part C, Section C.4: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

The numbered results of Section C.4 that are **not proved yet**: their
statements are given faithfully and their proofs are left as `sorry`.  They
were originally stated in `RequestProject/PartC/MSO.lean`; they have been moved
here, unchanged, so that `RequestProject/PartC/MSO.lean`, which collects the
results of Section C.4 that *are* proved, contains no `sorry`.
`RequestProject/PartC/MSO.lean` imports this file, so all names are unchanged
and are still available to anything importing `RequestProject.PartC.MSO`.

Theorem C.4.4 and Lemma C.4.10 used to be stated here as well; they are now
proved, and their statements have moved back to `RequestProject/PartC/MSO.lean`.

Not formalised at all: Claim C.4.5, Lemma C.4.9 and Claim C.4.14, which are
internal steps of the proofs of Theorems C.4.4, C.4.8 and C.4.11.
-/
import RequestProject.PartC.MSODef

namespace Transducers

/-! ## C.4.2 Rational functions in terms of logic -/

/-! Theorem C.4.4 (`rational_iff_msoRelabelling`) is now proved; it lives in
`RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/MSORatRelab.lean`. -/

/-! Lemma C.4.10 (`mso_formulas_via_rational`) is now proved; it lives in
`RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/MSOPrecomp.lean`. -/

/-! ## C.4.3 Regular functions in terms of logic -/

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

/-- **Lemma C.4.13.**  Two strings have the same `k`-type if and only if they
satisfy the same first-order sentences of quantifier rank at most `k`. -/
theorem tp_eq_iff_fo_equiv {A : Type} [Finite A] (k : ℕ) (w v : List A) :
    tp k w = tp k v ↔
      ∀ φ : MSO A, φ.IsFO → φ.freeFO = ∅ → φ.qrank ≤ k →
        ((∀ fo so, MSO.Sat w fo so φ) ↔ (∀ fo so, MSO.Sat v fo so φ)) := by
  sorry

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
