/-
Part C, Section C.4: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

The numbered results of Section C.4 that are **not proved yet** -- by now only
Theorem C.4.17: their statements are given faithfully and their proofs are left
as `sorry`.  They were originally stated in `RequestProject/PartC/MSO.lean`;
they have been moved here, unchanged, so that
`RequestProject/PartC/MSO.lean`, which collects the results of Section C.4 that
*are* proved, contains no `sorry`.
`RequestProject/PartC/MSO.lean` imports this file, so all names are unchanged
and are still available to anything importing `RequestProject.PartC.MSO`.

Theorem C.4.4, Lemma C.4.10, Theorem C.4.8, Theorem C.4.11 and Lemma C.4.13
used to be stated here as well; they are now proved, and their statements have
moved back to `RequestProject/PartC/MSO.lean`.

Not formalised as numbered results: Claim C.4.5, Lemma C.4.9 and Claim C.4.14,
which are internal steps of the proofs of Theorems C.4.4, C.4.8 and
Lemma C.4.13.
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

/-! Theorem C.4.8 (`msoTransduction_iff_regular`) is now proved; it lives in
`RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/MSOReg.lean` (from mso transductions to regular functions)
and `RequestProject/PartC/TwoWayMSO.lean` (the converse). -/

/-! ## C.4.4 The first-order fragment -/

/-! Theorem C.4.11 (`foDefinable_iff_aperiodic_dfa`) and Lemma C.4.13
(`tp_eq_iff_fo_equiv`) are now proved; they live in
`RequestProject/PartC/MSO.lean`, with their proofs in
`RequestProject/PartC/FOComp.lean` and `RequestProject/PartC/FOHintikka.lean`
(Lemma C.4.13) and in `RequestProject/PartC/FOTypeDFA.lean` and
`RequestProject/PartC/FOMealy.lean` (Theorem C.4.11). -/

/-! Theorem C.4.16 (`foRelabelling_iff_aperiodicBimachine`) is now proved; it
lives in `RequestProject/PartC/MSO.lean`, with its proof in
`RequestProject/PartC/FORelabBimach.lean` (from first-order relabellings to
aperiodic bimachines) and `RequestProject/PartC/FOBimachRelab.lean` (the
converse). -/

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
duplicate and first-order rational functions.

**Still open in this formalisation.**  The book states this theorem without a
proof (it leaves the proof for a future edition of the notes), and sketches what
the proof would need: first-order variants of (1) the lemma saying that a string
representation of the configuration graph of a two-way transducer can be
computed, and (2) the main step in the decomposition of two-way transducers into
primes, saying that the output string can be read off the configuration graph by
a composition of primes -- the second one being, in the words of the book, more
technical.  In this project those two ingredients are the contents of the many
files behind Theorem C.4.8, and their aperiodic counterparts are not available.
The easy inclusion (from compositions of primes to first-order transductions)
additionally needs closure of first-order transductions under composition, which
in the mso case is obtained here *through* Theorem C.4.8 and so does not
transfer directly either; it would have to be proved by substituting formulas.
The statement is therefore recorded faithfully and left as `sorry`. -/
theorem foTransduction_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFOTransduction f ↔ CompClosure FORegularFam A B f := by
  sorry

end Transducers
