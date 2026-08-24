/-
Part C, Section C.4: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

This file used to hold the numbered results of Section C.4 whose proofs were
still left as `sorry`, so that `RequestProject/PartC/MSO.lean`, which collects
the results of Section C.4 that *are* proved, contains no `sorry`.

The last such result was Theorem C.4.17, which **has been removed from the
formalised theorems at the user's request**; its statement is kept below, only
as a comment, and no longer exists as a Lean declaration.  Nothing in Section
C.4 is left unproved: the file now contains no declaration at all, and is kept
only for the pointers below.
`RequestProject/PartC/MSO.lean` imports this file, so all remaining names are
unchanged and are still available to anything importing
`RequestProject.PartC.MSO`.

Theorem C.4.4, Lemma C.4.10, Theorem C.4.8, Theorem C.4.11 and Lemma C.4.13
used to be stated here as well; they are now proved, and their statements have
moved back to `RequestProject/PartC/MSO.lean`.

Not formalised as numbered results: Claim C.4.5, Lemma C.4.9 and Claim C.4.14,
which are internal steps of the proofs of Theorems C.4.4, C.4.8 and
Lemma C.4.13.
-/
import RequestProject.PartC.FOTransPrimeComp

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

/-! The family `Transducers.FORegularFam` of prime first-order regular
functions used to be defined here; it has moved to
`RequestProject/PartC/FOPrimeFam.lean`, which this file imports.  Its easy
inclusion into the first-order transductions is proved, independently of
anything below, in `RequestProject/PartC/FOTransPrimeComp.lean`
(`Transducers.isFOTransduction_of_compClosure`). -/

/-!
### Theorem C.4.17 has been removed from the formalised theorems

At the user's request, Theorem C.4.17 and its open half are no longer part of
this formalisation.  They are kept here, commented out, for the record only.
The book itself states Theorem C.4.17 without a proof (it leaves the proof for
a future edition of the notes), and the direction from first-order transductions
to compositions of primes was the only `sorry` of Section C.4.  The inclusion
that *is* proved survives untouched as
`Transducers.isFOTransduction_of_compClosure` in
`RequestProject/PartC/FOTransPrimeComp.lean`.
-/

/-
/-- **The open half of Theorem C.4.17.**  Every first-order transduction is a
composition of first-order relabellings, map reverse and map duplicate.

**Still open in this formalisation**, and the only part of Theorem C.4.17 that
is.  The book states Theorem C.4.17 without a proof (it leaves the proof for a
future edition of the notes), and sketches what this direction would need:
first-order variants of (1) the lemma saying that a string representation of the
configuration graph of a two-way transducer can be computed, and (2) the main
step in the decomposition of two-way transducers into primes, saying that the
output string can be read off the configuration graph by a composition of
primes -- the second one being, in the words of the book, more technical.  In
this project those two ingredients are the contents of the many files behind
Theorem C.4.8, and their aperiodic counterparts are not available. -/
theorem compClosure_of_isFOTransduction {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsFOTransduction f) : CompClosure FORegularFam A B f := by
  sorry
-/

/-
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
in the mso case is obtained *through* Theorem C.4.8 and so does not transfer
directly either; it is proved here by substituting formulas, in
`RequestProject/PartC/FOTransTr.lean` and
`RequestProject/PartC/FOTransComp.lean`.

**Status.**  The inclusion from right to left (compositions of primes are
first-order transductions) is proved, in
`RequestProject/PartC/FOTransPrimeComp.lean`.  The inclusion from left to right
is the still open `Transducers.compClosure_of_isFOTransduction` above. -/
theorem foTransduction_iff_prime_composition {A B : Type} [Finite A] [Finite B]
    (f : List A → List B) : IsFOTransduction f ↔ CompClosure FORegularFam A B f :=
  ⟨compClosure_of_isFOTransduction, isFOTransduction_of_compClosure⟩
-/

end Transducers
