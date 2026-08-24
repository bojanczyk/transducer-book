# C4-transduction — COMPLETE

task: fa8e8e6d-8fa7-40bf-b832-ecc5414ddd8e
created: 2026-08-23 18:28:46.017098

Theorem C.4.8 (`Transducers.msoTransduction_iff_regular`, in `transducer-lean/RequestProject/PartC/MSO.lean`) is now formalised in both directions, and its statement is byte-identical to the one that previously carried a `sorry` in `MSOOpen.lean` (that placeholder was replaced by a pointer comment, the convention already used for C.4.4 and C.4.10).

What was added:

* `RequestProject/PartC/MSOWalkData.lean` — the product of a finite family of DFAs together with a "last letter read" component, the `WalkAut.Data` builder `walkData` with its projection lemmas, and the correctness theorem `Transducers.MSOWalk.computes_walkData`, which discharges the nine hypotheses of `WalkAut.computes_of_spec`.
* `RequestProject/PartC/MSOReg.lean` — the hard direction `Transducers.MSOReg.isRegularFun_of_isMSOTransduction`. Route: normalise the type τ (Lemma C.4.9, `MSOTransduction.exists_norm`, which was already present — it is not a numbered result, so it is kept as a plain lemma), enumerate the unary and binary questions, apply Lemma C.4.10 to precompute their answers with a rational function, build the walking transducer with `computes_walkData`, and compose the rational preprocessing with a bounded-width two-way run, which is regular by `boundedWidth_isRegular`. The case of an empty output alphabet is handled separately.
* Internal helper names in `MSOWalkForms.lean` were renamed (`tt`→`ttF`, `bigAnd`→`bigAndF`, etc.) to resolve a name clash with `MSOSyntax.lean`; no numbered statement was touched.

Status of the results:

* **Proved outright:** the direction regular ⊆ mso, `Transducers.TwoWayMSO.isMSOTransduction_of_isTwoWay` (axioms: propext, Classical.choice, Quot.sound), and the new correctness theorem `Transducers.MSOWalk.computes_walkData` (same axioms).
* **Proved from an unfinished dependency:** Theorem C.4.8 itself, and the direction mso ⊆ regular. Neither contains any `sorry`, but they invoke Theorem C.2.9, whose hard half still rests on the open snake-lemma induction step `boundedWidth_isRegular_step` in `RequestProject/PartC/SnakeReg.lean`. Accordingly `#print axioms Transducers.msoTransduction_iff_regular` reports `sorryAx` in addition to propext, Classical.choice, Quot.sound, exactly as for the already-recorded Theorem C.3.2. So C.4.8 should not yet be called proved outright; closing `boundedWidth_isRegular_step` is all that remains.
* **Still open in Section C.4:** C.4.11, C.4.13, C.4.16, C.4.17 (statements only, in `MSOOpen.lean`).

`lake build` completes with no errors (8188 jobs); the only warnings are the pre-existing `declaration uses 'sorry'` ones from the open statements in Parts B, C and D. `THEOREMS.md` has been updated (file table, the C.4.8/C.4.9 rows, a new subsection describing the proof of C.4.8, and the `## Status` paragraph), and all work is committed and pushed.
