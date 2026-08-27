# external — COMPLETE

task: 4bdb7b3f-ff26-48fc-842b-3f8d9ee2bf5a
created: 2026-08-27 02:00:30.953207

Theorem `thm:for-transducers-are-polyregular` (`Transducers.polyregular_iff_forTransducer`, in `transducer-lean/RequestProject/PartD/Statements.lean`) is now **proved outright**, with no `sorry` anywhere in its dependencies. `#print axioms Transducers.polyregular_iff_forTransducer` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

What was done this session (the missing right-to-left inclusion, "for-transducer ⇒ polyregular"; the left-to-right one was already in place in `PartD/ForPolyreg.lean`):

* `PartD/PolyScan.lean` (new): the streaming string transducer that scans the enumeration of the tuples of positions — one annotated copy of the input per tuple — running the loop-free body of the nest once per copy and the epilogue at the end. Its state keeps the Boolean variables of the for-transducer plus the finite information about the copy being read (the letter under each variable and the order of the variables), which suffices because a loop-free program only sees that view. The file proves the run over a prefix of a copy, over a whole copy, over a copy followed by its separator, over the whole list of copies, and finally `Transducers.PolyEnum.scan_enum`: on `enum` the machine outputs exactly what the program in prenex form outputs.
* `PartD/PolyFor.lean` (new): the scan is a streaming string transducer, hence a regular function (via `Transducers.sst_iff_regular`), hence polyregular; composing it with the polyregular enumeration (`isPolyregular_enum`, from earlier work) gives `isPolyregular_of_prenex`, and Lemma `lemma:prenex-normal-form` upgrades this to `isPolyregular_of_isForTransducer` for arbitrary for-transducers.
* `PartD/PolyScanAux.lean` was completed (its remaining gaps in the ordering/consistency lemmas for the canonical copy were closed) and the `sorry` in `Statements.lean` was replaced by the two inclusions.

Status of the numbered results of Part D after this run:
* proved outright: `thm:polyregular-functions-are-continuous`, `thm:for-transducers-are-polyregular`, `lemma:prenex-normal-form`, `lem:for-closed-under-composition`;
* still open (statement only, `sorry`, untouched by this task): `thm:pebble-are-continuous` and `thm:pebble-are-for`. What remains for them is the simulation of pebble transducers by for-transducers and the continuity argument for pebble transducers.
* No result of this run is proved from an extra hypothesis; no `axiom`, no `native_decide`, no weakened statement.

Bookkeeping: `Labels.lean` now carries `assert_no_sorry` for `thm:for-transducers-are-polyregular` (and `tools/gen_labels.py --check` passes); `THEOREMS.md` was updated — the status row for the theorem, the new Part D file entries (`PolyDef`, `ForMachine`, `ForMapRev`, `ForPrimes`, `ForPolyreg`, `PolyEnum`, `PolyStep`/`PolyStepTop`, `PolyEnumPoly`, `PolyScanAux`, `PolyScan`, `PolyFor`), the `## Status` section and the audit notes. The header of `PartD/Statements.lean` was updated accordingly. A full `lake build` succeeds with no errors; the only `declaration uses sorry` warnings are the two pebble statements. All work is committed and pushed.
