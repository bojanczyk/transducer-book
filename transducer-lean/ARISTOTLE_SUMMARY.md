# The three exercises of Section D.3, restated for the polyregular terms

Exercise `exer:reverse-from-split`, Exercise `exer:block-from-split` and
Exercise `exer:pref-from-mult` ask, in the book, for **polyregular** terms.  They
were formalised for the *higher-order* terms of Definition
`def:higher-order-terms`, and the header of
`RequestProject/Exercises/HOAtomsFromSplit.lean` justified that by calling it
"the stronger reading ... since a polyregular term is a higher-order term".  The
implication runs the other way: every polyregular term is a higher-order term,
so asking for a higher-order term asks for *less*.  The witnesses really did use
the extra power — `HTerm.reverseTerm` has two `lam` nodes, `blockSplitTerm` one
and `prefTerm` seven, because in the higher-order syntax `map` is an atomic
function of arrow type that must be applied to a lambda.

This run restates all three for `Transducers.PolyTerm` (Definition
`def:polyregular-terms`), where `map` is a combinator and the author's solutions
transcribe without a single lambda.  The wrong sentence in the header is
corrected.  Everything is proved outright: `lake build` succeeds, the file
contains no `sorry`, no `axiom` and no `native_decide`, and `#print axioms` on
each of the three aliases of `RequestProject/Labels.lean` gives only `propext`,
`Classical.choice`, `Quot.sound`.

| exercise | Lean name | witness |
| --- | --- | --- |
| `exer:reverse-from-split` | `Transducers.Exercises.reverse_from_split` | `Transducers.Exercises.polyReverse` |
| `exer:block-from-split` | `Transducers.Exercises.block_from_split` | `Transducers.Exercises.polyBlockSplit` |
| `exer:pref-from-mult` | `Transducers.Exercises.pref_from_mult` | `Transducers.Exercises.polyPref` |

## Saying which atomic functions are avoided

There was no predicate on `Transducers.PolyTerm` for this, so three were added,
on the model of `Transducers.HAtom.Small` and `Transducers.HTerm.Small`: a
recursion over the constructors, propagated structurally through `comp`,
`prodMap`, `sumMap` and `map`.

* `Transducers.PolyTerm.NoReverse` — the atomic function `reverse` does not occur;
* `Transducers.PolyTerm.NoBlockSplit` — the block split does not occur;
* `Transducers.PolyTerm.NoPref` — group prefix multiplication does not occur.

Each statement carries the clause its exercise needs, and `block_from_split`
carries both `NoBlockSplit` and `NoReverse`, so the exclusion is visible in the
statement itself.  The auxiliary `Transducers.PolyTerm.Reduced` (none of the
three) is what the terms of the file are proved to satisfy; three lemmas extract
from it the clause each exercise needs.

## The atomic function `mult`

Exercise `exer:pref-from-mult` asks for a term that uses the product
`mult : G* → G` of a list.  Definition `def:polyregular-terms` has `pref`, not
`mult`, and without a group operation in the syntax there is nothing to build
`pref` from, so the exercise cannot be stated inside `Transducers.PolyTerm`
alone.  Rather than change a numbered definition, the exercise is stated for
`Transducers.PolyMultTerm`: terms built from the polyregular terms and from
`mult` by composition and the three functoriality combinators — exactly "the
polyregular terms with one more atomic function", since the polyregular terms
are themselves closed under those combinators.  `PolyMultTerm.NoPref` is the
clause that says `pref` is not used.  The deviation is recorded in the file
header, in `EXERCISES.md` and in `THEOREMS.md`.

## The terms

They follow the author's solutions and reuse the combinatorial identities of
`RequestProject/PartD/HOFewerAux.lean` unchanged —
`Transducers.flatten_headAsList_splits`, `Transducers.twiFun_eq`,
`Transducers.bsFun_eq` and `Transducers.prefFun_eq`.  `polyReverse` is `splits`,
then `snd*`, then `headAsList*`, then `concat`; `polyBlockSplit` pairs `polyTwi`
with `polyBs`, each of which runs over the cuts in the reversed order that
`polyReverse` produces; `polyPref` collects the product of every non-empty
prefix.  The auxiliary terms — `polyBang` (the unique function `A → 1`, by
induction on the type), `polyNil`, `polyPure`, `polySwap`, `polyHeadAsList`,
`polyInrPart`, `polyHeadInl` — are all `Reduced`.

## What is kept

The higher-order statements are kept, under the names
`reverse_from_split_higherOrder`, `block_from_split_higherOrder` and
`pref_from_mult_higherOrder`, and the file header says what each group is for:
the higher-order ones are what the proof of Lemma `lem:fewer-atomic` in
`RequestProject/PartD/HOFewer.lean` appeals to, and that file and
`RequestProject/PartD/HOFewerAux.lean` are untouched; the polyregular ones are
the formalisation of the exercises.

## Checks

`lake build` succeeds with no errors, and `tools/decl_files.py --check` passes.
`tools/gen_labels.py --check` and `tools/tex_numbering.py --check LABELS.md`
report only the failures that were already there before this run — one fewer,
in fact (25 instead of 26).  They come from the copy of the book in this
checkout being older than the author's: `main.aux` has no `\newlabel` for
`ex:block`, `ex:marked-squaring-for-transducer`,
`claim:atomic-functions-are-natural-transformations` or
`claim:functors-applied-to-good`, and its numbers are stale for 49 rows of
`LABELS.md`.  `tools/print_axioms.sh` reports that all 282 aliases depend only
on `propext`, `Classical.choice`, `Quot.sound`.
