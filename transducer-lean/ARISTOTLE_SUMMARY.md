# Six results of the book that were still unformalised

A review of the whole book found six results with no formalisation.  All six are
now proved, `lake build` succeeds, and `tools/gen_labels.py --check`,
`tools/decl_files.py --check` and `tools/tex_numbering.py --check LABELS.md`
pass.  None of the new files contains a `sorry`, an `axiom` or a
`native_decide`, no statement takes a `Prop`-valued assumption, and
`tools/print_axioms.sh` reports that all 292 aliases of
`RequestProject/Labels.lean` — the seven new ones included — depend only on
`propext`, `Classical.choice`, `Quot.sound`.

| result | Lean | file |
| --- | --- | --- |
| Claim `claim:parsing-is-regular` | `Transducers.reprLang_isRegular` | `RequestProject/PartC/CombParse.lean` (new) |
| Exercise `exer:filter-plus` | `Transducers.Exercises.regTerm_filter_plus` | `RequestProject/Exercises/CombinatorsEx.lean` |
| Exercise `exer:split-triple` | `Transducers.Exercises.split_triple` | `RequestProject/Exercises/SplitTriple.lean` (new) |
| Claim `claim:factorial-powers-stabilise-in-monoids` | `Transducers.Exercises.factorial_powers_stabilise` | `RequestProject/Exercises/Intro.lean` |
| Claim `lem:fo-non-elementary-order` | `Transducers.Exercises.fo_non_elementary_order` | `RequestProject/Exercises/FONonElemClaim.lean` (new) |
| Claim `claim:grammar-compression-of-baib` | `Transducers.Exercises.gaps_finite_of_generates`, `Transducers.Exercises.ncard_gaps_le_of_generates` | `RequestProject/Exercises/Compression.lean` |

## Notes

* **`claim:parsing-is-regular`** was recorded in `THEOREMS.md` as *not
  formalised*, under the placeholder tag
  `nolabel:claim-representations-are-a-regular-language`, because it carried no
  `\label`.  The author has labelled it, so the dictionary of `LABELS.md` now
  uses the real label and the claim is proved, by the book's induction on the
  type: the language `Transducers.reprLang` of the representations is described
  by a regular expression built from the languages of the components, and the
  closure of the regular languages under concatenation, union and the Kleene
  star (`RequestProject/Common/RegLangClosure.lean`) finishes it.  The rest of
  Section *Combinators* is untouched: it parses a representation with the
  bracket counter of `PartC/CombDepth.lean` and does not use this claim.

* **`lem:fo-non-elementary-order`** and **`claim:grammar-compression-of-baib`**
  were already proved in substance by the files that formalise the exercises
  they belong to; what was missing in each case was the statement the book
  makes.  For the first, `Transducers.Exercises.phiOrd` has six free position
  variables, the last two of which select between *same index* and *consecutive
  index*, because the induction needs both; the new
  `Transducers.Exercises.phiOrdSucc` quantifies those two away in the mode
  *consecutive* and so has the four free variables `x₁, x₂, y₁, y₂` of the book,
  with the same linear size.  For the second, the bound on the set of distances
  between consecutive marked letters is read off the machinery already in
  `Exercises/Compression.lean`.

* **`claim:factorial-powers-stabilise-in-monoids`** is not in Mathlib — Mathlib
  has the powers of an idempotent element and the order of an element of a
  finite group, but nothing giving the eventual periodicity of the powers of an
  element of a finite monoid — so it is proved here, from the stabilisation of
  the iterates of a self-map of a finite set
  (`Transducers.Exercises.iterate_stable_single`) applied to left multiplication
  by `m`.

* **The two exercises** are the author's own solutions transcribed: `map` of the
  function `L a ↦ [a]`, `R b ↦ []` followed by `concat` for `exer:filter-plus`;
  the atomic function `split`, a term applied to every cut, `concat` and a final
  `reverse` for `exer:split-triple`.

## Reading conventions fixed here

* `exer:split-triple` writes its codomain `(A* × A × A*)*` without bracketing
  the product; it is read as `A* × (A × A*)`.
* `lem:fo-non-elementary-order` reads an infix half-open, as `(x₁, x₂]`, and
  renders "consecutive in the lexicographic order" as "with consecutive
  indices" — both as in the existing development of `exer:fo-non-elementary` —
  and carries that hypothesis of `Transducers.Exercises.sat_phiOrd` that the
  string has at least two positions, which is what makes the two quantified
  mode positions available.
