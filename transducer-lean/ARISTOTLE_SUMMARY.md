# Section *Combinators* is complete: the converse of Theorem `thm:regular-terms`

The converse direction of Theorem `thm:regular-terms` -- every function that is
regular under string representation is defined by a regular term -- is now
proved, and the theorem is stated as the equivalence it is in the book:

```
theorem Transducers.regular_iff_regularTerm {A B : Ty} (f : A.Elt → B.Elt) :
    IsRegularUnderRepr f ↔ IsRegularTermFun f
```

`Transducers.Book.«thm:regular-terms»` is its alias, and `#print axioms` on it
reports `propext`, `Classical.choice`, `Quot.sound`.  The two directions are
`Transducers.regularTerm_isRegular` (`«thm:regular-terms#2»`, proved by an
earlier run) and `Transducers.regularTerm_of_isRegular`
(`«thm:regular-terms#3»`).

With it, the ten numbered results of Section *Combinators* that the converse
goes through are proved outright, each with the same three axioms:
Lemma `lem:terms-define-string-homomorphisms`, Claim
`claim:finite-type-bijection-disjoint-units`, Claim
`claim:finite-domain-regular-list-function`, Lemma
`lem:terms-define-append-hash`, Claim `claim:bang-definable`, Lemma
`lem:terms-define-map-reverse-duplicate` (map reverse and map duplicate), Lemma
`lem:terms-define-flip-flop`, Lemma `lem:terms-define-reversible`, Lemma
`lem:terms-define-string-representation` and Claim `claim:head`.  No result
takes a hypothesis, and the project declares no `axiom`.

## The route

`Transducers.IsRegularFun` is by definition the closure of
`Transducers.RegularFam` under composition, and the functions definable by terms
are closed under composition, so the converse reduces to covering the primes.

* `PartC/CombFinite.lean` -- a function whose domain is a finite type is
  definable (Claim `claim:finite-domain-regular-list-function`), hence so is a
  string homomorphism (Lemma `lem:terms-define-string-homomorphisms`).
* `PartC/CombDerived.lean` -- the derived combinators the book uses without
  comment, the finite case distinction `Transducers.tfun_finCases`, and the
  three claims that are about terms alone.
* `PartC/CombStrFam.lean` -- `Transducers.TermStrFun`, the interface between the
  primes (functions `A* → B*` for arbitrary finite alphabets) and the terms
  (which speak about the elements of a `Ty`), together with Lemma
  `lem:terms-define-append-hash`.
* `PartC/CombMealyFF.lean`, `PartC/CombMealyRev.lean` -- the two Mealy primes,
  which with Theorem `thm:rational-primes` (and behind it Theorem
  `thm:2dfa-decomposition-into-primes` and Theorem `thm:krohn-rhodes`) give all
  the rational primes.
* `PartC/CombMapRev.lean` -- map reverse and map duplicate, both instances of
  the map lifting of a term-definable function.
* `PartC/CombComplete.lean` -- every regular string-to-string function is
  definable by terms.
* `PartC/CombRepr.lean` -- Lemma `lem:terms-define-string-representation` and,
  from it, the converse.

## Divergences from the book

Three, all of them in the *route* and none in a statement; they are recorded
under *Divergences from the book* in `THEOREMS.md` and in the docstrings.

* Claim `claim:finite-type-bijection-disjoint-units` is deduced *from* Claim
  `claim:finite-domain-regular-list-function`, the reverse of the book's order.
  Both are proved.
* In Lemma `lem:terms-define-reversible` the input alphabet `A` is embedded in
  `Equiv.Perm (Option A)` by `a ↦ Equiv.swap none (some a)` instead of carrying
  the book's arbitrary cyclic group structure on `A`.
* In the product case of Lemma `lem:terms-define-string-representation` the
  functions that implement the projections under string representation, from the
  easy direction, replace the book's marking machine.  Claim `claim:head` is
  proved all the same, it is simply not needed on this route.

## Verification

`lake build` succeeds with no errors.  No declaration of the project uses
`sorry`, `axiom` or `native_decide` -- the only occurrences of `sorry` are
inside the commented-out records of statements that were withdrawn or corrected,
which elaborate nothing -- `python3 tools/gen_labels.py --check` agrees with
`LABELS.md` and the index tables, and the counts in `THEOREMS.md` were
recomputed: of the 115 environments of the dictionary, 23 definitions and 89
results are formalised, none from a hypothesis, and 3 environments are not
formalised (Definition `def:rational-recognisable-subsets`, Claim
`nolabel:claim-representations-are-a-regular-language`, and the withdrawn
unnumbered paragraph `nolabel:thm-fo-transduction-into-primes`).
