/- Part B: the rational and the recognisable subsets of a monoid (Section *Rational relations*)
  from *Transducers* (M. Bojańczyk).

This file contains Definition `def:rational-recognisable-subsets` only.  The definition is made in
the book to explain the name *rational*, in the remark that precedes the Kleene Theorem, and
nothing else in the book uses it; accordingly nothing is proved about the two notions here, and no
file of the project depends on this one except the index `RequestProject/PartB.lean`. -/
import Mathlib

namespace Transducers

open Pointwise

/-! ## Rational and recognisable subsets of a monoid

Definition `def:rational-recognisable-subsets` of the book identifies, in an arbitrary monoid `M`,
two candidate notions of a "regular" subset: the recognisable subsets, defined through a
Myhill--Nerode style congruence of finite index, and the rational subsets, defined through regular
expressions.  In the free monoid `A*` the two coincide (the Kleene Theorem), and in `A* × B*` they
do not; neither of these facts is formalised here, the second one being formalised for `A* × B*`
only, as Exercise `ex:recognisable-relations` (see `EXERCISES.md`).

Mathlib has neither notion for a general monoid, but it has the ingredients of both: a congruence
of a monoid is a `Con`, that is, an equivalence relation `c` on `M` satisfying exactly the
implication displayed in the book,

  `m₁ ∼ m₁' → m₂ ∼ m₂' → m₁ * m₂ ∼ m₁' * m₂'`,

its index is the cardinality of the quotient `c.Quotient`, and the pointwise product `L * K` and
the pointwise power `L ^ n` of subsets of a monoid are `Set.mul` and `Set.pow` of the `Pointwise`
scope. -/

/-- **Definition `def:rational-recognisable-subsets`** (the recognisable subsets of a monoid).  A
subset `L` of a monoid `M` is *recognisable* if it is a union of finitely many equivalence classes
of some congruence of `M` of finite index.

A congruence is rendered by Mathlib's `Con M`, which is an equivalence relation on `M` closed under
multiplication in both arguments, as in the book; `Finite c.Quotient` says that it has finite
index, and `S` is the set of classes whose union is `L`.  The hypothesis `S.Finite` is the book's
"finitely many", and it is of course implied by `Finite c.Quotient`; it is kept so that the
definition reads as the book's does. -/
def IsRecognisableSubset {M : Type*} [Monoid M] (L : Set M) : Prop :=
  ∃ c : Con M, Finite c.Quotient ∧ ∃ S : Set c.Quotient, S.Finite ∧ L = ⇑c.mk' ⁻¹' S

/-- **Definition `def:rational-recognisable-subsets`** (the rational subsets of a monoid).  A
subset `L` of a monoid `M` is *rational* if it can be obtained from the finite subsets of `M` by
applying finitely many times the operations of union, product and Kleene star

  `L* = ⋃ₙ Lⁿ`,

where the product and the powers are pointwise.  "Finitely many times" is rendered, as usual, by
making the predicate an inductive one: its proofs are exactly the finite derivations of `L` from
the finite subsets by the three operations. -/
inductive IsRationalSubset {M : Type*} [Monoid M] : Set M → Prop
  /-- Every finite subset is rational. -/
  | of_finite {L : Set M} (hL : L.Finite) : IsRationalSubset L
  /-- The rational subsets are closed under union. -/
  | union {L K : Set M} (hL : IsRationalSubset L) (hK : IsRationalSubset K) :
      IsRationalSubset (L ∪ K)
  /-- The rational subsets are closed under pointwise product. -/
  | mul {L K : Set M} (hL : IsRationalSubset L) (hK : IsRationalSubset K) :
      IsRationalSubset (L * K)
  /-- The rational subsets are closed under Kleene star. -/
  | star {L : Set M} (hL : IsRationalSubset L) : IsRationalSubset (⋃ n : ℕ, L ^ n)

end Transducers
