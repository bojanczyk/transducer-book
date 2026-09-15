/-
The three exercises of Section *A functional programming language* (`higher-order.tex`).

Lemma `lem:fewer-atomic` drops eight of the atomic functions of Definition `def:higher-order-terms`
and keeps ten: the two projections, the two co-projections, `uncons`, `concat`, `split`, `mult`,
`map` and `either`.  For five of the eight the book displays the defining term; the remaining three
are the exercises formalised here, each of which says that one dropped atomic function is definable
from the ten that remain:

* Exercise `exer:reverse-from-split` -- `reverse`, by running over the cuts that `split` produces
  and keeping the first entry of every suffix;
* Exercise `exer:block-from-split` -- the block split of Example `ex:block`, without `reverse`;
* Exercise `exer:pref-from-mult` -- group prefix multiplication, from the product `mult` of a list.

The terms are the ones of `RequestProject/PartD/HOFewer.lean`, where they are used to prove Lemma
`lem:fewer-atomic`; the statements below are the existential form of each exercise, and their
`Transducers.HTerm.Small` clause is exactly the requirement that the dropped atomic function -- and,
for the block split, `reverse` as well -- is not used.

The book phrases the three exercises for *polyregular* terms, and the formalisation states them for
the higher-order terms with the reduced set of atomic functions of Lemma `lem:fewer-atomic`: that is
the setting in which the book itself appeals to them, in the proof of that lemma, and it is the
stronger reading of the first two, since a polyregular term is a higher-order term.
-/
import RequestProject.PartD.HOFewer

namespace Transducers
namespace Exercises

/-- **Exercise `exer:reverse-from-split`.**  The atomic function `reverse` is defined by a closed
term that does not use it: the term runs over the cuts of the input list that `split` produces and
keeps the first entry of every suffix. -/
theorem reverse_from_split (A : HTy) :
    ∃ t : HTerm [] (.arrow (.list A) (.list A)), t.Small ∧
      ∀ l : List A.Sem, t.eval .nil l = l.reverse :=
  ⟨HTerm.reverseTerm [] A, HAtom.smallImpl_small (.reverse A) [],
    fun l => congrFun (HTerm.reverseTerm_eval (Γ := []) (A := A) .nil) l⟩

/-- **Exercise `exer:block-from-split`.**  The block split of Example `ex:block` is defined by a
closed term that uses neither it nor `reverse`. -/
theorem block_from_split (A B : HTy) :
    ∃ t : HTerm [] (.arrow (.list (.sum A B))
      (.prod (.list A) (.list (.prod B (.list A))))), t.Small ∧
        ∀ l : List (A.Sem ⊕ B.Sem), t.eval .nil l = splitList l :=
  ⟨HTerm.blockSplitTerm [] A B, HAtom.smallImpl_small (.blockSplit A B) [],
    fun l => congrFun (HTerm.blockSplitTerm_eval (Γ := []) (A := A) (B := B) .nil) l⟩

/-- **Exercise `exer:pref-from-mult`.**  Group prefix multiplication is defined by a closed term
that does not use it, but uses the product `mult` of a list: the expressive power of the terms does
not change when the one atomic function is replaced by the other. -/
theorem pref_from_mult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    ∃ t : HTerm [] (.arrow (.list (HTy.ofTy G)) (.list (HTy.ofTy G))), t.Small ∧
      ∀ l : List (HTy.ofTy G).Sem, t.eval .nil l = groupPrefixProd G grp l :=
  ⟨HTerm.prefTerm [] G grp hfin, HAtom.smallImpl_small (.pref G grp hfin) [],
    fun l => congrFun (HTerm.prefTerm_eval (Γ := []) (G := G) (grp := grp) (hfin := hfin) .nil) l⟩

end Exercises
end Transducers
