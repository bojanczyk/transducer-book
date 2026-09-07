/-
The easy direction of Theorem `thm:rational-terms` of Section *Combinators* of *Transducers*
(M. Bojańczyk): every function defined by a rational term is rational under string representation.

The proof is the induction on the term that the book describes for the regular case, "while paying
attention to the atomic functions that are used".  Its basis is that every atomic function of the
theorem is rational under string representation, which is the content of `RatAtomA.lean`,
`RatAtomB.lean` and `RatAtomC.lean`; its induction step is the content of `RatComb.lean`
(composition being `Transducers.IsRationalUnderRepr.comp`, in `RatTerms.lean`).  All that is left
here is to put the cases together.
-/
import RequestProject.PartC.RatAtomB
import RequestProject.PartC.RatAtomC
import RequestProject.PartC.RatComb

namespace Transducers

open RatComb

/-- **Every rational term defines a function that is rational under string representation.**  This
is the easy direction of Theorem `thm:rational-terms`, by induction on the term. -/
theorem RatTerm.isRationalUnderRepr :
    ∀ {A B : Ty} (t : RatTerm A B), IsRationalUnderRepr t.eval
  | _, _, .id A => isRationalUnderRepr_id A
  | _, _, .fst A B => isRationalUnderRepr_fst A B
  | _, _, .snd A B => isRationalUnderRepr_snd A B
  | _, _, .inl A B => isRationalUnderRepr_inl A B
  | _, _, .inr A B => isRationalUnderRepr_inr A B
  | _, _, .codiag A => isRationalUnderRepr_codiag A
  | _, _, .appendOne A => isRationalUnderRepr_appendOne A
  | _, _, .prependOne A => isRationalUnderRepr_prependOne A
  | _, _, .distr A B C => isRationalUnderRepr_distr A B C
  | _, _, .distl A B C => isRationalUnderRepr_distl A B C
  | _, _, .cons A => isRationalUnderRepr_cons A
  | _, _, .uncons A => isRationalUnderRepr_uncons A
  | _, _, .unsnoc A => isRationalUnderRepr_unsnoc A
  | _, _, .concat A => isRationalUnderRepr_concat A
  | _, _, .split A B => isRationalUnderRepr_split A B
  | _, _, .pref G grp hfin => by
      letI := grp
      haveI := hfin
      exact isRationalUnderRepr_pref G
  | _, _, .comp s t => (RatTerm.isRationalUnderRepr s).comp (RatTerm.isRationalUnderRepr t)
  | _, _, .prodMap s t =>
      IsRationalUnderRepr.prodMap (RatTerm.isRationalUnderRepr s) (RatTerm.isRationalUnderRepr t)
  | _, _, .sumMap s t =>
      IsRationalUnderRepr.sumMap (RatTerm.isRationalUnderRepr s) (RatTerm.isRationalUnderRepr t)
  | _, _, .map t => IsRationalUnderRepr.mapList (RatTerm.isRationalUnderRepr t)

/-- **Theorem `thm:rational-terms`, the easy direction.**  Every type-to-type function that is
defined by a rational term is rational under string representation. -/
theorem ratTerm_isRational {A B : Ty} {f : A.Elt → B.Elt} (h : IsRatTermFun f) :
    IsRationalUnderRepr f := by
  obtain ⟨t, ht⟩ := h
  exact ht ▸ t.isRationalUnderRepr

end Transducers
