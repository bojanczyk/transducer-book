/-
Part D: every polyregular term defines a function that is polyregular under string representation.

This is the easy direction of Theorem `thm:polyregular-terms`, and it is the induction on the term
that the book describes: the old atomic functions are regular, hence polyregular
(`RequestProject/PartC/CombStatements.lean` and
`Transducers.IsRegularUnderRepr.isPolyregularUnderRepr`); the combinators preserve polyregularity
(`RequestProject/PartD/PolyRepr.lean`); and the new atomic function is polyregular
(`RequestProject/PartD/PolySplitsAtom.lean`).
-/
import RequestProject.PartD.PolySplitsAtom

namespace Transducers

open Comb

/-- **The diagonal is polyregular under string representation.** -/
theorem isPolyregularUnderRepr_diag (A : Ty) :
    IsPolyregularUnderRepr (A := A) (B := Ty.prod A A) (fun a => (a, a)) :=
  (isRegularUnderRepr_diag A).isPolyregularUnderRepr

/-- **Every polyregular term defines a function that is polyregular under string
representation.** -/
theorem PolyTerm.isPolyregularUnderRepr :
    ∀ {A B : Ty} (t : PolyTerm A B), IsPolyregularUnderRepr t.eval
  | _, _, .id A => (isRegularUnderRepr_id A).isPolyregularUnderRepr
  | _, _, .fst A B => (isRegularUnderRepr_fst A B).isPolyregularUnderRepr
  | _, _, .snd A B => (isRegularUnderRepr_snd A B).isPolyregularUnderRepr
  | _, _, .inl A B => (isRegularUnderRepr_inl A B).isPolyregularUnderRepr
  | _, _, .inr A B => (isRegularUnderRepr_inr A B).isPolyregularUnderRepr
  | _, _, .diag A => (isRegularUnderRepr_diag A).isPolyregularUnderRepr
  | _, _, .codiag A => (isRegularUnderRepr_codiag A).isPolyregularUnderRepr
  | _, _, .distr A B C => (isRegularUnderRepr_distr A B C).isPolyregularUnderRepr
  | _, _, .cons A => (isRegularUnderRepr_cons A).isPolyregularUnderRepr
  | _, _, .uncons A => (isRegularUnderRepr_uncons A).isPolyregularUnderRepr
  | _, _, .reverse A => (isRegularUnderRepr_reverse A).isPolyregularUnderRepr
  | _, _, .concat A => (isRegularUnderRepr_concat A).isPolyregularUnderRepr
  | _, _, .split A B => (isRegularUnderRepr_split A B).isPolyregularUnderRepr
  | _, _, .pref G grp hfin => by
      letI := grp
      haveI := hfin
      exact (isRegularUnderRepr_pref G).isPolyregularUnderRepr
  | _, _, .splits A => isPolyregularUnderRepr_splits A
  | _, _, .comp s t =>
      (PolyTerm.isPolyregularUnderRepr s).comp (PolyTerm.isPolyregularUnderRepr t)
  | _, _, .prodMap s t =>
      IsPolyregularUnderRepr.prodMap (PolyTerm.isPolyregularUnderRepr s)
        (PolyTerm.isPolyregularUnderRepr t)
  | _, _, .sumMap s t =>
      IsPolyregularUnderRepr.sumMap (PolyTerm.isPolyregularUnderRepr s)
        (PolyTerm.isPolyregularUnderRepr t)
  | _, _, .map t => IsPolyregularUnderRepr.mapList (PolyTerm.isPolyregularUnderRepr t)

/-- **Theorem `thm:polyregular-terms`, the easy direction.**  Every type-to-type function that is
defined by a polyregular term is polyregular under string representation. -/
theorem polyregularTerm_isPolyregular {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsPolyregularTermFun f) : IsPolyregularUnderRepr f := by
  obtain ⟨t, ht⟩ := h
  exact ht ▸ t.isPolyregularUnderRepr

end Transducers
