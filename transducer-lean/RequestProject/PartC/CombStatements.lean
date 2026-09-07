/-
The easy direction of Theorem `thm:regular-terms` of Section *Combinators* of *Transducers*
(M. Bojańczyk).

Theorem `thm:regular-terms` says that a type-to-type function is regular under string
representation *if and only if* it is defined by some regular term.  This file proves the
implication

    defined by a regular term  ⟹  regular under string representation,

which is `Transducers.regularTerm_isRegular`.  The converse -- expressive completeness of the
terms -- is not proved here, and is *not* assumed anywhere either: no statement of this
development takes it as a hypothesis, so the theorem below is unconditional.  It is for that
reason that the equivalence itself is not stated: a biconditional whose second half rested on an
assumption would be worth less than the half that is proved.

The proof is the induction on the term that the book describes.  Its basis is that every atomic
term is regular under string representation, which is the content of `CombAtomProj.lean`,
`CombAtomDistr.lean`, `CombAtomCons.lean`, `CombAtomConcat.lean`, `CombAtomSplit.lean`,
`CombAtomReverse.lean` and `CombAtomPref.lean`; its induction step is the content of
`CombCombinators.lean` (composition being `Transducers.IsRegularUnderRepr.comp`, in
`CombTypes.lean`).  All that is left here is to put the cases together.
-/
import RequestProject.PartC.CombAtomProj
import RequestProject.PartC.CombAtomDistr
import RequestProject.PartC.CombAtomCons
import RequestProject.PartC.CombAtomConcat
import RequestProject.PartC.CombAtomSplit
import RequestProject.PartC.CombAtomReverse
import RequestProject.PartC.CombAtomPref
import RequestProject.PartC.CombCombinators

namespace Transducers

open Comb

/-! ## The diagonal, the co-diagonal and the two functoriality combinators

The atomic terms `diag` and `codiag` and the combinators `f × g` and `f + g` of Definition
`def:regular-terms` are put together here, out of the pairing and co-pairing of
`CombCombinators.lean` and the projections and co-projections of `CombAtomProj.lean`, because this
is the first file that has all of them in scope. -/

/-- **The diagonal is regular under string representation.** -/
theorem isRegularUnderRepr_diag (A : Ty) :
    IsRegularUnderRepr (A := A) (B := Ty.prod A A) (fun a => (a, a)) :=
  IsRegularUnderRepr.pair (isRegularUnderRepr_id A) (isRegularUnderRepr_id A)

/-- **The co-diagonal is regular under string representation.** -/
theorem isRegularUnderRepr_codiag (A : Ty) :
    IsRegularUnderRepr (A := Ty.sum A A) (B := A) (fun x => Sum.elim (fun a => a) (fun a => a) x) :=
  (IsRegularUnderRepr.copair (isRegularUnderRepr_id A)
    (isRegularUnderRepr_id A)).congr (fun x => by cases x <;> rfl)

/-- **The functoriality combinator `f₁ × f₂` preserves regularity under string
representation.** -/
theorem IsRegularUnderRepr.prodMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsRegularUnderRepr f) (hg : IsRegularUnderRepr g) :
    IsRegularUnderRepr (A := Ty.prod A₁ A₂) (B := Ty.prod B₁ B₂) (fun p => (f p.1, g p.2)) :=
  IsRegularUnderRepr.pair ((isRegularUnderRepr_fst A₁ A₂).comp hf)
    ((isRegularUnderRepr_snd A₁ A₂).comp hg)

/-- **The functoriality combinator `f₁ + f₂` preserves regularity under string
representation.** -/
theorem IsRegularUnderRepr.sumMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsRegularUnderRepr f) (hg : IsRegularUnderRepr g) :
    IsRegularUnderRepr (A := Ty.sum A₁ A₂) (B := Ty.sum B₁ B₂) (fun x => Sum.map f g x) :=
  (IsRegularUnderRepr.copair (hf.comp (isRegularUnderRepr_inl B₁ B₂))
    (hg.comp (isRegularUnderRepr_inr B₁ B₂))).congr (fun x => by cases x <;> rfl)

/-- **Every regular term defines a function that is regular under string representation.**  This
is the easy direction of Theorem `thm:regular-terms`, by induction on the term. -/
theorem RegTerm.isRegularUnderRepr :
    ∀ {A B : Ty} (t : RegTerm A B), IsRegularUnderRepr t.eval
  | _, _, .id A => isRegularUnderRepr_id A
  | _, _, .fst A B => isRegularUnderRepr_fst A B
  | _, _, .snd A B => isRegularUnderRepr_snd A B
  | _, _, .inl A B => isRegularUnderRepr_inl A B
  | _, _, .inr A B => isRegularUnderRepr_inr A B
  | _, _, .diag A => isRegularUnderRepr_diag A
  | _, _, .codiag A => isRegularUnderRepr_codiag A
  | _, _, .distr A B C => isRegularUnderRepr_distr A B C
  | _, _, .cons A => isRegularUnderRepr_cons A
  | _, _, .uncons A => isRegularUnderRepr_uncons A
  | _, _, .reverse A => isRegularUnderRepr_reverse A
  | _, _, .concat A => isRegularUnderRepr_concat A
  | _, _, .split A B => isRegularUnderRepr_split A B
  | _, _, .pref G grp hfin => by
      letI := grp
      haveI := hfin
      exact isRegularUnderRepr_pref G
  | _, _, .comp s t => (RegTerm.isRegularUnderRepr s).comp (RegTerm.isRegularUnderRepr t)
  | _, _, .prodMap s t =>
      IsRegularUnderRepr.prodMap (RegTerm.isRegularUnderRepr s) (RegTerm.isRegularUnderRepr t)
  | _, _, .sumMap s t =>
      IsRegularUnderRepr.sumMap (RegTerm.isRegularUnderRepr s) (RegTerm.isRegularUnderRepr t)
  | _, _, .map t => IsRegularUnderRepr.mapList (RegTerm.isRegularUnderRepr t)

/-- **Theorem `thm:regular-terms`, the easy direction.**  Every type-to-type function that is
defined by a regular term is regular under string representation. -/
theorem regularTerm_isRegular {A B : Ty} {f : A.Elt → B.Elt} (h : IsRegularTermFun f) :
    IsRegularUnderRepr f := by
  obtain ⟨t, ht⟩ := h
  exact ht ▸ t.isRegularUnderRepr

end Transducers
