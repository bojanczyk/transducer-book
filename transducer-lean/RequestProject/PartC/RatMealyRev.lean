/-
Reversible Mealy machines are definable by *rational* terms.

This is the rational-term analogue of Lemma `lem:terms-define-reversible`, needed for Theorem
`thm:rational-terms`.  The construction is the one of `CombMealyRev.lean` and all of its
combinatorics is reused verbatim: each letter is paired with the pair of group elements
`Transducers.RevMealy.phi`, group prefix multiplication turns the list of these into the list of
their prefix products, the delay machine of Example `ex:delay` -- a flip-flop machine, hence
covered by `Transducers.rtfun_flipFlop_eval` -- pairs every prefix product with the previous one,
and a letter-to-letter homomorphism reads the output letter off the two.

None of the four steps uses the diagonal or reverse, so the argument goes through unchanged for
the rational terms.  The *right-to-left* reversible machines are not treated here: they are not
needed, because Exercise `exer:no-reverse-reversible` removes them from the list of primes.
-/
import RequestProject.PartC.RatMealyFF
import RequestProject.PartC.CombMealyRev

namespace Transducers

open RevMealy in
/-- The version for a machine whose alphabets and states are the elements of types. -/
theorem rtfun_reversible_eval {A B QT : Ty} (hA : Finite A.Elt) (hQ : Finite QT.Elt)
    (M : Mealy A.Elt B.Elt QT.Elt) (hM : M.Reversible) :
    IsRatTermFun (A := .list A) (B := .list B) M.eval := by
  classical
  haveI := hA
  haveI := hQ
  haveI : Finite (Grp A.Elt QT.Elt) := inferInstance
  haveI : Nonempty (Grp A.Elt QT.Elt) := ⟨1⟩
  obtain ⟨PT, ⟨eH⟩, hPf⟩ := exists_ty_equiv (Grp A.Elt QT.Elt)
  letI grp : Group PT.Elt := Equiv.group eH.symm
  have hhom : ∀ x y : PT.Elt, eH.symm (x * y) = eH.symm x * eH.symm y := by
    intro x y
    exact eH.symm_apply_apply _
  have hone : eH.symm (1 : PT.Elt) = 1 := eH.symm_apply_apply _
  have hphi : IsRatTermFun (A := .list A) (B := .list PT)
      (fun l => l.map (fun a => eH (phi M hM a))) := rtfun_mapRen hA _
  have hpref : IsRatTermFun (A := .list PT) (B := .list PT) (fun l => prefixProd l) :=
    ⟨RatTerm.pref PT grp hPf, rfl⟩
  have hdelay : IsRatTermFun (A := .list PT) (B := .list (.prod PT PT))
      (delayMealy (eH 1)).eval :=
    rtfun_flipFlop_eval hPf hPf _ (delayMealy_flipFlop _)
  haveI : Finite (Ty.prod PT PT).Elt := by
    show Finite (PT.Elt × PT.Elt); haveI := hPf; infer_instance
  have hout : IsRatTermFun (A := .list (.prod PT PT)) (B := .list B)
      (fun l => l.map (fun p => outH M (eH.symm p.1, eH.symm p.2))) :=
    rtfun_mapRen inferInstance _
  refine (hphi.comp (hpref.comp (hdelay.comp hout))).congr ?_
  intro l
  have h1 : l.map (fun a => eH (phi M hM a)) = (l.map (phi M hM)).map eH := by
    simp [List.map_map, Function.comp_def]
  have h2 : prefixProd ((l.map (phi M hM)).map eH)
      = (prefixProd (l.map (phi M hM))).map eH :=
    prefixProd_map_of_symm_hom eH hone hhom _
  have h3 : (delayMealy (eH 1)).eval ((prefixProd (l.map (phi M hM))).map eH)
      = (delayList (1 : Grp A.Elt QT.Elt) (prefixProd (l.map (phi M hM)))).map
        (fun q => (eH q.1, eH q.2)) := by
    show (delayMealy (eH 1)).run (eH 1) _ = _
    rw [delayMealy_run]
    exact delayList_map eH 1 _
  have h4 := rev_run M hM (1 : Grp A.Elt QT.Elt) l
  rw [accState_one M] at h4
  show ((delayMealy (eH 1)).eval (prefixProd (l.map (fun a => eH (phi M hM a))))).map
      (fun p => outH M (eH.symm p.1, eH.symm p.2)) = M.eval l
  rw [h1, h2, h3, List.map_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]
  exact h4

/-- **Reversible Mealy machines are definable by rational terms.** -/
theorem rat_terms_define_reversible {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : IsReversibleMealy g) : RatTermStrFun g := by
  obtain ⟨Q, hQ, M, hMg, hRev⟩ := h
  subst hMg
  haveI := hX
  haveI := hY
  haveI := hQ
  by_cases hne : Nonempty X
  case neg => exact ratTermStrFun_of_isEmpty_dom _ (not_nonempty_iff.1 hne)
  by_cases hne' : Nonempty Y
  case neg => exact ratTermStrFun_of_isEmpty_cod _ (not_nonempty_iff.1 hne')
  haveI := hne
  haveI := hne'
  haveI : Nonempty Q := ⟨M.init⟩
  obtain ⟨A, ⟨eA⟩, hAf⟩ := exists_ty_equiv X
  obtain ⟨B, ⟨eB⟩, hBf⟩ := exists_ty_equiv Y
  obtain ⟨QT, ⟨eQ⟩, hQf⟩ := exists_ty_equiv Q
  refine ratTermStrFun_of_one A B hBf eA.symm eB ?_
  exact (rtfun_reversible_eval hAf hQf (M.transport eA.symm eB eQ)
    (Mealy.reversible_transport hRev _ _ _)).congr
    (fun l => Mealy.eval_transport M eA.symm eB eQ l)

end Transducers
