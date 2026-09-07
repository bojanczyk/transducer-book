/-
The atomic rational terms that are computed by a single left-to-right machine, or by a composition
of such machines, are rational under string representation.  Part of the easy direction of Theorem
`thm:rational-terms` of *Transducers* (M. Bojańczyk).

The machines of `CombMach.lean` compute *rational* functions -- that is what
`Transducers.Comb.Mach.isRationalFun_run` says -- so every atomic term whose treatment in
`CombAtom*.lean` goes through a single such machine, or through a composition of two of them, is
rational under string representation and not merely regular, with the very same correctness proof.
That covers identity, the two co-projections, the two projections, the list deconstructor, split,
concatenation and group prefix multiplication.  This file collects them, and adds the co-diagonal,
which deletes the first letter, and the two atomic functions of Theorem `thm:rational-terms` that
adjoin a unit, which decorate the input with constants.
-/
import RequestProject.PartC.RatTerms
import RequestProject.PartC.CombAtomProj
import RequestProject.PartC.CombAtomCons
import RequestProject.PartC.CombAtomSplit
import RequestProject.PartC.CombAtomConcat
import RequestProject.PartC.CombAtomPref
import RequestProject.PartC.CombCombinators

namespace Transducers
namespace RatComb

open Comb

/-! ## Two elementary rational functions -/

/-- Composition of rational functions, up to pointwise equality. -/
theorem isRationalFun_comp' {A B C : Type} {f : List A → List B} {g : List B → List C}
    {h : List A → List C} (hf : IsRationalFun f) (hg : IsRationalFun g)
    (hh : ∀ w, h w = g (f w)) : IsRationalFun h :=
  (isRationalFun_comp hf hg).congr (fun w v => by rw [hh])

/-- Appending a fixed string is a rational function. -/
theorem isRationalFun_appendConst {A : Type} [Finite A] (v : List A) :
    IsRationalFun (fun w : List A => w ++ v) := by
  have h : ∀ w : List A,
      seqFinEval (fun (_ : Unit) (_ : A) => ()) (fun _ c => [c]) (fun _ => v) () w = w ++ v := by
    intro w
    induction w with
    | nil => rfl
    | cons c w ih => rw [seqFinEval_cons]; simpa using ih
  refine (isRationalFun_seqFinEval (fun (_ : Unit) (_ : A) => ()) () (fun _ c => [c])
    (fun _ => v)).congr (fun w u => ?_)
  rw [h w]

/-- The identity is a rational function. -/
theorem isRationalFun_id' {A : Type} [Finite A] : IsRationalFun (fun w : List A => w) := by
  refine (isRationalFun_appendConst ([] : List A)).congr (fun w u => ?_)
  simp

/-! ## Identity, the co-projections and the co-diagonal -/

theorem isRationalUnderRepr_id (A : Ty) : IsRationalUnderRepr (fun x : A.Elt => x) :=
  ⟨fun w => w, isRationalFun_id', fun _ => rfl⟩

theorem isRationalUnderRepr_inl (A B : Ty) :
    IsRationalUnderRepr (A := A) (B := Ty.sum A B) (fun a => Sum.inl a) :=
  ⟨fun w => Sym8.left :: w, isRationalFun_cons _, fun _ => rfl⟩

theorem isRationalUnderRepr_inr (A B : Ty) :
    IsRationalUnderRepr (A := B) (B := Ty.sum A B) (fun b => Sum.inr b) :=
  ⟨fun w => Sym8.right :: w, isRationalFun_cons _, fun _ => rfl⟩

/-- **The co-diagonal is rational under string representation**: it deletes the first letter of
the representation. -/
theorem isRationalUnderRepr_codiag (A : Ty) :
    IsRationalUnderRepr (A := Ty.sum A A) (B := A)
      (fun x => Sum.elim (fun a => a) (fun a => a) x) := by
  refine ⟨fun w => w.tail, isRationalFun_tail, fun x => ?_⟩
  cases x with
  | inl a => rfl
  | inr a => rfl

/-! ## Adjoining units -/

/-- **Adjoining a unit on the right is rational under string representation.** -/
theorem isRationalUnderRepr_appendOne (A : Ty) :
    IsRationalUnderRepr (A := A) (B := Ty.prod A Ty.one) (fun a => (a, ())) := by
  refine ⟨fun w => Sym8.lpar :: (w ++ [Sym8.comma, Sym8.one, Sym8.rpar]), ?_, fun a => rfl⟩
  exact isRationalFun_comp (isRationalFun_appendConst [Sym8.comma, Sym8.one, Sym8.rpar])
    (isRationalFun_cons Sym8.lpar)

/-- **Adjoining a unit on the left is rational under string representation.** -/
theorem isRationalUnderRepr_prependOne (A : Ty) :
    IsRationalUnderRepr (A := A) (B := Ty.prod Ty.one A) (fun a => ((), a)) := by
  refine ⟨fun w => Sym8.lpar :: Sym8.one :: Sym8.comma :: (w ++ [Sym8.rpar]), ?_, fun a => rfl⟩
  exact isRationalFun_comp (isRationalFun_comp (isRationalFun_comp
    (isRationalFun_appendConst [Sym8.rpar]) (isRationalFun_cons Sym8.comma))
    (isRationalFun_cons Sym8.one)) (isRationalFun_cons Sym8.lpar)

/-! ## The atomic terms computed by a machine -/

theorem isRationalUnderRepr_fst (A B : Ty) :
    IsRationalUnderRepr (fun x : (Ty.prod A B).Elt => x.1) :=
  ⟨fstMach.run ((Ty.prod A B).height) .start,
    fstMach.isRationalFun_run _ _, fun x => fstMach_run A B x.1 x.2⟩

theorem isRationalUnderRepr_snd (A B : Ty) :
    IsRationalUnderRepr (fun x : (Ty.prod A B).Elt => x.2) :=
  ⟨sndMach.run ((Ty.prod A B).height) .start,
    sndMach.isRationalFun_run _ _, fun x => sndMach_run A B x.1 x.2⟩

theorem isRationalUnderRepr_uncons (A : Ty) :
    IsRationalUnderRepr (A := Ty.list A) (B := Ty.sum Ty.one (Ty.prod A (Ty.list A)))
      (fun l => match l with | [] => Sum.inl () | a :: l' => Sum.inr (a, l')) :=
  ⟨unconsMach.run ((Ty.list A).height) .start, unconsMach.isRationalFun_run _ _,
    fun l => unconsMach_run A l⟩

theorem isRationalUnderRepr_split (A B : Ty) :
    IsRationalUnderRepr (A := splitDom A B)
      (B := Ty.prod (Ty.list A) (Ty.list (pairTy A B))) (fun l => splitList l) := by
  refine ⟨splitMach.run ((splitDom A B).height) (SplitPhase.start, false, false),
    splitMach.isRationalFun_run _ _, fun l => ?_⟩
  rw [splitMach_run, splitOut_false]
  simp only [aBody]
  show _ = Sym8.lpar :: ((Ty.list A).repr (splitList l).1
    ++ Sym8.comma :: ((Ty.list (pairTy A B)).repr (splitList l).2 ++ [Sym8.rpar]))
  rw [Ty.repr_list, Ty.repr_list]
  simp

theorem isRationalUnderRepr_concat (A : Ty) :
    IsRationalUnderRepr (A := catDom A) (B := Ty.list A) (fun l => l.flatten) := by
  refine ⟨fun w => dropFirstMach.run ((catDom A).height)
      .first (concatMach.run ((catDom A).height) .start w),
    isRationalFun_comp (concatMach.isRationalFun_run _ _) (dropFirstMach.isRationalFun_run _ _),
    fun l => ?_⟩
  show dropFirstMach.run _ .first (concatMach.run _ ConcatMode.start ((catDom A).repr l)) = _
  rw [concatMach_run, dropFirstMach_run, commaBlocks_tail]
  rfl

theorem isRationalUnderRepr_pref (G : Ty) [Group G.Elt] [Finite G.Elt] :
    IsRationalUnderRepr (A := Ty.list G) (B := Ty.list G) (fun l => prefixProd l) := by
  refine ⟨fun w => dropFirstMach.run ((prefDom G).height) .first
      ((prefMach G).run ((prefDom G).height) (PrefPhase.start, 1, some (pfxNil G)) w),
    isRationalFun_comp ((prefMach G).isRationalFun_run _ _)
      (dropFirstMach.isRationalFun_run _ _),
    fun l => ?_⟩
  show dropFirstMach.run ((prefDom G).height) DropMode.first
      ((prefMach G).run ((prefDom G).height) (PrefPhase.start, 1, some (pfxNil G))
        ((prefDom G).repr l)) = (Ty.list G).repr (prefixProd l)
  rw [prefMach_run, dropFirstMach_run, commaBlocks_tail, prefixProdFrom_one]
  rfl

end RatComb
end Transducers
