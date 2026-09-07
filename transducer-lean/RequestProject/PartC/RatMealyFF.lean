/-
Flip-flop Mealy machines are definable by *rational* terms, in both reading directions.

This is the rational-term analogue of Lemma `lem:terms-define-flip-flop`, needed for Theorem
`thm:rational-terms`.  The left-to-right case is the book's argument transcribed with the rational
combinators of `RatTerms.lean`: annotate the reset letters with the state they produce, split at
the annotations, and apply to every block the homomorphism determined by the (finite) state that
labels it.

The right-to-left case cannot be reduced to the left-to-right one by reversal, because reversal is
not a rational term.  Instead the annotation is put *before* each reset letter, together with a
separator, and the state carried by a block is then its **last** letter -- which is why left
distributivity, and with it `Transducers.rtfun_finCasesR`, is one of the atoms of the rational
terms.
-/
import RequestProject.PartC.RatStrFam
import RequestProject.PartC.RatDerived
import RequestProject.PartC.CombMealyFF

namespace Transducers

/-! ## The left-to-right case -/

/-- The version for a machine whose alphabets and states are the elements of types. -/
theorem rtfun_flipFlop_eval {A B QT : Ty} (hA : Finite A.Elt) (hQ : Finite QT.Elt)
    (M : Mealy A.Elt B.Elt QT.Elt) (hM : M.FlipFlop) :
    IsRatTermFun (A := .list A) (B := .list B) M.eval := by
  have h1 : IsRatTermFun (A := .list A) (B := .list (.sum A QT))
      (fun l => (l.map M.ffHom).flatten) :=
    rat_terms_define_string_homomorphisms (B := .sum A QT) hA M.ffHom
  have h3 : IsRatTermFun (A := .list A) (B := .list B)
      (fun l => l.map (fun a => (M.step M.init a).2)) := rtfun_mapRen hA _
  have h4 : IsRatTermFun (A := .prod QT (.list A)) (B := .list B)
      (fun p => p.2.map (fun a => (M.step p.1 a).2)) :=
    rtfun_finCases (F := QT) (T := .list A) (U := .list B) hQ
      (g := fun q v => v.map (fun a => (M.step q a).2)) (fun q => rtfun_mapRen hA _)
  have h5 := (h4.mapList).comp (rtfun_concat B)
  have h6 := (h3.prodMap h5).comp (rtfun_append B)
  refine (h1.comp ((rtfun_split A QT).comp h6)).congr ?_
  intro l
  exact (Mealy.ff_run M hM M.init l).symm

/-- **Flip-flop Mealy machines are definable by rational terms.** -/
theorem rat_terms_define_flip_flop {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : IsFlipFlopMealy g) : RatTermStrFun g := by
  obtain ⟨Q, hQ, M, hMg, hFF⟩ := h
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
  exact (rtfun_flipFlop_eval hAf hQf (M.transport eA.symm eB eQ)
    (Mealy.flipFlop_transport hFF _ _ _)).congr
    (fun l => Mealy.eval_transport M eA.symm eB eQ l)

/-! ## The right-to-left case

The annotation now puts the state that a reset letter produces *before* that letter, separated
from it, so that the state which labels a block of the split is the block's last letter.
-/

namespace Mealy

variable {X Y Q : Type}

/-- The homomorphism `A* → ((A + Q) + 1)*` of the right-to-left construction: a reset letter is
preceded by the state that it produces and by a separator. -/
noncomputable def ffHomR (M : Mealy X Y Q) (a : X) : List ((X ⊕ Q) ⊕ Unit) :=
  match M.ffTarget a with
  | none => [Sum.inl (Sum.inl a)]
  | some r => [Sum.inl (Sum.inr r), Sum.inr (), Sum.inl (Sum.inl a)]

/-- The annotated string: the homomorphic image, followed by the initial state. -/
noncomputable def ffAnn (M : Mealy X Y Q) (w : List X) : List ((X ⊕ Q) ⊕ Unit) :=
  (w.map M.ffHomR).flatten ++ [Sum.inl (Sum.inr M.init)]

lemma ffAnn_nil (M : Mealy X Y Q) : M.ffAnn [] = [Sum.inl (Sum.inr M.init)] := rfl

lemma ffAnn_cons (M : Mealy X Y Q) (a : X) (w : List X) :
    M.ffAnn (a :: w) = M.ffHomR a ++ M.ffAnn w := by
  simp [ffAnn, List.append_assoc]

/-- The state that a flip-flop machine is in after reading `w` from right to left: the target of
the leftmost reset letter of `w`, and the initial state when there is none. -/
noncomputable def ffStateR (M : Mealy X Y Q) : List X → Q
  | [] => M.init
  | a :: w =>
      match M.ffTarget a with
      | none => M.ffStateR w
      | some r => r

/-- The longest prefix of `w` that contains no reset letter. -/
noncomputable def nrPrefix (M : Mealy X Y Q) : List X → List X
  | [] => []
  | a :: w =>
      match M.ffTarget a with
      | none => a :: M.nrPrefix w
      | some _ => []

/-- The homomorphism that reads a block in a fixed state; the annotation letters are erased. -/
def ffBlkHom (M : Mealy X Y Q) (q : Q) : (X ⊕ Q) → List Y
  | Sum.inl a => [(M.step q a).2]
  | Sum.inr _ => []

/-- The state carried by an annotation letter. -/
def ffStateOf (M : Mealy X Y Q) : (X ⊕ Q) → Q
  | Sum.inl _ => M.init
  | Sum.inr r => r

/-- The output on one block of the split: the last letter of the block is the state, and the rest
of the block is read in that state. -/
noncomputable def ffSegOut (M : Mealy X Y Q) (v : List (X ⊕ Q)) : List Y :=
  match unsnocList v with
  | Sum.inl _ => []
  | Sum.inr (u, x) => (u.map (M.ffBlkHom (M.ffStateOf x))).flatten

/-- The whole right-to-left output, read off the split of the annotation. -/
noncomputable def ffOut (M : Mealy X Y Q) (z : List ((X ⊕ Q) ⊕ Unit)) : List Y :=
  M.ffSegOut (splitList z).1 ++ ((splitList z).2.map (fun p => M.ffSegOut p.2)).flatten

lemma ffSegOut_append_singleton (M : Mealy X Y Q) (u : List (X ⊕ Q)) (x : X ⊕ Q) :
    M.ffSegOut (u ++ [x]) = (u.map (M.ffBlkHom (M.ffStateOf x))).flatten := by
  rw [ffSegOut, unsnocList_append_singleton]

/-- **The prefix of the split.**  It consists of the letters before the first reset letter,
followed by the state that the machine has after reading `w` from right to left. -/
lemma ffAnn_split_fst (M : Mealy X Y Q) (w : List X) :
    (splitList (M.ffAnn w)).1 =
      (M.nrPrefix w).map Sum.inl ++ [Sum.inr (M.ffStateR w)] := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [ffAnn_cons]
      rcases h : M.ffTarget a with _ | r
      · have hh : M.ffHomR a = [Sum.inl (Sum.inl a)] := by rw [ffHomR, h]
        have hn : M.nrPrefix (a :: w) = a :: M.nrPrefix w := by rw [nrPrefix, h]
        have hs : M.ffStateR (a :: w) = M.ffStateR w := by rw [ffStateR, h]
        rw [hh, List.singleton_append, splitList_inl, hn, hs, ih]
        simp
      · have hh : M.ffHomR a = [Sum.inl (Sum.inr r), Sum.inr (), Sum.inl (Sum.inl a)] := by
          rw [ffHomR, h]
        have hn : M.nrPrefix (a :: w) = [] := by rw [nrPrefix, h]
        have hs : M.ffStateR (a :: w) = r := by rw [ffStateR, h]
        rw [hh, hn, hs]
        show (splitList (Sum.inl (Sum.inr r) :: Sum.inr () ::
          Sum.inl (Sum.inl a) :: M.ffAnn w)).1 = _
        rw [splitList_inl, splitList_inr]
        simp

/-- Prefixing a letter to the prefix block adds one output letter. -/
lemma ffSegOut_cons_split (M : Mealy X Y Q) (a : X) (w : List X) :
    M.ffSegOut (Sum.inl a :: (splitList (M.ffAnn w)).1) =
      (M.step (M.ffStateR w) a).2 :: M.ffSegOut (splitList (M.ffAnn w)).1 := by
  rw [ffAnn_split_fst, ← List.cons_append, ffSegOut_append_singleton,
    ffSegOut_append_singleton]
  show ((Sum.inl a :: (M.nrPrefix w).map Sum.inl).map
      (M.ffBlkHom (M.ffStateOf (Sum.inr (M.ffStateR w))))).flatten = _
  rw [List.map_cons, List.flatten_cons]
  rfl

/-- **The state after a right-to-left pass.**  For a flip-flop machine it is the target of the
leftmost reset letter. -/
lemma ffStateR_eq (M : Mealy X Y Q) (hM : M.FlipFlop) (w : List X) :
    M.trans w.reverse M.init = M.ffStateR w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [List.reverse_cons, Mealy.trans_append, ih]
      show M.letterTrans a (M.ffStateR w) = _
      rcases Mealy.ffTarget_spec M hM a with ⟨h0, hid⟩ | ⟨r, h0, hr⟩
      · rw [hid, ffStateR, h0]
      · rw [hr, ffStateR, h0]

/-- **The right-to-left run of a flip-flop machine, read off the split of its annotation.** -/
lemma ffOut_ffAnn (M : Mealy X Y Q) (hM : M.FlipFlop) (w : List X) :
    M.ffOut (M.ffAnn w) = (M.eval w.reverse).reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      have hstate : M.trans w.reverse M.init = M.ffStateR w := ffStateR_eq M hM w
      have hev : (M.eval (a :: w).reverse).reverse =
          (M.step (M.ffStateR w) a).2 :: (M.eval w.reverse).reverse := by
        rw [List.reverse_cons, Mealy.eval_append, List.reverse_append, hstate]
        rfl
      rw [hev, ← ih, ffAnn_cons]
      rcases h : M.ffTarget a with _ | r
      · have hh : M.ffHomR a = [Sum.inl (Sum.inl a)] := by rw [ffHomR, h]
        have hs : M.ffStateR w = M.ffStateR (a :: w) := by rw [ffStateR, h]
        rw [hh, List.singleton_append, ffOut, ffOut, splitList_inl, ffSegOut_cons_split]
        simp
      · have hh : M.ffHomR a = [Sum.inl (Sum.inr r), Sum.inr (), Sum.inl (Sum.inl a)] := by
          rw [ffHomR, h]
        rw [hh, ffOut, ffOut]
        show M.ffSegOut (splitList (Sum.inl (Sum.inr r) :: Sum.inr () ::
              Sum.inl (Sum.inl a) :: M.ffAnn w)).1 ++
            ((splitList (Sum.inl (Sum.inr r) :: Sum.inr () ::
              Sum.inl (Sum.inl a) :: M.ffAnn w)).2.map (fun p => M.ffSegOut p.2)).flatten = _
        rw [splitList_inl, splitList_inr, splitList_inl]
        show M.ffSegOut ([Sum.inr r] : List (X ⊕ Q)) ++
            (M.ffSegOut (Sum.inl a :: (splitList (M.ffAnn w)).1) ::
              (splitList (M.ffAnn w)).2.map (fun p => M.ffSegOut p.2)).flatten = _
        rw [ffSegOut_cons_split]
        show ([] : List Y) ++ _ = _
        simp

end Mealy

/-! ### The right-to-left case as a statement about rational terms -/

/-- The version for a machine whose alphabets and states are the elements of types. -/
theorem rtfun_flipFlopR_eval {A B QT : Ty} (hA : Finite A.Elt) (hQ : Finite QT.Elt)
    (M : Mealy A.Elt B.Elt QT.Elt) (hM : M.FlipFlop) :
    IsRatTermFun (A := .list A) (B := .list B) (fun w => (M.eval w.reverse).reverse) := by
  haveI := hA
  haveI := hQ
  haveI hL : Finite (Ty.sum A QT).Elt := inferInstanceAs (Finite (A.Elt ⊕ QT.Elt))
  have hAnn : IsRatTermFun (A := .list A) (B := .list (.sum (.sum A QT) .one)) M.ffAnn :=
    rtfun_appendConst
      (rat_terms_define_string_homomorphisms (B := .sum (.sum A QT) .one) hA M.ffHomR)
      [Sum.inl (Sum.inr M.init)]
  have hCase : IsRatTermFun (A := .prod (.list (.sum A QT)) (.sum A QT)) (B := .list B)
      (fun p => (p.1.map (M.ffBlkHom (M.ffStateOf p.2))).flatten) :=
    rtfun_finCasesR (T := .list (.sum A QT)) (F := .sum A QT) (U := .list B) hL
      (g := fun x u => (u.map (M.ffBlkHom (M.ffStateOf x))).flatten)
      (fun x => rat_terms_define_string_homomorphisms hL _)
  have hSeg : IsRatTermFun (A := .list (.sum A QT)) (B := .list B) M.ffSegOut := by
    refine ((rtfun_unsnoc (.sum A QT)).comp
      ((rtfun_const .one (.list B) []).copair hCase)).congr ?_
    intro v
    show Sum.elim _ _ (unsnocList v) = M.ffSegOut v
    rw [Mealy.ffSegOut]
    cases unsnocList v with
    | inl u => rfl
    | inr p => rfl
  have hBlocks : IsRatTermFun (A := .list (.prod .one (.list (.sum A QT)))) (B := .list B)
      (fun bs => (bs.map (fun p => M.ffSegOut p.2)).flatten) :=
    (((rtfun_snd .one (.list (.sum A QT))).comp hSeg).mapList).comp (rtfun_concat B)
  have hOut := (hSeg.prodMap hBlocks).comp (rtfun_append B)
  refine (hAnn.comp ((rtfun_split (.sum A QT) .one).comp hOut)).congr ?_
  intro w
  exact Mealy.ffOut_ffAnn M hM w

/-- **Right-to-left flip-flop Mealy machines are definable by rational terms.**  This is the case
that forces left distributivity into the list of atoms: reversal is not available, so the state
that labels a block has to be read off the *end* of the block. -/
theorem rat_terms_define_flip_flop_rtl {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : IsFlipFlopMealy (fun w => (g w.reverse).reverse)) :
    RatTermStrFun g := by
  obtain ⟨Q, hQ, M, hMg, hFF⟩ := h
  haveI := hX
  haveI := hY
  haveI := hQ
  have hg : ∀ w, g w = (M.eval w.reverse).reverse := by
    intro w
    have h1 := congrFun hMg w.reverse
    simp only [List.reverse_reverse] at h1
    rw [h1, List.reverse_reverse]
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
  refine (rtfun_flipFlopR_eval hAf hQf (M.transport eA.symm eB eQ)
    (Mealy.flipFlop_transport hFF _ _ _)).congr ?_
  intro l
  simp [Mealy.eval_transport, hg, List.map_reverse]

end Transducers
