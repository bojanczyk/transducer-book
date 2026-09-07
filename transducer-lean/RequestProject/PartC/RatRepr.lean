/-
The string representation and its inverse are definable by *rational* terms, and with them the
hard direction of Theorem `thm:rational-terms` of *Transducers* (M. Bojańczyk).

This is the analogue, for the rational terms, of Lemma `lem:terms-define-string-representation`.
The representation itself is again a straightforward induction, with one change forced by the
absence of the diagonal: the regular case builds `(a,b) ↦ ⟨a⟩,⟨b⟩` by *pairing* two terms on the
same input, whereas here the two coordinates are encoded separately by the functoriality
combinator `f₁ × f₂` and the fixed letters are attached by `Transducers.rtfun_prependConst` and
`Transducers.rtfun_appendConst`.

The inverse is where pairing really is missing.  For a co-product and for a list the regular
argument goes through unchanged; for a product it does not, because it applies to the *same* input
the two functions that implement the two projections, and then pairs the results.  Instead the
machine `Transducers.RatComb.pairMarkMach`, which already serves the combinator `f₁ × f₂`, cuts
the representation of a pair into the two tagged blocks `L⟨a⟩` and `R⟨b⟩`; the split of Example
`ex:split` turns them into a list of two blocks, the inverse of a co-product -- which is available
-- turns that into the list `[inl a, inr b]`, and a second split, followed by two `head`
operations, reads the pair off it.  No coordinate is ever duplicated, which is what the rational
terms must not be able to do.
-/
import RequestProject.PartC.RatComplete
import RequestProject.PartC.RatEasy
import RequestProject.PartC.RatComb
import RequestProject.PartC.RatDerived
import RequestProject.PartC.CombRepr

namespace Transducers

open Comb

/-! ## Rational string functions as rational terms -/

/-- A rational function on strings over the eight-letter alphabet is definable by a rational
term. -/
lemma rtfun_ofRationalStr {f : List Sym8 → List Sym8} (hf : IsRationalFun f) :
    IsRatTermFun (A := .list SymTy) (B := .list SymTy)
      (fun l => (f (l.map symEq.symm)).map symEq) :=
  ratTermStrFun_of_isRationalFun inferInstance inferInstance hf SymTy SymTy inferInstance
    inferInstance symEq.symm symEq

/-- The same, for a rational function whose output alphabet is `Option Sym8`. -/
lemma rtfun_ofRationalStrOpt {f : List Sym8 → List (Option Sym8)} (hf : IsRationalFun f) :
    IsRatTermFun (A := .list SymTy) (B := .list (.sum SymTy .one))
      (fun l => (f (l.map symEq.symm)).map optSymEq) := by
  haveI : Finite (Ty.sum SymTy Ty.one).Elt := by
    show Finite (SymTy.Elt ⊕ Unit); infer_instance
  exact ratTermStrFun_of_isRationalFun inferInstance inferInstance hf SymTy (.sum SymTy .one)
    inferInstance inferInstance symEq.symm optSymEq

/-! ## Prepending the separator -/

lemma rtfun_prependSep (T : Ty) :
    IsRatTermFun (A := .list (.sum T .one)) (B := .list (.sum T .one)) prependSep := by
  set U : Ty := .sum T .one with hU
  refine ((rtfun_uncons U).comp ((rtfun_const .one (.list U) []).copair
    ((rtfun_inr .one (.prod U (.list U))).comp
      ((rtfun_cons U).comp (rtfun_consFixed U (Sum.inr ())))))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons x r => rfl

/-! ## The inverse for a co-product -/

lemma rtfun_sumInvFun {A B : Ty} {fa : List SymTy.Elt → A.Elt} {fb : List SymTy.Elt → B.Elt}
    (hfa : IsRatTermFun (A := .list SymTy) (B := A) fa)
    (hfb : IsRatTermFun (A := .list SymTy) (B := B) fb) (x : SymTy.Elt) :
    IsRatTermFun (A := .list SymTy) (B := .sum A B) (sumInvFun A B fa fb x) := by
  classical
  by_cases h1 : x = symEq Sym8.left
  · refine (hfa.comp (rtfun_inl A B)).congr ?_
    intro rest
    rw [sumInvFun, if_pos h1]
  · by_cases h2 : x = symEq Sym8.right
    · refine (hfb.comp (rtfun_inr A B)).congr ?_
      intro rest
      rw [sumInvFun, if_neg h1, if_pos h2]
    · refine (rtfun_const (.list SymTy) (.sum A B) default).congr ?_
      intro rest
      rw [sumInvFun, if_neg h1, if_neg h2]

/-- The inverse of the representation of a co-product, assembled from the inverses of the two
summands.  It is used twice below: for the co-product itself, and -- applied to the two tagged
blocks that the pair-marking machine produces -- for the product. -/
noncomputable def sumInv (A B : Ty) (invA : List SymTy.Elt → A.Elt)
    (invB : List SymTy.Elt → B.Elt) (l : List SymTy.Elt) : (Ty.sum A B).Elt :=
  match l with
  | [] => default
  | x :: rest => sumInvFun A B invA invB x rest

lemma rtfun_sumInv {A B : Ty} {invA : List SymTy.Elt → A.Elt} {invB : List SymTy.Elt → B.Elt}
    (hinvA : IsRatTermFun (A := .list SymTy) (B := A) invA)
    (hinvB : IsRatTermFun (A := .list SymTy) (B := B) invB) :
    IsRatTermFun (A := .list SymTy) (B := .sum A B) (sumInv A B invA invB) := by
  refine ((rtfun_uncons SymTy).comp
    ((rtfun_const .one (.sum A B) default).copair
      (rtfun_finCases instFiniteSymTy (rtfun_sumInvFun hinvA hinvB)))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons x rest => rfl

lemma sumInv_repr_left {A B : Ty} {invA : List SymTy.Elt → A.Elt}
    {invB : List SymTy.Elt → B.Elt} {a : A.Elt} (h : invA (reprElt A a) = a) :
    sumInv A B invA invB (symEq Sym8.left :: reprElt A a) = Sum.inl a := by
  show sumInvFun A B invA invB (symEq Sym8.left) (reprElt A a) = _
  rw [sumInvFun, if_pos rfl, h]

lemma sumInv_repr_right {A B : Ty} {invA : List SymTy.Elt → A.Elt}
    {invB : List SymTy.Elt → B.Elt} {b : B.Elt} (h : invB (reprElt B b) = b) :
    sumInv A B invA invB (symEq Sym8.right :: reprElt B b) = Sum.inr b := by
  have hne : symEq Sym8.right ≠ symEq Sym8.left := by
    intro hh
    exact absurd (symEq.injective hh) (by decide)
  show sumInvFun A B invA invB (symEq Sym8.right) (reprElt B b) = _
  rw [sumInvFun, if_neg hne, if_pos rfl, h]

/-! ## The inverse for a product -/

/-- Reading a pair off the list `[inl a, inr b]`: the split of Example `ex:split` separates the
two entries, and two `head` operations pick them out. -/
lemma rtfun_pairOfSumList (A B : Ty) :
    IsRatTermFun (A := .list (.sum A B)) (B := .prod A B)
      (fun l => ((splitList l).1.headI, ((splitList l).2.map Prod.fst).headI)) :=
  (rtfun_split A B).comp
    ((rat_claim_head A).prodMap
      (((rtfun_fst B (.list A)).mapList).comp (rat_claim_head B)))

lemma pairOfSumList_two (A B : Ty) (a : A.Elt) (b : B.Elt) :
    ((splitList [Sum.inl a, Sum.inr b]).1.headI,
      ((splitList [Sum.inl a, Sum.inr b]).2.map Prod.fst).headI) = (a, b) := rfl

/-! ## Lemma `lem:terms-define-string-representation` for rational terms -/

/-- **The string representation and a one-sided inverse of it are definable by rational
terms.**  This is the rational analogue of Lemma `lem:terms-define-string-representation`. -/
theorem rat_terms_define_string_representation :
    ∀ A : Ty, IsRatTermFun (A := A) (B := .list SymTy) (reprElt A) ∧
      ∃ inv : List SymTy.Elt → A.Elt,
        IsRatTermFun (A := .list SymTy) (B := A) inv ∧ ∀ a : A.Elt, inv (reprElt A a) = a := by
  intro A
  induction A with
  | one =>
      exact ⟨(rtfun_const .one (.list SymTy) [symEq Sym8.one]).congr (fun a => by cases a; rfl),
        ⟨fun _ => (), rtfun_const (Ty.list SymTy) Ty.one (), fun a => by cases a; rfl⟩⟩
  | prod A B ihA ihB =>
      obtain ⟨hencA, invA, hinvA, hinvAe⟩ := ihA
      obtain ⟨hencB, invB, hinvB, hinvBe⟩ := ihB
      constructor
      · refine (rtfun_prependConst (rtfun_appendConst
          ((hencA.prodMap (rtfun_prependConst hencB [symEq Sym8.comma])).comp
            (rtfun_append SymTy)) [symEq Sym8.rpar]) [symEq Sym8.lpar]).congr ?_
        rintro ⟨a, b⟩
        simp [reprElt, Ty.repr_prod]
      · haveI : Finite (Ty.sum SymTy Ty.one).Elt := by
          show Finite (SymTy.Elt ⊕ Unit); infer_instance
        refine ⟨_, ((rtfun_ofRationalStrOpt
            (RatComb.pairMarkMach.isRationalFun_run ((Ty.prod A B).height) .start)).comp
          ((rtfun_prependSep SymTy).comp
            ((rtfun_split SymTy .one).comp
              (((rtfun_snd (.list SymTy) (.list (.prod .one (.list SymTy)))).comp
                (((rtfun_snd .one (.list SymTy)).comp (rtfun_sumInv hinvA hinvB)).mapList)).comp
                (rtfun_pairOfSumList A B))))), ?_⟩
        rintro ⟨a, b⟩
        rw [reprElt_map_symm, RatComb.pairMarkMach_run]
        have hb : ∀ x ∈ [Sym8.left :: A.repr a, Sym8.right :: B.repr b], x ≠ [] := by
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · simp
          · rcases List.mem_cons.1 hx with rfl | hx
            · simp
            · exact absurd hx (by simp)
        rw [show (optBlocks [Sym8.left :: A.repr a, Sym8.right :: B.repr b]).map optSymEq
              = reprBlocks [Sym8.left :: A.repr a, Sym8.right :: B.repr b] from rfl,
          splitList_reprBlocks _ hb]
        simp only [List.map_cons, List.map_nil]
        rw [show List.map (⇑symEq) (A.repr a) = reprElt A a from rfl,
          show List.map (⇑symEq) (B.repr b) = reprElt B b from rfl,
          sumInv_repr_left (invB := invB) (hinvAe a),
          sumInv_repr_right (invA := invA) (hinvBe b)]
        exact pairOfSumList_two A B a b
  | sum A B ihA ihB =>
      obtain ⟨hencA, invA, hinvA, hinvAe⟩ := ihA
      obtain ⟨hencB, invB, hinvB, hinvBe⟩ := ihB
      constructor
      · refine ((rtfun_prependConst hencA [symEq Sym8.left]).copair
          (rtfun_prependConst hencB [symEq Sym8.right])).congr ?_
        rintro (a | b) <;> simp [reprElt]
      · refine ⟨_, rtfun_sumInv hinvA hinvB, ?_⟩
        rintro (a | b)
        · exact sumInv_repr_left (hinvAe a)
        · exact sumInv_repr_right (hinvBe b)
  | list A₀ ih =>
      obtain ⟨hencA, invA, hinvA, hinvAe⟩ := ih
      constructor
      · refine (rtfun_prependConst (rtfun_appendConst
          (((hencA.comp (rtfun_consFixed SymTy (symEq Sym8.comma))).mapList.comp
            (rtfun_concat SymTy)).comp (rtfun_tail SymTy)) [symEq Sym8.rbrack])
            [symEq Sym8.lbrack]).congr ?_
        intro l
        have h1 : (l.map (fun a => symEq Sym8.comma :: reprElt A₀ a)).flatten
            = (commaBlocks A₀ l).map symEq := by
          simp [commaBlocks, reprElt, List.map_flatten, List.map_map, Function.comp_def]
        rw [h1, ← List.map_tail, commaBlocks_tail]
        simp [reprElt, Ty.repr_list]
      · haveI : Finite (Ty.sum SymTy Ty.one).Elt := by
          show Finite (SymTy.Elt ⊕ Unit); infer_instance
        refine ⟨_, (rtfun_ofRationalStrOpt (listMarkMach.isRationalFun_run (listMarkN A₀) .start)).comp
          ((rtfun_prependSep SymTy).comp
            ((rtfun_split SymTy .one).comp
              ((rtfun_snd (.list SymTy) (.list (.prod .one (.list SymTy)))).comp
                (((rtfun_snd .one (.list SymTy)).comp hinvA).mapList)))), ?_⟩
        intro l
        rw [reprElt_map_symm, listMarkMach_run]
        have hb : ∀ x ∈ l.map A₀.repr, x ≠ [] := by
          intro x hx
          obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
          obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A₀ a
          rw [hcw]
          simp
        rw [show (optBlocks (l.map A₀.repr)).map optSymEq = reprBlocks (l.map A₀.repr) from rfl,
          splitList_reprBlocks (l.map A₀.repr) hb]
        simp only [List.map_map, Function.comp_def]
        calc List.map (fun x : A₀.Elt => invA ((A₀.repr x).map symEq)) l
            = List.map (fun x : A₀.Elt => x) l := List.map_congr_left (fun a _ => hinvAe a)
          _ = l := List.map_id' l

/-! ## Theorem `thm:rational-terms` -/

/-- Every type-to-type function that is rational under string representation is defined by a
rational term. -/
theorem ratTerm_of_isRational {A B : Ty} {f : A.Elt → B.Elt} (h : IsRationalUnderRepr f) :
    IsRatTermFun f := by
  obtain ⟨f', hf'r, hf'e⟩ := h
  obtain ⟨hencA, -⟩ := rat_terms_define_string_representation A
  obtain ⟨-, invB, hinvB, hinvBe⟩ := rat_terms_define_string_representation B
  refine ((hencA.comp (rtfun_ofRationalStr hf'r)).comp hinvB).congr ?_
  intro a
  dsimp only
  rw [reprElt_map_symm, hf'e a]
  exact hinvBe (f a)

/-- **Theorem `thm:rational-terms`.**  A type-to-type function is rational under string
representation if and only if it is defined by some rational term. -/
theorem rational_iff_rationalTerm {A B : Ty} (f : A.Elt → B.Elt) :
    IsRationalUnderRepr f ↔ IsRatTermFun f :=
  ⟨ratTerm_of_isRational, ratTerm_isRational⟩

end Transducers
