/-
Lemma `lem:terms-define-string-representation` of Section *Combinators* of *Transducers*
(M. Bojańczyk), and with it the converse direction of Theorem `thm:regular-terms`.

For every type, its string representation and a one-sided inverse of it are definable by regular
terms.  The representation itself is a straightforward induction.  For the inverse, the book uses,
at each type constructor, the expressive completeness of terms for string-to-string functions that
was proved in `CombComplete.lean`:

* for a product, the two regular functions that the *easy* direction of the theorem already
  provides, namely those that implement the two projections under string representation
  (`Transducers.isRegularUnderRepr_fst` and `Transducers.isRegularUnderRepr_snd`), cut the
  representation of a pair into the representations of its two coordinates;
* for a co-product, no machine is needed at all: the first letter of the representation is `L` or
  `R` and the rest is the representation of the component, so the list deconstructor and a finite
  case distinction suffice;
* for a list, the marking machine of `CombMark.lean` replaces the top-level commas of the
  representation by a fresh separator and deletes the outer brackets, and then the split function
  of Example `ex:split` cuts the string into the representations of the entries.  A separator is
  prepended first, by a term, so that the first entry is also a block of the split -- with that,
  the empty list and a one-element list are treated by the same term.

Claim `claim:head` -- which the book uses for the product case -- is `Transducers.claim_head` in
`CombDerived.lean`; the route taken here for products does not need it, but it is proved there all
the same.
-/
import RequestProject.PartC.CombComplete
import RequestProject.PartC.CombMark
import RequestProject.PartC.CombAtomProj
import RequestProject.PartC.CombStatements

namespace Transducers

open Comb

instance : Inhabited Sym8 := ⟨Sym8.one⟩

/-! ## A type whose elements are the eight letters -/

/-- A type whose set of elements is the book's eight-letter alphabet. -/
noncomputable def SymTy : Ty := (exists_ty_equiv Sym8).choose

/-- The naming of the eight letters by the elements of `Transducers.SymTy`. -/
noncomputable def symEq : Sym8 ≃ SymTy.Elt := ((exists_ty_equiv Sym8).choose_spec.1).some

instance instFiniteSymTy : Finite SymTy.Elt := (exists_ty_equiv Sym8).choose_spec.2

/-- The string representation, as a list over `Transducers.SymTy`. -/
noncomputable def reprElt (A : Ty) (a : A.Elt) : List SymTy.Elt := (A.repr a).map symEq

lemma reprElt_map_symm (A : Ty) (a : A.Elt) : (reprElt A a).map symEq.symm = A.repr a := by
  simp [reprElt, List.map_map, Function.comp_def]

/-- The naming of `Option Sym8` by the elements of `SymTy + 1`. -/
noncomputable def optSymEq : Option Sym8 ≃ (Ty.sum SymTy Ty.one).Elt :=
  (Equiv.optionCongr symEq).trans (sumOptEquiv SymTy.Elt).symm

@[simp] lemma optSymEq_some (c : Sym8) : optSymEq (some c) = Sum.inl (symEq c) := rfl

@[simp] lemma optSymEq_none : optSymEq none = Sum.inr () := rfl

/-! ## Regular string functions as terms -/

/-- A regular function on strings over the eight-letter alphabet is definable by a term. -/
lemma tfun_ofRegularStr {f : List Sym8 → List Sym8} (hf : IsRegularFun f) :
    IsRegularTermFun (A := .list SymTy) (B := .list SymTy)
      (fun l => (f (l.map symEq.symm)).map symEq) :=
  termStrFun_of_isRegularFun hf inferInstance inferInstance SymTy SymTy inferInstance
    inferInstance symEq.symm symEq

/-- The same, for a regular function whose output alphabet is `Option Sym8`. -/
lemma tfun_ofRegularStrOpt {f : List Sym8 → List (Option Sym8)} (hf : IsRegularFun f) :
    IsRegularTermFun (A := .list SymTy) (B := .list (.sum SymTy .one))
      (fun l => (f (l.map symEq.symm)).map optSymEq) := by
  haveI : Finite (Ty.sum SymTy Ty.one).Elt := by
    show Finite (SymTy.Elt ⊕ Unit); infer_instance
  exact termStrFun_of_isRegularFun hf inferInstance inferInstance SymTy (.sum SymTy .one)
    inferInstance inferInstance symEq.symm optSymEq

/-! ## Two derived terms -/

/-- Two terms into a list type, concatenated. -/
lemma tfun_appendPair {A T : Ty} {u v : A.Elt → List T.Elt}
    (hu : IsRegularTermFun (A := A) (B := .list T) u)
    (hv : IsRegularTermFun (A := A) (B := .list T) v) :
    IsRegularTermFun (A := A) (B := .list T) (fun a => u a ++ v a) :=
  (hu.pair hv).comp (tfun_append T)

/-- Prepending the separator to a nonempty string over `T + 1`, and doing nothing to the empty
string. -/
def prependSep {T : Ty} : List (Ty.sum T Ty.one).Elt → List (Ty.sum T Ty.one).Elt
  | [] => []
  | x :: r => Sum.inr () :: x :: r

@[simp] lemma prependSep_nil {T : Ty} : prependSep ([] : List (Ty.sum T Ty.one).Elt) = [] := rfl

@[simp] lemma prependSep_cons {T : Ty} (x : (Ty.sum T Ty.one).Elt)
    (r : List (Ty.sum T Ty.one).Elt) : prependSep (x :: r) = Sum.inr () :: x :: r := rfl

lemma tfun_prependSep (T : Ty) :
    IsRegularTermFun (A := .list (.sum T .one)) (B := .list (.sum T .one)) prependSep := by
  set U : Ty := .sum T .one with hU
  refine ((tfun_uncons U).comp ((tfun_const .one (.list U) []).copair
    ((tfun_inr .one (.prod U (.list U))).comp
      ((tfun_cons U).comp (tfun_consFixed U (Sum.inr ())))))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons x r => rfl

/-! ## The inverse for a co-product -/

open Classical in
/-- The branch of the inverse of the representation of a co-product, once the first letter of the
input has been read. -/
noncomputable def sumInvFun (A B : Ty) (fa : List SymTy.Elt → A.Elt)
    (fb : List SymTy.Elt → B.Elt) (x : SymTy.Elt) (rest : List SymTy.Elt) : (Ty.sum A B).Elt :=
  if x = symEq Sym8.left then Sum.inl (fa rest)
  else if x = symEq Sym8.right then Sum.inr (fb rest) else default

lemma tfun_sumInvFun {A B : Ty} {fa : List SymTy.Elt → A.Elt} {fb : List SymTy.Elt → B.Elt}
    (hfa : IsRegularTermFun (A := .list SymTy) (B := A) fa)
    (hfb : IsRegularTermFun (A := .list SymTy) (B := B) fb) (x : SymTy.Elt) :
    IsRegularTermFun (A := .list SymTy) (B := .sum A B) (sumInvFun A B fa fb x) := by
  classical
  by_cases h1 : x = symEq Sym8.left
  · refine (hfa.comp (tfun_inl A B)).congr ?_
    intro rest
    rw [sumInvFun, if_pos h1]
  · by_cases h2 : x = symEq Sym8.right
    · refine (hfb.comp (tfun_inr A B)).congr ?_
      intro rest
      rw [sumInvFun, if_neg h1, if_pos h2]
    · refine (tfun_const (.list SymTy) (.sum A B) default).congr ?_
      intro rest
      rw [sumInvFun, if_neg h1, if_neg h2]

/-! ## The inverse for a list -/

lemma splitList_map_inl_append {α β : Type} :
    ∀ (u : List α) (v : List (α ⊕ β)),
      splitList (u.map Sum.inl ++ v) = (u ++ (splitList v).1, (splitList v).2) := by
  intro u
  induction u with
  | nil => intro v; simp
  | cons a u ih =>
      intro v
      rw [List.map_cons, List.cons_append, splitList_inl, ih v]
      rfl

/-- The blocks of a marked list representation, over the type `SymTy + 1`. -/
noncomputable def reprBlocks (xs : List (List Sym8)) : List (Ty.sum SymTy Ty.one).Elt :=
  (optBlocks xs).map optSymEq

/-- The part of `Transducers.reprBlocks` that follows the first block. -/
noncomputable def reprBlocksTail (xs : List (List Sym8)) : List (Ty.sum SymTy Ty.one).Elt :=
  (optBlocksTail xs).map optSymEq

/-- The marking of a single block. -/
noncomputable def reprBlockHead (x : List Sym8) : List (Ty.sum SymTy Ty.one).Elt :=
  (x.map symEq).map Sum.inl

@[simp] lemma reprBlocks_nil : reprBlocks [] = [] := rfl

@[simp] lemma reprBlocksTail_nil : reprBlocksTail [] = [] := rfl

lemma reprBlocksTail_cons (y : List Sym8) (r : List (List Sym8)) :
    reprBlocksTail (y :: r) = Sum.inr () :: reprBlocks (y :: r) := by
  unfold reprBlocksTail reprBlocks
  rw [optBlocksTail_cons, List.map_cons]
  rfl

lemma reprBlocks_cons (x : List Sym8) (xs : List (List Sym8)) :
    reprBlocks (x :: xs) = reprBlockHead x ++ reprBlocksTail xs := by
  unfold reprBlocks reprBlocksTail reprBlockHead
  rw [optBlocks_cons, List.map_append]
  congr 1
  simp [List.map_map, Function.comp_def]

lemma reprBlockHead_ne_nil {x : List Sym8} (hx : x ≠ []) : reprBlockHead x ≠ [] := by
  simpa [reprBlockHead] using hx

lemma prependSep_reprBlocks_cons {x : List Sym8} (hx : x ≠ []) (xs : List (List Sym8)) :
    prependSep (reprBlocks (x :: xs)) = Sum.inr () :: reprBlocks (x :: xs) := by
  obtain ⟨y, r, hyr⟩ := List.exists_cons_of_ne_nil (reprBlockHead_ne_nil hx)
  rw [reprBlocks_cons, hyr, List.cons_append, prependSep_cons]

lemma splitList_reprBlocks :
    ∀ (xs : List (List Sym8)), (∀ x ∈ xs, x ≠ []) →
      splitList (prependSep (reprBlocks xs)) = ([], xs.map (fun r => ((), r.map symEq))) := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro hne
      have hx : x ≠ [] := hne x (by simp)
      have hxs : ∀ y ∈ xs, y ≠ [] := fun y hy => hne y (by simp [hy])
      rw [prependSep_reprBlocks_cons hx, splitList_inr, reprBlocks_cons,
        show reprBlockHead x = (x.map symEq).map Sum.inl from rfl, splitList_map_inl_append]
      cases xs with
      | nil => simp [splitList]
      | cons y r =>
          have hih := ih hxs
          rw [prependSep_reprBlocks_cons (hxs y (by simp)), splitList_inr] at hih
          have h2 : ((), (splitList (reprBlocks (y :: r))).1) :: (splitList (reprBlocks (y :: r))).2
              = (y :: r).map (fun z => ((), z.map symEq)) := congrArg Prod.snd hih
          rw [reprBlocksTail_cons, splitList_inr]
          simp only [List.append_nil, List.map_cons]
          rw [h2]
          simp

/-! ## Lemma `lem:terms-define-string-representation` -/

/-- **Lemma `lem:terms-define-string-representation`.**  For every type, its string
representation and a one-sided inverse of it are definable by regular terms. -/
theorem terms_define_string_representation :
    ∀ A : Ty, IsRegularTermFun (A := A) (B := .list SymTy) (reprElt A) ∧
      ∃ inv : List SymTy.Elt → A.Elt,
        IsRegularTermFun (A := .list SymTy) (B := A) inv ∧ ∀ a : A.Elt, inv (reprElt A a) = a := by
  intro A
  induction A with
  | one =>
      refine ⟨(tfun_const .one (.list SymTy) [symEq Sym8.one]).congr (fun a => by
        cases a; rfl),
        ⟨fun _ => (), tfun_const (Ty.list SymTy) Ty.one (), fun a => by cases a; rfl⟩⟩
  | prod A B ihA ihB =>
      obtain ⟨hencA, invA, hinvA, hinvAe⟩ := ihA
      obtain ⟨hencB, invB, hinvB, hinvBe⟩ := ihB
      constructor
      · refine (tfun_appendPair (tfun_const _ _ [symEq Sym8.lpar])
          (tfun_appendPair ((tfun_fst A B).comp hencA)
            (tfun_appendPair (tfun_const _ _ [symEq Sym8.comma])
              (tfun_appendPair ((tfun_snd A B).comp hencB)
                (tfun_const _ _ [symEq Sym8.rpar]))))).congr ?_
        rintro ⟨a, b⟩
        simp [reprElt, Ty.repr_prod]
      · obtain ⟨f₁, hf₁r, hf₁e⟩ := isRegularUnderRepr_fst A B
        obtain ⟨f₂, hf₂r, hf₂e⟩ := isRegularUnderRepr_snd A B
        refine ⟨_,
          ((tfun_ofRegularStr hf₁r).comp hinvA).pair ((tfun_ofRegularStr hf₂r).comp hinvB), ?_⟩
        rintro ⟨a, b⟩
        rw [reprElt_map_symm, hf₁e (a, b), hf₂e (a, b)]
        exact Prod.ext (hinvAe a) (hinvBe b)
  | sum A B ihA ihB =>
      obtain ⟨hencA, invA, hinvA, hinvAe⟩ := ihA
      obtain ⟨hencB, invB, hinvB, hinvBe⟩ := ihB
      constructor
      · refine ((tfun_appendPair (tfun_const _ _ [symEq Sym8.left]) hencA).copair
          (tfun_appendPair (tfun_const _ _ [symEq Sym8.right]) hencB)).congr ?_
        rintro (a | b) <;> simp [reprElt]
      · refine ⟨_, (tfun_uncons SymTy).comp
          ((tfun_const .one (.sum A B) default).copair
            (tfun_finCases instFiniteSymTy (tfun_sumInvFun hinvA hinvB))), ?_⟩
        rintro (a | b)
        · show sumInvFun A B invA invB (symEq Sym8.left) (reprElt A a) = _
          rw [sumInvFun, if_pos rfl, hinvAe]
        · have hne : symEq Sym8.right ≠ symEq Sym8.left := by
            intro h
            exact absurd (symEq.injective h) (by decide)
          show sumInvFun A B invA invB (symEq Sym8.right) (reprElt B b) = _
          rw [sumInvFun, if_neg hne, if_pos rfl, hinvBe]
  | list A₀ ih =>
      obtain ⟨hencA, invA, hinvA, hinvAe⟩ := ih
      constructor
      · refine (tfun_appendPair (tfun_const _ _ [symEq Sym8.lbrack])
          (tfun_appendPair
            (((hencA.comp (tfun_consFixed SymTy (symEq Sym8.comma))).mapList.comp
              (tfun_concat SymTy)).comp (tfun_tail SymTy))
            (tfun_const _ _ [symEq Sym8.rbrack]))).congr ?_
        intro l
        have h1 : (l.map (fun a => symEq Sym8.comma :: reprElt A₀ a)).flatten
            = (commaBlocks A₀ l).map symEq := by
          simp [commaBlocks, reprElt, List.map_flatten, List.map_map, Function.comp_def]
        rw [h1, ← List.map_tail, commaBlocks_tail]
        simp [reprElt, Ty.repr_list]
      · refine ⟨_, (tfun_ofRegularStrOpt (isRegularFun_listMarkRun A₀)).comp
          ((tfun_prependSep SymTy).comp
            ((tfun_split SymTy .one).comp
              ((tfun_snd (.list SymTy) (.list (.prod .one (.list SymTy)))).comp
                (((tfun_snd .one (.list SymTy)).comp hinvA).mapList)))), ?_⟩
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

/-! ## Theorem `thm:regular-terms` -/

/-- **The converse direction of Theorem `thm:regular-terms`.**  Every type-to-type function that
is regular under string representation is defined by a regular term. -/
theorem regularTerm_of_isRegular {A B : Ty} {f : A.Elt → B.Elt} (h : IsRegularUnderRepr f) :
    IsRegularTermFun f := by
  obtain ⟨f', hf'r, hf'e⟩ := h
  obtain ⟨hencA, -⟩ := terms_define_string_representation A
  obtain ⟨-, invB, hinvB, hinvBe⟩ := terms_define_string_representation B
  refine ((hencA.comp (tfun_ofRegularStr hf'r)).comp hinvB).congr ?_
  intro a
  dsimp only
  rw [reprElt_map_symm, hf'e a]
  exact hinvBe (f a)

/-- **Theorem `thm:regular-terms`.**  A type-to-type function is regular under string
representation if and only if it is defined by some regular term. -/
theorem regular_iff_regularTerm {A B : Ty} (f : A.Elt → B.Elt) :
    IsRegularUnderRepr f ↔ IsRegularTermFun f :=
  ⟨regularTerm_of_isRegular, regularTerm_isRegular⟩

end Transducers
