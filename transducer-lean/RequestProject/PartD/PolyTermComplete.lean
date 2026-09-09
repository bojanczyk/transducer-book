/-
Part D: expressive completeness of the polyregular terms -- the converse direction of Theorem
`thm:polyregular-terms`.

The book's proof: "we use the definition of polyregular functions in terms of compositions of
primes from `def:polyregular-functions`; in this case it is enough to show that map squaring can be
expressed using `split`.  This is an easy exercise, which we leave to the reader."  Here it is.
Marked squaring is

    [a₁,…,aₙ] ↦ a₁ a₂ ⋯ aₙ  a₁ a₂ ⋯ aₙ  ⋯  a₁ a₂ ⋯ aₙ,

the `i`-th copy having its first `i` letters underlined, and the list of pairs produced by the new
atomic function of Definition `def:polyregular-terms` is, read backwards and with its first entry
`([],[a₁,…,aₙ])` removed, exactly the list of the `n` copies, described by the prefix that is
underlined and the suffix that is not.  So

    marked squaring = split ; reverse ; tail ; (underline × don't) ; concatenate the pair ; flatten,

and all of the terms other than `split` are regular terms (`Transducers.tfun_tail` and
`Transducers.tfun_append` of `RequestProject/PartC/CombDerived.lean`).  That is
`Transducers.isPolyregularTermFun_markedSquare`.

The rest of the file is the interface between string-to-string functions and terms, copied from
`RequestProject/PartC/CombStrFam.lean` with "regular" replaced by "polyregular"
(`Transducers.PolyTermStrFun`), and the assembly: every polyregular string-to-string function is
definable by a polyregular term, hence so is every type-to-type function that is polyregular under
string representation, because the string representation and a one-sided inverse of it are
definable by *regular* terms (Lemma `lem:terms-define-string-representation`).
-/
import RequestProject.PartD.PolyTermEasy

namespace Transducers

/-! ## Marked squaring is definable using the new atomic function -/

/-- Marked squaring, as a function on the elements of a list type, is defined by a polyregular
term.  This is the step that the book leaves to the reader. -/
theorem isPolyregularTermFun_markedSquare (T : Ty) :
    IsPolyregularTermFun (A := .list T) (B := .list (.sum T T))
      (fun l => markedSquare T.Elt l) := by
  have hsplits : IsPolyregularTermFun (A := .list T) (B := .list (.prod (.list T) (.list T)))
      (fun l => splitsList l) := IsPolyregularTermFun.of_term (PolyTerm.splits T)
  have hrev : IsPolyregularTermFun (A := .list (.prod (.list T) (.list T)))
      (B := .list (.prod (.list T) (.list T))) (fun l => l.reverse) :=
    IsPolyregularTermFun.of_regularTerm (tfun_reverse (.prod (.list T) (.list T)))
  have htail : IsPolyregularTermFun (A := .list (.prod (.list T) (.list T)))
      (B := .list (.prod (.list T) (.list T))) (fun l => l.tail) :=
    IsPolyregularTermFun.of_regularTerm (tfun_tail (.prod (.list T) (.list T)))
  have hentry : IsPolyregularTermFun (A := .prod (.list T) (.list T)) (B := .list (.sum T T))
      (fun p => p.1.map Sum.inl ++ p.2.map Sum.inr) :=
    IsPolyregularTermFun.of_regularTerm
      ((tfun_prodMap ((tfun_inl T T).mapList) ((tfun_inr T T).mapList)).comp
        (tfun_append (.sum T T)))
  have hconcat : IsPolyregularTermFun (A := .list (.list (.sum T T))) (B := .list (.sum T T))
      (fun l => l.flatten) := IsPolyregularTermFun.of_regularTerm (tfun_concat (.sum T T))
  refine ((((hsplits.comp hrev).comp htail).comp hentry.mapList).comp hconcat).congr ?_
  intro l
  show ((((splitsList l).reverse).tail.map
    (fun p => p.1.map Sum.inl ++ p.2.map Sum.inr)).flatten) = markedSquare T.Elt l
  rw [splitsList_reverse, show List.range (l.length + 1)
    = 0 :: (List.range l.length).map Nat.succ from List.range_succ_eq_map]
  simp only [List.map_cons, List.tail_cons, List.map_map, Function.comp_def]
  rfl

/-! ## String-to-string functions definable by polyregular terms -/

/-- A string-to-string function between finite alphabets is **definable by polyregular terms** if,
whichever types are used to name the two alphabets, the corresponding function between the two list
types is defined by a polyregular term.  This is `Transducers.TermStrFun` with "regular" replaced
by "polyregular". -/
def PolyTermStrFun {X Y : Type} (g : List X → List Y) : Prop :=
  ∀ (A B : Ty), Finite A.Elt → Finite B.Elt → ∀ (eA : A.Elt ≃ X) (eB : Y ≃ B.Elt),
    IsPolyregularTermFun (A := .list A) (B := .list B) (fun l => (g (l.map eA)).map eB)

/-- Definability by polyregular terms only depends on the function. -/
lemma PolyTermStrFun.congr {X Y : Type} {g g' : List X → List Y} (h : PolyTermStrFun g)
    (hgg : ∀ w, g w = g' w) : PolyTermStrFun g' := by
  intro A B hA hB eA eB
  exact (h A B hA hB eA eB).congr (fun l => by rw [hgg])

/-- A function definable by regular terms is definable by polyregular terms. -/
lemma TermStrFun.polyTermStrFun {X Y : Type} {g : List X → List Y} (h : TermStrFun g) :
    PolyTermStrFun g :=
  fun A B hA hB eA eB => IsPolyregularTermFun.of_regularTerm (h A B hA hB eA eB)

/-- A letter-to-letter renaming of a list, as a polyregular term. -/
lemma ptfun_mapRen {A B : Ty} (hA : Finite A.Elt) (h : A.Elt → B.Elt) :
    IsPolyregularTermFun (A := .list A) (B := .list B) (fun l => l.map h) :=
  IsPolyregularTermFun.of_regularTerm (tfun_mapRen hA h)

/-- **One naming of the alphabets suffices.** -/
lemma polyTermStrFun_of_one {X Y : Type} {g : List X → List Y}
    (A B : Ty) (hB : Finite B.Elt) (eA : A.Elt ≃ X) (eB : Y ≃ B.Elt)
    (h : IsPolyregularTermFun (A := .list A) (B := .list B) (fun l => (g (l.map eA)).map eB)) :
    PolyTermStrFun g := by
  intro A' B' hA' hB' eA' eB'
  have hrho := ptfun_mapRen hA' (fun a => eA.symm (eA' a))
  have hsigma := ptfun_mapRen hB (fun b => eB' (eB.symm b))
  refine ((hrho.comp h).comp hsigma).congr ?_
  intro l
  simp [List.map_map, Function.comp_def]

/-- If the input alphabet is empty then `PolyTermStrFun` is vacuously true. -/
lemma polyTermStrFun_of_isEmpty_dom {X Y : Type} (g : List X → List Y) (h : IsEmpty X) :
    PolyTermStrFun g := by
  intro A _ _ _ eA _
  exact (h.false (eA default)).elim

/-- If the output alphabet is empty then `PolyTermStrFun` is vacuously true. -/
lemma polyTermStrFun_of_isEmpty_cod {X Y : Type} (g : List X → List Y) (h : IsEmpty Y) :
    PolyTermStrFun g := by
  intro _ B _ _ _ eB
  exact (h.false (eB.symm default)).elim

lemma polyTermStrFun_id (X : Type) : PolyTermStrFun (fun w : List X => w) :=
  (termStrFun_id X).polyTermStrFun

lemma polyTermStrFun_const {X Y : Type} (v : List Y) : PolyTermStrFun (fun _ : List X => v) :=
  (termStrFun_const v).polyTermStrFun

lemma PolyTermStrFun.comp {X Y Z : Type} [Finite Y] {g₁ : List X → List Y} {g₂ : List Y → List Z}
    (h₁ : PolyTermStrFun g₁) (h₂ : PolyTermStrFun g₂) : PolyTermStrFun (fun w => g₂ (g₁ w)) := by
  by_cases hY : Nonempty Y
  · haveI := hY
    obtain ⟨B, ⟨eB⟩, hB⟩ := exists_ty_equiv Y
    intro A C hA hC eA eC
    have k₁ := h₁ A B hA hB eA eB
    have k₂ := h₂ B C hB hC eB.symm eC
    refine (k₁.comp k₂).congr ?_
    intro l
    simp [List.map_map, Function.comp_def]
  · have hg1 : ∀ w, g₁ w = [] := by
      intro w
      cases hw : g₁ w with
      | nil => rfl
      | cons y _ => exact absurd ⟨y⟩ hY
    exact (polyTermStrFun_const (X := X) (g₂ [])).congr (fun w => by rw [hg1])

/-- **A composition closure is covered as soon as its primes are.** -/
theorem polyTermStrFun_of_compClosure {P : ∀ (A B : Type), (List A → List B) → Prop}
    (hP : ∀ {X Y : Type} {g : List X → List Y}, Finite X → Finite Y → P X Y g →
      PolyTermStrFun g) :
    ∀ {X Y : Type} {g : List X → List Y}, CompClosure P X Y g → Finite X → Finite Y →
      PolyTermStrFun g := by
  intro X Y g h
  induction h with
  | base hf => intro hX hY; exact hP hX hY hf
  | id X => intro _ _; exact polyTermStrFun_id X
  | @comp X Y Z hY f g _ _ ihf ihg =>
      intro hX hZ
      exact ((ihf hX hY).comp (ihg hY hZ)).congr (fun _ => rfl)

/-! ## The primes -/

/-- Marked squaring, as a string-to-string function, is definable by polyregular terms. -/
theorem polyTermStrFun_markedSquare {X Y : Type} [Finite X] [Finite Y] (A₀ : Type) [Finite A₀]
    (e : X ≃ A₀) (e' : Y ≃ A₀ ⊕ A₀) :
    PolyTermStrFun (fun w : List X => (markedSquare A₀ (w.map e)).map e'.symm) := by
  by_cases hX : Nonempty X
  · haveI := hX
    haveI : Nonempty A₀ := ⟨e (Classical.arbitrary X)⟩
    obtain ⟨T, ⟨eT⟩, hT⟩ := exists_ty_equiv A₀
    haveI := hT
    haveI hTT : Finite (Ty.sum T T).Elt := by
      show Finite (T.Elt ⊕ T.Elt); infer_instance
    refine polyTermStrFun_of_one (X := X) (Y := Y) T (.sum T T) hTT (eT.symm.trans e.symm)
      (e'.trans (Equiv.sumCongr eT eT)) ?_
    refine (isPolyregularTermFun_markedSquare T).congr ?_
    intro l
    show markedSquare T.Elt l
      = ((markedSquare A₀ ((l.map (eT.symm.trans e.symm)).map e)).map e'.symm).map
          (e'.trans (Equiv.sumCongr eT eT))
    have h1 : (l.map (eT.symm.trans e.symm)).map e = l.map eT.symm := by
      simp [List.map_map, Function.comp_def]
    rw [h1, markedSquare_map, List.map_map, List.map_map]
    have h2 : ∀ x : T.Elt ⊕ T.Elt,
        (e'.trans (Equiv.sumCongr eT eT)) (e'.symm (Sum.map eT.symm eT.symm x)) = x := by
      intro x; cases x <;> simp
    calc markedSquare T.Elt l = (markedSquare T.Elt l).map id := by simp
      _ = _ := List.map_congr_left (fun x _ => (h2 x).symm)
  · exact polyTermStrFun_of_isEmpty_dom _ (not_nonempty_iff.mp hX)

/-- **Every polyregular string-to-string function is definable by a polyregular term.** -/
theorem polyTermStrFun_of_isPolyregular {X Y : Type} {g : List X → List Y}
    (h : IsPolyregular g) (hX : Finite X) (hY : Finite Y) : PolyTermStrFun g := by
  refine polyTermStrFun_of_compClosure (P := PolyregularFam) ?_ h hX hY
  intro X' Y' g' hX' hY' hp
  haveI := hX'; haveI := hY'
  rcases hp with hreg | ⟨A₀, e, e', hge⟩
  · exact (termStrFun_of_isRegularFun hreg hX' hY').polyTermStrFun
  · haveI : Finite A₀ := Finite.of_equiv X' e
    exact (polyTermStrFun_markedSquare A₀ e e').congr (fun w => (hge w).symm)

/-! ## The converse direction of Theorem `thm:polyregular-terms` -/

/-- A polyregular function on strings over the eight-letter alphabet is definable by a polyregular
term. -/
lemma ptfun_ofPolyregularStr {f : List Sym8 → List Sym8} (hf : IsPolyregular f) :
    IsPolyregularTermFun (A := .list SymTy) (B := .list SymTy)
      (fun l => (f (l.map symEq.symm)).map symEq) :=
  polyTermStrFun_of_isPolyregular hf inferInstance inferInstance SymTy SymTy inferInstance
    inferInstance symEq.symm symEq

/-- **The converse direction of Theorem `thm:polyregular-terms`.**  Every type-to-type function
that is polyregular under string representation is defined by a polyregular term. -/
theorem polyregularTerm_of_isPolyregular {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsPolyregularUnderRepr f) : IsPolyregularTermFun f := by
  obtain ⟨f', hf'r, hf'e⟩ := h
  obtain ⟨hencA, -⟩ := terms_define_string_representation A
  obtain ⟨-, invB, hinvB, hinvBe⟩ := terms_define_string_representation B
  refine (((IsPolyregularTermFun.of_regularTerm hencA).comp (ptfun_ofPolyregularStr hf'r)).comp
    (IsPolyregularTermFun.of_regularTerm hinvB)).congr ?_
  intro a
  dsimp only
  rw [reprElt_map_symm, hf'e a]
  exact hinvBe (f a)

end Transducers
