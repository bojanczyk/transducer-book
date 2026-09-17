/-
Five exercises of Section *Combinators* of *Transducers* (M. Bojańczyk), all of them constructions
in the language of regular (and rational) terms of Definition `def:regular-terms`.

* Exercise `exer:filter-plus`: a regular term of type `(A + B)* → A*` that keeps only the entries
  of type `A`.
* Exercise `exer:if-then-else`: the functions defined by regular terms, and the functions defined
  by rational terms, are closed under the conditional construction.
* Exercise `exer:identity-function-replacement`: the general identity `A → A` may be replaced by
  its special case at `A = 1`, and in fact dropped altogether.
* Exercise `exer:group-prefix-multiplication-isomorphism`: group prefix multiplication is a
  bijection, and its inverse is again defined by a regular term.
* Exercise `exer:windows-of-size-two`: a regular term of type `A* → (A × A)*` that outputs the
  windows of size two of its input.

Everything is stated for the term language of `RequestProject/PartC/CombTerms.lean`
(`Transducers.RegTerm`, `Transducers.RegTerm.eval`) and its rational fragment in
`RequestProject/PartC/RatTerms.lean` (`Transducers.RatTerm`), and uses the toolbox of derived
combinators of `RequestProject/PartC/CombDerived.lean`.
-/
import RequestProject.PartC.CombDerived
import RequestProject.PartC.RatRepr
import RequestProject.PartC.RatTools
import RequestProject.PartB.RationalStatements
import RequestProject.Exercises.IntroAux

namespace Transducers
namespace Exercises

open Transducers

/-! ## Exercise `exer:if-then-else`: the conditional -/

/-- The Booleans as the book reads them: the type `1 + 1`.  The convention taken here is that
`Sum.inl ()` is *true* and `Sum.inr ()` is *false*. -/
abbrev boolTy : Ty := .sum .one .one

/-- The conditional construction of Exercise `exer:if-then-else`: `a` is mapped to `f₁ a` when
`f a` is true, and to `f₂ a` when it is false. -/
def condFun {A B : Ty} (f : A.Elt → boolTy.Elt) (f₁ f₂ : A.Elt → B.Elt) (a : A.Elt) : B.Elt :=
  Sum.elim (fun _ => f₁ a) (fun _ => f₂ a) (f a)

/-- **Exercise `exer:if-then-else`, for regular terms.**  The functions defined by regular terms
are closed under the conditional construction.

This is the author's composition:
`A → A × (1 + 1) → (A × 1) + (A × 1) → A + A → B`, that is, pairing with the test, followed by
distributivity, the two projections and the co-pairing of the two branches. -/
theorem regTerm_ite {A B : Ty} {f : A.Elt → boolTy.Elt} {f₁ f₂ : A.Elt → B.Elt}
    (hf : IsRegularTermFun f) (h₁ : IsRegularTermFun f₁) (h₂ : IsRegularTermFun f₂) :
    IsRegularTermFun (condFun f f₁ f₂) := by
  have hpair : IsRegularTermFun (A := A) (B := .prod A boolTy) (fun a => (a, f a)) :=
    (tfun_id A).pair hf
  have hbranch : IsRegularTermFun (A := .sum (.prod A .one) (.prod A .one)) (B := B)
      (Sum.elim (fun p => f₁ p.1) (fun p => f₂ p.1)) :=
    ((tfun_fst A .one).comp h₁).copair ((tfun_fst A .one).comp h₂)
  refine ((hpair.comp (tfun_distr A .one .one)).comp hbranch).congr ?_
  intro a
  cases h : f a with
  | inl u => simp [condFun, h]
  | inr u => simp [condFun, h]

/-- **Exercise `exer:if-then-else`, for rational terms.**  The functions defined by rational terms
are closed under the conditional construction as well.

Pairing is not available in the rational fragment, so this is the author's indirect argument: by
Theorem `thm:rational-terms` the functions defined by rational terms are exactly the functions
that are rational under string representation, and that class is closed under the conditional.
The string function is a case distinction over the regular language of the strings that the test
sends to the representation of *true*; the language is regular because rational relations are
continuous (Theorem `thm:continuity-rational-relations`), and the case distinction is rational by
`Transducers.isRationalFun_ite_lang`. -/
theorem ratTerm_ite {A B : Ty} {f : A.Elt → boolTy.Elt} {f₁ f₂ : A.Elt → B.Elt}
    (hf : IsRatTermFun f) (h₁ : IsRatTermFun f₁) (h₂ : IsRatTermFun f₂) :
    IsRatTermFun (condFun f f₁ f₂) := by
  rw [← rational_iff_rationalTerm] at hf h₁ h₂ ⊢
  obtain ⟨f', hf'r, hf'e⟩ := hf
  obtain ⟨g₁, hg₁r, hg₁e⟩ := h₁
  obtain ⟨g₂, hg₂r, hg₂e⟩ := h₂
  set c : List Sym8 := boolTy.repr (Sum.inl ()) with hc
  have hL : Language.IsRegular ({w : List Sym8 | f' w = c} : Language Sym8) := by
    have h := rationalRel_continuous (R := fun (w : List Sym8) (v : List Sym8) => v = f' w) hf'r
      ({c} : Language Sym8) (isRegular_singleton c)
    have hset : {w : List Sym8 | ∃ v, v = f' w ∧ v ∈ ({c} : Language Sym8)}
        = {w : List Sym8 | f' w = c} := by
      ext w
      constructor
      · rintro ⟨v, rfl, hv⟩
        exact hv
      · intro hw
        exact ⟨f' w, rfl, hw⟩
    rwa [hset] at h
  haveI : DecidablePred (fun w => w ∈ ({w : List Sym8 | f' w = c} : Language Sym8)) :=
    fun w => inferInstanceAs (Decidable (f' w = c))
  refine ⟨fun w => if w ∈ ({w : List Sym8 | f' w = c} : Language Sym8) then g₁ w else g₂ w,
    isRationalFun_ite_lang hL hg₁r hg₂r, ?_⟩
  intro a
  have hfa : f' (A.repr a) = boolTy.repr (f a) := hf'e a
  cases h : f a with
  | inl u =>
      have hmem : A.repr a ∈ ({w : List Sym8 | f' w = c} : Language Sym8) := by
        show f' (A.repr a) = c
        rw [hfa, h, hc]
        cases u
        rfl
      simp only [if_pos hmem]
      rw [hg₁e a]
      simp [condFun, h]
  | inr u =>
      have hne : ¬ A.repr a ∈ ({w : List Sym8 | f' w = c} : Language Sym8) := by
        intro hmem
        have : f' (A.repr a) = c := hmem
        rw [hfa, h, hc] at this
        cases u
        exact absurd this (by decide)
      simp only [if_neg hne]
      rw [hg₂e a]
      simp [condFun, h]

/-! ## Exercise `exer:identity-function-replacement`: the identity is not needed -/

/-- The identity on the unit type, built without the identity atom: the right co-projection
`1 → 1 + 1` followed by the co-diagonal `1 + 1 → 1`.  This is the author's solution. -/
def idOneTerm : RegTerm .one .one := (RegTerm.inr .one .one).comp (RegTerm.codiag .one)

@[simp] lemma idOneTerm_eval (x : Ty.one.Elt) : idOneTerm.eval x = x := rfl

/-- The identity on an arbitrary type, built from the identity on the unit type by the three
functoriality combinators.  This is the induction on the structure of the type of the author's
solution. -/
def idTermOf : (A : Ty) → RegTerm A A
  | .one => idOneTerm
  | .prod A B => (idTermOf A).prodMap (idTermOf B)
  | .sum A B => (idTermOf A).sumMap (idTermOf B)
  | .list A => (idTermOf A).map

@[simp] lemma idTermOf_eval : ∀ (A : Ty) (x : A.Elt), (idTermOf A).eval x = x
  | .one, x => by cases x; rfl
  | .prod A B, x => by
      show ((idTermOf A).eval x.1, (idTermOf B).eval x.2) = x
      rw [idTermOf_eval A, idTermOf_eval B]
      rfl
  | .sum A B, x => by
      show Sum.map (idTermOf A).eval (idTermOf B).eval x = x
      cases x with
      | inl a => simp [Sum.map, idTermOf_eval A]
      | inr b => simp [Sum.map, idTermOf_eval B]
  | .list A, l => by
      show l.map (idTermOf A).eval = l
      rw [show (idTermOf A).eval = fun x => x from funext (idTermOf_eval A)]
      simp

/-- A term *uses no identity*: the atom `id` does not occur in it. -/
def IdFree : {A B : Ty} → RegTerm A B → Prop
  | _, _, .id _ => False
  | _, _, .fst _ _ => True
  | _, _, .snd _ _ => True
  | _, _, .inl _ _ => True
  | _, _, .inr _ _ => True
  | _, _, .diag _ => True
  | _, _, .codiag _ => True
  | _, _, .distr _ _ _ => True
  | _, _, .cons _ => True
  | _, _, .uncons _ => True
  | _, _, .reverse _ => True
  | _, _, .concat _ => True
  | _, _, .split _ _ => True
  | _, _, .pref _ _ _ => True
  | _, _, .comp s t => IdFree s ∧ IdFree t
  | _, _, .prodMap s t => IdFree s ∧ IdFree t
  | _, _, .sumMap s t => IdFree s ∧ IdFree t
  | _, _, .map t => IdFree t

/-- A term *uses the identity only at the unit type*: every occurrence of the atom `id` in it is
the identity of the type `1`. -/
def IdOnlyOne : {A B : Ty} → RegTerm A B → Prop
  | _, _, .id A => A = Ty.one
  | _, _, .fst _ _ => True
  | _, _, .snd _ _ => True
  | _, _, .inl _ _ => True
  | _, _, .inr _ _ => True
  | _, _, .diag _ => True
  | _, _, .codiag _ => True
  | _, _, .distr _ _ _ => True
  | _, _, .cons _ => True
  | _, _, .uncons _ => True
  | _, _, .reverse _ => True
  | _, _, .concat _ => True
  | _, _, .split _ _ => True
  | _, _, .pref _ _ _ => True
  | _, _, .comp s t => IdOnlyOne s ∧ IdOnlyOne t
  | _, _, .prodMap s t => IdOnlyOne s ∧ IdOnlyOne t
  | _, _, .sumMap s t => IdOnlyOne s ∧ IdOnlyOne t
  | _, _, .map t => IdOnlyOne t

lemma idFree_idOnlyOne : ∀ {A B : Ty} (t : RegTerm A B), IdFree t → IdOnlyOne t
  | _, _, .id _, h => h.elim
  | _, _, .fst _ _, _ => trivial
  | _, _, .snd _ _, _ => trivial
  | _, _, .inl _ _, _ => trivial
  | _, _, .inr _ _, _ => trivial
  | _, _, .diag _, _ => trivial
  | _, _, .codiag _, _ => trivial
  | _, _, .distr _ _ _, _ => trivial
  | _, _, .cons _, _ => trivial
  | _, _, .uncons _, _ => trivial
  | _, _, .reverse _, _ => trivial
  | _, _, .concat _, _ => trivial
  | _, _, .split _ _, _ => trivial
  | _, _, .pref _ _ _, _ => trivial
  | _, _, .comp s t, h => ⟨idFree_idOnlyOne s h.1, idFree_idOnlyOne t h.2⟩
  | _, _, .prodMap s t, h => ⟨idFree_idOnlyOne s h.1, idFree_idOnlyOne t h.2⟩
  | _, _, .sumMap s t, h => ⟨idFree_idOnlyOne s h.1, idFree_idOnlyOne t h.2⟩
  | _, _, .map t, h => idFree_idOnlyOne t h

lemma idOneTerm_idFree : IdFree idOneTerm := ⟨trivial, trivial⟩

lemma idTermOf_idFree : ∀ A : Ty, IdFree (idTermOf A)
  | .one => idOneTerm_idFree
  | .prod A B => ⟨idTermOf_idFree A, idTermOf_idFree B⟩
  | .sum A B => ⟨idTermOf_idFree A, idTermOf_idFree B⟩
  | .list A => idTermOf_idFree A

/-- The rewriting that removes the identity atom from a term: every occurrence of `id A` is
replaced by the term `idTermOf A`, which defines the same function. -/
def elimId : {A B : Ty} → RegTerm A B → RegTerm A B
  | _, _, .id A => idTermOf A
  | _, _, .fst A B => .fst A B
  | _, _, .snd A B => .snd A B
  | _, _, .inl A B => .inl A B
  | _, _, .inr A B => .inr A B
  | _, _, .diag A => .diag A
  | _, _, .codiag A => .codiag A
  | _, _, .distr A B C => .distr A B C
  | _, _, .cons A => .cons A
  | _, _, .uncons A => .uncons A
  | _, _, .reverse A => .reverse A
  | _, _, .concat A => .concat A
  | _, _, .split A B => .split A B
  | _, _, .pref G grp hfin => .pref G grp hfin
  | _, _, .comp s t => (elimId s).comp (elimId t)
  | _, _, .prodMap s t => (elimId s).prodMap (elimId t)
  | _, _, .sumMap s t => (elimId s).sumMap (elimId t)
  | _, _, .map t => (elimId t).map

lemma elimId_idFree : ∀ {A B : Ty} (t : RegTerm A B), IdFree (elimId t)
  | _, _, .id A => idTermOf_idFree A
  | _, _, .fst _ _ => trivial
  | _, _, .snd _ _ => trivial
  | _, _, .inl _ _ => trivial
  | _, _, .inr _ _ => trivial
  | _, _, .diag _ => trivial
  | _, _, .codiag _ => trivial
  | _, _, .distr _ _ _ => trivial
  | _, _, .cons _ => trivial
  | _, _, .uncons _ => trivial
  | _, _, .reverse _ => trivial
  | _, _, .concat _ => trivial
  | _, _, .split _ _ => trivial
  | _, _, .pref _ _ _ => trivial
  | _, _, .comp s t => ⟨elimId_idFree s, elimId_idFree t⟩
  | _, _, .prodMap s t => ⟨elimId_idFree s, elimId_idFree t⟩
  | _, _, .sumMap s t => ⟨elimId_idFree s, elimId_idFree t⟩
  | _, _, .map t => elimId_idFree t

lemma elimId_eval : ∀ {A B : Ty} (t : RegTerm A B), (elimId t).eval = t.eval
  | _, _, .id A => funext (idTermOf_eval A)
  | _, _, .fst _ _ => rfl
  | _, _, .snd _ _ => rfl
  | _, _, .inl _ _ => rfl
  | _, _, .inr _ _ => rfl
  | _, _, .diag _ => rfl
  | _, _, .codiag _ => rfl
  | _, _, .distr _ _ _ => rfl
  | _, _, .cons _ => rfl
  | _, _, .uncons _ => rfl
  | _, _, .reverse _ => rfl
  | _, _, .concat _ => rfl
  | _, _, .split _ _ => rfl
  | _, _, .pref _ _ _ => rfl
  | _, _, .comp s t => by
      funext x
      show (elimId t).eval ((elimId s).eval x) = t.eval (s.eval x)
      rw [elimId_eval s, elimId_eval t]
  | _, _, .prodMap s t => by
      funext p
      show ((elimId s).eval p.1, (elimId t).eval p.2) = (s.eval p.1, t.eval p.2)
      rw [elimId_eval s, elimId_eval t]
  | _, _, .sumMap s t => by
      funext x
      show Sum.map (elimId s).eval (elimId t).eval x = Sum.map s.eval t.eval x
      rw [elimId_eval s, elimId_eval t]
  | _, _, .map t => by
      funext l
      show l.map (elimId t).eval = l.map t.eval
      rw [elimId_eval t]

/-- **Exercise `exer:identity-function-replacement`.**  The general identity `A → A` is not needed
among the atomic terms: every regular term defines the same function as a term in which the
identity is used only at the type `1`, and indeed as a term in which it is not used at all. -/
theorem regTerm_id_replaceable {A B : Ty} (t : RegTerm A B) :
    (∃ s : RegTerm A B, s.eval = t.eval ∧ IdOnlyOne s) ∧
      (∃ s : RegTerm A B, s.eval = t.eval ∧ IdFree s) :=
  ⟨⟨elimId t, elimId_eval t, idFree_idOnlyOne _ (elimId_idFree t)⟩,
    ⟨elimId t, elimId_eval t, elimId_idFree t⟩⟩

/-! ## Exercise `exer:windows-of-size-two`: the windows of size two

The term is exhibited: `Transducers.Exercises.windowsTwoTerm` is a closed expression in the syntax
of Definition `def:regular-terms`, and `Transducers.Exercises.regTerm_windows_two` says that it
computes exactly `Transducers.Exercises.windowsTwo`.  The route is the author's: send every letter
`a` to the two-letter list `[L a, R a]`, concatenate, split at the letters from the right summand,
keep the second component, drop its last entry, and take the head of each block. -/

/-- The windows of size two of a list: `[1,2,3,4] ↦ [(1,2),(2,3),(3,4)]`. -/
def windowsTwo {α : Type} (l : List α) : List (α × α) := l.zip l.tail

example : windowsTwo [1, 2, 3, 4] = [(1, 2), (2, 3), (3, 4)] := rfl

/-! ### Some terms that the construction needs

They are the terms behind the derived combinators of `RequestProject/PartC/CombDerived.lean`,
written out here because the exercise asks for a term rather than for the mere existence of one. -/

/-- The unique term `A → 1`, by induction on the type; this is Claim `claim:bang-definable`. -/
def bangTerm : (A : Ty) → RegTerm A .one
  | .one => idOneTerm
  | .prod A B => (RegTerm.fst A B).comp (bangTerm A)
  | .sum A B => ((bangTerm A).sumMap (bangTerm B)).comp (RegTerm.codiag .one)
  | .list A => (RegTerm.uncons A).comp
      ((idOneTerm.sumMap ((RegTerm.fst A (.list A)).comp (bangTerm A))).comp (RegTerm.codiag .one))

/-- The empty list, as a term `1 → A*`. -/
def nilTerm (A : Ty) : RegTerm .one (.list A) :=
  (RegTerm.inl .one (.prod A (.list A))).comp (RegTerm.cons A)

@[simp] lemma nilTerm_eval (A : Ty) (x : Ty.one.Elt) : (nilTerm A).eval x = [] := rfl

/-- The empty list, as a term `A → B*`. -/
def constNilTerm (A B : Ty) : RegTerm A (.list B) := (bangTerm A).comp (nilTerm B)

@[simp] lemma constNilTerm_eval (A B : Ty) (a : A.Elt) : (constNilTerm A B).eval a = [] := rfl

/-- The singleton list, as a term `A → A*`. -/
def pureTerm (A : Ty) : RegTerm A (.list A) :=
  ((RegTerm.diag A).comp ((idTermOf A).prodMap (constNilTerm A A))).comp
    ((RegTerm.inr .one (.prod A (.list A))).comp (RegTerm.cons A))

@[simp] lemma pureTerm_eval (A : Ty) (a : A.Elt) : (pureTerm A).eval a = [a] := by
  show (idTermOf A).eval a :: (constNilTerm A A).eval a = [a]
  rw [idTermOf_eval, constNilTerm_eval]

/-- The concatenation of two lists, as a term `A* × A* → A*`. -/
def appendTerm (A : Ty) : RegTerm (.prod (.list A) (.list A)) (.list A) :=
  ((idTermOf (.list A)).prodMap (pureTerm (.list A))).comp
    (((RegTerm.inr .one (.prod (.list A) (.list (.list A)))).comp (RegTerm.cons (.list A))).comp
      (RegTerm.concat A))

@[simp] lemma appendTerm_eval (A : Ty) (u v : List A.Elt) :
    (appendTerm A).eval (u, v) = u ++ v := by
  show ((idTermOf (.list A)).eval u :: (pureTerm (.list A)).eval v).flatten = u ++ v
  rw [idTermOf_eval, pureTerm_eval]
  show u ++ (v ++ []) = u ++ v
  rw [List.append_nil]

/-- A term `1 → A` that invents an element of `A`; it returns the default element of the type. -/
def inventTerm : (A : Ty) → RegTerm .one A
  | .one => idOneTerm
  | .prod A B => (RegTerm.diag .one).comp ((inventTerm A).prodMap (inventTerm B))
  | .sum A B => (inventTerm A).comp (RegTerm.inl A B)
  | .list A => nilTerm A

@[simp] lemma inventTerm_eval : ∀ (A : Ty) (x : Ty.one.Elt), (inventTerm A).eval x = default
  | .one, x => by cases x; rfl
  | .prod A B, x => by
      have h : (inventTerm (Ty.prod A B)).eval x
          = ((inventTerm A).eval x, (inventTerm B).eval x) := rfl
      rw [h, inventTerm_eval A, inventTerm_eval B]
      rfl
  | .sum A B, x => by
      have h : (inventTerm (Ty.sum A B)).eval x = Sum.inl ((inventTerm A).eval x) := rfl
      rw [h, inventTerm_eval A]
      rfl
  | .list A, x => rfl

/-- The head of a list, as a term `A* → A`; this is Claim `claim:head`. -/
def headTerm (A : Ty) : RegTerm (.list A) A :=
  (RegTerm.uncons A).comp
    (((inventTerm A).sumMap (RegTerm.fst A (.list A))).comp (RegTerm.codiag A))

@[simp] lemma headTerm_eval (A : Ty) (l : List A.Elt) : (headTerm A).eval l = l.headI := by
  cases l with
  | nil =>
      have h : (headTerm A).eval ([] : List A.Elt) = (inventTerm A).eval () := rfl
      rw [h, inventTerm_eval]
      rfl
  | cons a l => rfl

/-- The tail of a list, as a term `A* → A*`. -/
def tailTerm (A : Ty) : RegTerm (.list A) (.list A) :=
  (RegTerm.uncons A).comp
    (((nilTerm A).sumMap (RegTerm.snd A (.list A))).comp (RegTerm.codiag (.list A)))

@[simp] lemma tailTerm_eval (A : Ty) (l : List A.Elt) : (tailTerm A).eval l = l.tail := by
  cases l with
  | nil => rfl
  | cons a l => rfl

/-- The list without its last entry, as a term `A* → A*`: reverse, tail, reverse. -/
def dropLastTerm (A : Ty) : RegTerm (.list A) (.list A) :=
  ((RegTerm.reverse A).comp (tailTerm A)).comp (RegTerm.reverse A)

lemma reverse_tail_reverse {α : Type} (l : List α) : (l.reverse.tail).reverse = l.dropLast := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a _ => simp

@[simp] lemma dropLastTerm_eval (A : Ty) (l : List A.Elt) :
    (dropLastTerm A).eval l = l.dropLast := by
  show ((tailTerm A).eval l.reverse).reverse = l.dropLast
  rw [tailTerm_eval, reverse_tail_reverse]

/-- The term `A → (A + A)*` of the author's solution: `a ↦ [L a, R a]`. -/
def dupTerm (A : Ty) : RegTerm A (.list (.sum A A)) :=
  ((RegTerm.diag A).comp
      (((RegTerm.inl A A).comp (pureTerm (.sum A A))).prodMap
        ((RegTerm.inr A A).comp (pureTerm (.sum A A))))).comp (appendTerm (.sum A A))

@[simp] lemma dupTerm_eval (A : Ty) (a : A.Elt) :
    (dupTerm A).eval a = [Sum.inl a, Sum.inr a] := by
  have h : (dupTerm A).eval a = (appendTerm (Ty.sum A A)).eval
      ((pureTerm (.sum A A)).eval (Sum.inl a), (pureTerm (.sum A A)).eval (Sum.inr a)) := rfl
  rw [h, pureTerm_eval, pureTerm_eval, appendTerm_eval]
  rfl

/-- **The term of Exercise `exer:windows-of-size-two`.** -/
def windowsTwoTerm (A : Ty) : RegTerm (.list A) (.list (.prod A A)) :=
  ((((dupTerm A).map).comp (RegTerm.concat (.sum A A))).comp
      (((RegTerm.split A A).comp (RegTerm.snd (.list A) (.list (.prod A (.list A))))).comp
        (dropLastTerm (.prod A (.list A))))).comp
    (((idTermOf A).prodMap (headTerm A)).map)

/-! ### What the term computes -/

/-- The value of the second component of the split, in the author's solution: every entry of the
input, together with the (empty or one-element) list of the entry that follows it. -/
def pairsAux {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: l => (a, l.take 1) :: pairsAux l

lemma splitList_dup {α : Type} : ∀ l : List α,
    splitList ((l.map (fun a => [Sum.inl a, Sum.inr a])).flatten) = (l.take 1, pairsAux l)
  | [] => rfl
  | a :: l => by
      have ih := splitList_dup l
      show splitList (Sum.inl a :: Sum.inr a ::
        (l.map (fun a => [Sum.inl a, Sum.inr a])).flatten) = _
      rw [splitList_inl, splitList_inr, ih]
      rfl

lemma pairsAux_cons_ne_nil {α : Type} (a : α) (l : List α) : pairsAux (a :: l) ≠ [] := by
  simp [pairsAux]

lemma map_dropLast_pairsAux {α : Type} [Inhabited α] : ∀ l : List α,
    ((pairsAux l).dropLast).map (fun q : α × List α => (q.1, q.2.headI)) = windowsTwo l
  | [] => rfl
  | a :: l => by
      cases l with
      | nil => rfl
      | cons b l =>
          have ih := map_dropLast_pairsAux (b :: l)
          show ((((a, [b]) : α × List α) :: pairsAux (b :: l)).dropLast).map _ = _
          rw [List.dropLast_cons_of_ne_nil (pairsAux_cons_ne_nil b l), List.map_cons, ih]
          rfl

/-- **Exercise `exer:windows-of-size-two`.**  The term `Transducers.Exercises.windowsTwoTerm`
computes the windows of size two of its input. -/
theorem regTerm_windows_two (A : Ty) (l : List A.Elt) :
    (windowsTwoTerm A).eval l = windowsTwo l := by
  have h1 : (windowsTwoTerm A).eval l
      = ((dropLastTerm (Ty.prod A (.list A))).eval
          (splitList ((l.map (dupTerm A).eval).flatten)).2).map
            (fun q => ((idTermOf A).eval q.1, (headTerm A).eval q.2)) := rfl
  have hdup : (l.map (dupTerm A).eval) = l.map (fun a => [Sum.inl a, Sum.inr a]) :=
    List.map_congr_left (fun a _ => dupTerm_eval A a)
  rw [h1, hdup, dropLastTerm_eval, splitList_dup]
  simp only [idTermOf_eval, headTerm_eval]
  exact map_dropLast_pairsAux l

/-- The windows of size two, as a function defined by a regular term. -/
lemma tfun_windowsTwo (A : Ty) :
    IsRegularTermFun (A := .list A) (B := .list (.prod A A))
      (fun l => windowsTwo l) :=
  ⟨windowsTwoTerm A, funext (regTerm_windows_two A)⟩

/-! ## Exercise `exer:group-prefix-multiplication-isomorphism`: prefix multiplication is a
bijection -/

section Group

variable {M : Type} [Group M]

/-- The inverse of group prefix multiplication, as the author describes it: if the output is
`[g₁,…,gₙ]` then the `i`-th input letter is `gᵢ₋₁⁻¹ gᵢ`, with `g₀` the unit of the group.  That is
the windows of size two of the input with the unit prepended. -/
def unprefixProd (l : List M) : List M := (windowsTwo (1 :: l)).map (fun q => q.1⁻¹ * q.2)

/-- The same function with an arbitrary element in front of the list, which is what the induction
needs. -/
def unprefAux (x : M) (l : List M) : List M := ((x :: l).zip l).map (fun q => q.1⁻¹ * q.2)

lemma unprefixProd_eq_unprefAux (l : List M) : unprefixProd l = unprefAux 1 l := rfl

@[simp] lemma unprefAux_nil (x : M) : unprefAux x [] = [] := rfl

lemma unprefAux_cons (x a : M) (l : List M) :
    unprefAux x (a :: l) = (x⁻¹ * a) :: unprefAux a l := rfl

@[simp] lemma prefixProd_nil : prefixProd ([] : List M) = [] := rfl

lemma scanl_mul_left (x : M) : ∀ l : List M,
    l.scanl (· * ·) x = (l.scanl (· * ·) 1).map (fun z => x * z)
  | [] => by simp
  | a :: l => by
      rw [List.scanl_cons, List.scanl_cons, List.map_cons, scanl_mul_left (x * a) l,
        scanl_mul_left (1 * a) l, List.map_map]
      simp [mul_assoc]

lemma scanl_one_eq (l : List M) : l.scanl (· * ·) 1 = 1 :: prefixProd l := by
  cases l with
  | nil => rfl
  | cons a l => rw [prefixProd, List.scanl_cons]; rfl

lemma prefixProd_cons (a : M) (l : List M) :
    prefixProd (a :: l) = a :: (prefixProd l).map (fun z => a * z) := by
  have h : prefixProd (a :: l) = l.scanl (· * ·) (1 * a) := by
    rw [prefixProd, List.scanl_cons]; rfl
  rw [h, one_mul, scanl_mul_left a l, scanl_one_eq, List.map_cons, mul_one]

lemma unprefAux_prefixProd : ∀ (l : List M) (x : M),
    unprefAux x ((prefixProd l).map (fun z => x * z)) = l
  | [], x => by simp
  | a :: l, x => by
      rw [prefixProd_cons, List.map_cons, List.map_map]
      have hmap : (prefixProd l).map ((fun z => x * z) ∘ fun z => a * z)
          = (prefixProd l).map (fun z => (x * a) * z) := by
        refine List.map_congr_left (fun z _ => ?_)
        simp [mul_assoc]
      rw [hmap, unprefAux_cons, unprefAux_prefixProd l (x * a)]
      simp

lemma prefixProd_unprefAux : ∀ (l : List M) (x : M),
    prefixProd (unprefAux x l) = l.map (fun z => x⁻¹ * z)
  | [], x => by simp
  | g :: l, x => by
      rw [unprefAux_cons, prefixProd_cons, prefixProd_unprefAux l g, List.map_map, List.map_cons]
      refine congrArg (fun v => (x⁻¹ * g) :: v) ?_
      refine List.map_congr_left (fun z _ => ?_)
      simp [mul_assoc]

/-- The inverse of prefix multiplication is a left inverse. -/
lemma unprefixProd_prefixProd (l : List M) : unprefixProd (prefixProd l) = l := by
  have h := unprefAux_prefixProd l (1 : M)
  simpa [unprefixProd_eq_unprefAux] using h

/-- The inverse of prefix multiplication is a right inverse. -/
lemma prefixProd_unprefixProd (l : List M) : prefixProd (unprefixProd l) = l := by
  have h := prefixProd_unprefAux l (1 : M)
  simpa [unprefixProd_eq_unprefAux] using h

end Group

/-- **Exercise `exer:group-prefix-multiplication-isomorphism`.**  Group prefix multiplication is a
bijection, and its inverse is again defined by a regular term.

The inverse is the author's: the `i`-th letter of the input is `gᵢ₋₁⁻¹ gᵢ`, where `[g₁,…,gₙ]` is
the output and `g₀` is the unit of the group.  As a term, it prepends the unit, takes the windows
of size two (Exercise `exer:windows-of-size-two`) and applies the map `(x, y) ↦ x⁻¹ y`, which is
definable because the underlying type of the group is finite. -/
theorem pref_bijective (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    Function.Bijective (RegTerm.pref G grp hfin).eval ∧
      ∃ t : RegTerm (.list G) (.list G),
        (∀ l : List G.Elt, t.eval ((RegTerm.pref G grp hfin).eval l) = l) ∧
        (∀ l : List G.Elt, (RegTerm.pref G grp hfin).eval (t.eval l) = l) := by
  letI := grp
  haveI := hfin
  have hev : ∀ l : List G.Elt, (RegTerm.pref G grp hfin).eval l = prefixProd l := fun _ => rfl
  have hleft : ∀ l : List G.Elt,
      unprefixProd ((RegTerm.pref G grp hfin).eval l) = l := by
    intro l; rw [hev]; exact unprefixProd_prefixProd l
  have hright : ∀ l : List G.Elt,
      (RegTerm.pref G grp hfin).eval (unprefixProd l) = l := by
    intro l; rw [hev]; exact prefixProd_unprefixProd l
  have hterm : IsRegularTermFun (A := .list G) (B := .list G)
      (fun l : List G.Elt => unprefixProd l) := by
    have hfin2 : Finite (Ty.prod G G).Elt := by
      change Finite (G.Elt × G.Elt)
      infer_instance
    have hmul : IsRegularTermFun (A := .prod G G) (B := G)
        (fun q : G.Elt × G.Elt => q.1⁻¹ * q.2) :=
      finite_domain_regular_list_function hfin2 _
    have h := ((tfun_consFixed G (1 : G.Elt)).comp (tfun_windowsTwo G)).comp hmul.mapList
    exact h.congr (fun l => rfl)
  obtain ⟨t, ht⟩ := hterm
  refine ⟨⟨?_, ?_⟩, t, ?_, ?_⟩
  · exact Function.LeftInverse.injective hleft
  · exact fun l => ⟨unprefixProd l, hright l⟩
  · intro l; rw [ht]; exact hleft l
  · intro l; rw [ht]; exact hright l

/-! ## Exercise `exer:filter-plus`: keeping the entries of the first summand -/

/-- The function of Exercise `exer:filter-plus`: from a list over `A + B`, keep the entries that
lie in `A`, in their order. -/
def filterPlus {A B : Ty} (l : List ((Ty.sum A B).Elt)) : List A.Elt :=
  l.filterMap Sum.getLeft?

@[simp] lemma filterPlus_nil {A B : Ty} : filterPlus (A := A) (B := B) [] = [] := rfl

@[simp] lemma filterPlus_cons_inl {A B : Ty} (a : A.Elt) (l : List ((Ty.sum A B).Elt)) :
    filterPlus (Sum.inl a :: l) = a :: filterPlus l := rfl

@[simp] lemma filterPlus_cons_inr {A B : Ty} (b : B.Elt) (l : List ((Ty.sum A B).Elt)) :
    filterPlus (A := A) (Sum.inr b :: l) = filterPlus l := rfl

/-- The function `A + B → A*` of the author's solution: `L a ↦ [a]` and `R b ↦ []`. -/
def keepLeftTerm (A B : Ty) : RegTerm (.sum A B) (.list A) :=
  ((pureTerm A).sumMap (constNilTerm B A)).comp (RegTerm.codiag (.list A))

@[simp] lemma keepLeftTerm_eval_inl (A B : Ty) (a : A.Elt) :
    (keepLeftTerm A B).eval (Sum.inl a) = [a] := by
  show (pureTerm A).eval a = [a]
  rw [pureTerm_eval]

@[simp] lemma keepLeftTerm_eval_inr (A B : Ty) (b : B.Elt) :
    (keepLeftTerm A B).eval (Sum.inr b) = [] := rfl

/-- **The term of Exercise `exer:filter-plus`**: apply `Transducers.Exercises.keepLeftTerm` to
every entry of the input and concatenate the results. -/
def filterPlusTerm (A B : Ty) : RegTerm (.list (.sum A B)) (.list A) :=
  ((keepLeftTerm A B).map).comp (RegTerm.concat A)

/-- **Exercise `exer:filter-plus`.**  The regular term `Transducers.Exercises.filterPlusTerm`
defines the function `(A + B)* → A*` that keeps only the list entries of type `A`. -/
theorem regTerm_filter_plus (A B : Ty) (l : List ((Ty.sum A B).Elt)) :
    (filterPlusTerm A B).eval l = filterPlus l := by
  show (l.map (keepLeftTerm A B).eval).flatten = filterPlus l
  induction l with
  | nil => rfl
  | cons x l ih =>
      cases x with
      | inl a => rw [List.map_cons, List.flatten_cons, keepLeftTerm_eval_inl, ih]; rfl
      | inr b => rw [List.map_cons, List.flatten_cons, keepLeftTerm_eval_inr, ih]; rfl

/-- The function of Exercise `exer:filter-plus`, as a function defined by a regular term. -/
lemma tfun_filterPlus (A B : Ty) :
    IsRegularTermFun (A := .list (.sum A B)) (B := .list A) filterPlus :=
  ⟨filterPlusTerm A B, funext (regTerm_filter_plus A B)⟩

end Exercises
end Transducers
