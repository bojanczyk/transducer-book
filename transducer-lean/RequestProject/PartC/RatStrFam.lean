/-
String-to-string functions that are definable by rational terms, for the converse direction of
Theorem `thm:rational-terms` of Section *Combinators* of *Transducers* (M. Bojańczyk).

This is the counterpart of `CombStrFam.lean`: the predicate `Transducers.RatTermStrFun g` says
that the function `g : A* → B*` between finite alphabets becomes a function definable by a
rational term once the alphabets are named by types, in every way of naming them, and the same
three facts make it usable -- one naming suffices, the predicate is closed under composition, and
therefore a whole composition closure is covered as soon as its primes are.

The easy primes are here as well: string homomorphisms and Lemma `lem:terms-define-append-hash`,
whose proof adjoins a unit where the regular one pairs with a constant.  String reversal, which
`CombStrFam.lean` uses to resolve the symmetry between the left-to-right and the right-to-left
prime Mealy machines, is *not* here: it is not rational, and the symmetry is resolved instead by
Exercise `exer:no-reverse-reversible` (for the reversible machines) and by redoing the construction
in the right-to-left direction (for the flip-flop machines), in `RatMealyFF.lean`.
-/
import RequestProject.PartC.RatDerived
import RequestProject.PartB.RationalStatements

namespace Transducers

/-! ## Lemma `lem:terms-define-append-hash` -/

/-- **Lemma `lem:terms-define-append-hash` for rational terms.**  The function `w ↦ w#` that
appends a fresh end marker, seen as a function `A* → (A + 1)*`, is definable by a rational
term. -/
theorem rat_terms_define_append_hash (A : Ty) :
    IsRatTermFun (A := .list A) (B := .list (.sum A .one))
      (fun l => l.map Sum.inl ++ [Sum.inr ()]) :=
  rtfun_appendConst ((rtfun_inl A .one).mapList) [Sum.inr ()]

/-- The general form: a letter-to-letter renaming followed by a fixed extra letter at the end. -/
lemma rtfun_mapAppendFixed {A B : Ty} (hA : Finite A.Elt) (psi : A.Elt → B.Elt) (c : B.Elt) :
    IsRatTermFun (A := .list A) (B := .list B) (fun l => l.map psi ++ [c]) :=
  rtfun_appendConst (rtfun_mapRen hA psi) [c]

/-! ## String-to-string functions definable by rational terms -/

/-- A string-to-string function between finite alphabets is **definable by rational terms** if,
whichever types are used to name the two alphabets, the corresponding function between the two
list types is defined by a rational term. -/
def RatTermStrFun {X Y : Type} (g : List X → List Y) : Prop :=
  ∀ (A B : Ty), Finite A.Elt → Finite B.Elt → ∀ (eA : A.Elt ≃ X) (eB : Y ≃ B.Elt),
    IsRatTermFun (A := .list A) (B := .list B) (fun l => (g (l.map eA)).map eB)

lemma RatTermStrFun.congr {X Y : Type} {g g' : List X → List Y} (h : RatTermStrFun g)
    (hgg : ∀ w, g w = g' w) : RatTermStrFun g' := by
  intro A B hA hB eA eB
  exact (h A B hA hB eA eB).congr (fun l => by rw [hgg])

/-- **One naming of the alphabets suffices.** -/
lemma ratTermStrFun_of_one {X Y : Type} {g : List X → List Y}
    (A B : Ty) (hB : Finite B.Elt) (eA : A.Elt ≃ X) (eB : Y ≃ B.Elt)
    (h : IsRatTermFun (A := .list A) (B := .list B) (fun l => (g (l.map eA)).map eB)) :
    RatTermStrFun g := by
  intro A' B' hA' hB' eA' eB'
  have hrho := rtfun_mapRen hA' (fun a => eA.symm (eA' a))
  have hsigma := rtfun_mapRen hB (fun b => eB' (eB.symm b))
  refine ((hrho.comp h).comp hsigma).congr ?_
  intro l
  simp [List.map_map, Function.comp_def]

/-- If the input alphabet is empty then `RatTermStrFun` is vacuously true: no type has an empty
set of elements. -/
lemma ratTermStrFun_of_isEmpty_dom {X Y : Type} (g : List X → List Y) (h : IsEmpty X) :
    RatTermStrFun g := by
  intro A _ _ _ eA _
  exact (h.false (eA default)).elim

/-- If the output alphabet is empty then `RatTermStrFun` is vacuously true. -/
lemma ratTermStrFun_of_isEmpty_cod {X Y : Type} (g : List X → List Y) (h : IsEmpty Y) :
    RatTermStrFun g := by
  intro _ B _ _ _ eB
  exact (h.false (eB.symm default)).elim

/-- A constant string-to-string function is definable by rational terms. -/
lemma ratTermStrFun_const {X Y : Type} (v : List Y) : RatTermStrFun (fun _ : List X => v) := by
  intro A B _ _ _ eB
  exact rtfun_const (.list A) (.list B) (v.map eB)

lemma ratTermStrFun_id (X : Type) : RatTermStrFun (fun w : List X => w) := by
  intro A B hA _ eA eB
  exact (rtfun_mapRen hA (fun a => eB (eA a))).congr (fun l => by
    simp [Function.comp_def])

lemma RatTermStrFun.comp {X Y Z : Type} [Finite Y] {g₁ : List X → List Y} {g₂ : List Y → List Z}
    (h₁ : RatTermStrFun g₁) (h₂ : RatTermStrFun g₂) : RatTermStrFun (fun w => g₂ (g₁ w)) := by
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
    exact (ratTermStrFun_const (X := X) (g₂ [])).congr (fun w => by rw [hg1])

/-- **A composition closure is covered as soon as its primes are.** -/
theorem ratTermStrFun_of_compClosure {P : ∀ (A B : Type), (List A → List B) → Prop}
    (hP : ∀ {X Y : Type} {g : List X → List Y}, Finite X → Finite Y → P X Y g →
      RatTermStrFun g) :
    ∀ {X Y : Type} {g : List X → List Y}, CompClosure P X Y g → Finite X → Finite Y →
      RatTermStrFun g := by
  intro X Y g h
  induction h with
  | base hf => intro hX hY; exact hP hX hY hf
  | id X => intro _ _; exact ratTermStrFun_id X
  | @comp X Y Z hY f g _ _ ihf ihg =>
      intro hX hZ
      exact ((ihf hX hY).comp (ihg hY hZ)).congr (fun _ => rfl)

/-! ## The easy primes -/

/-- Lemma `lem:terms-define-string-homomorphisms`, in the form used for the primes. -/
lemma ratTermStrFun_homOf {X Y : Type} (phi : X → List Y) : RatTermStrFun (homOf phi) := by
  intro A B hA hB eA eB
  refine (rat_terms_define_string_homomorphisms (B := B) hA
    (fun a => (phi (eA a)).map eB)).congr ?_
  intro l
  simp [homOf, List.map_map, Function.comp_def]

/-- The prime that appends a fresh separator is definable by rational terms. -/
lemma ratTermStrFun_sep {X Y : Type} (e : Option X ≃ Y) :
    RatTermStrFun (fun w : List X => w.map (fun a => e (some a)) ++ [e none]) := by
  intro A B hA _ eA eB
  refine (rtfun_mapAppendFixed hA (fun a => eB (e (some (eA a)))) (eB (e none))).congr ?_
  intro l
  simp [List.map_map, Function.comp_def]

end Transducers
