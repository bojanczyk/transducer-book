/-
String-to-string functions that are definable by regular terms, for the converse direction of
Theorem `thm:regular-terms` of Section *Combinators* of *Transducers* (M. Bojańczyk).

The converse direction is proved, as the book does, by showing that every *prime* regular
string-to-string function is definable by a term, and then using that terms are closed under
composition.  The primes of Definition `def:regular-functions` and of Theorem
`thm:rational-primes` are functions `A* → B*` for arbitrary finite alphabets `A` and `B`, while a
term speaks about `Ty`s.  This file is the interface between the two: the predicate

    `Transducers.TermStrFun g`

says that the function `g : A* → B*` becomes a term-definable function `A* → B*` between *list
types* once the alphabets are named by types, in every way of naming them.  Three facts make it
usable:

* `Transducers.termStrFun_of_one` -- one naming of the alphabets suffices, because a change of
  naming is a letter-to-letter renaming, and those are definable by Claim
  `claim:finite-domain-regular-list-function`;
* `Transducers.TermStrFun.comp` -- the predicate is closed under composition, with the empty
  intermediate alphabet treated separately (a type has no empty set of elements, so `TermStrFun`
  is vacuous there, and the composite is a constant function);
* `Transducers.termStrFun_of_compClosure` -- hence a whole `CompClosure` of a family of primes is
  covered as soon as its primes are.

The easy primes are also done here: homomorphisms (which is Lemma
`lem:terms-define-string-homomorphisms`, already proved in `CombFinite.lean`, in the present
form), string reversal, and Lemma `lem:terms-define-append-hash`.
-/
import RequestProject.PartC.CombDerived
import RequestProject.PartB.RationalStatements

namespace Transducers

/-! ## Lemma `lem:terms-define-append-hash` -/

/-- **Lemma `lem:terms-define-append-hash`.**  The function `w ↦ w#` that appends a fresh
end-marker, seen as a function `A* → (A + 1)*`, is definable by a term. -/
theorem terms_define_append_hash (A : Ty) :
    IsRegularTermFun (A := .list A) (B := .list (.sum A .one))
      (fun l => l.map Sum.inl ++ [Sum.inr ()]) := by
  refine ((((tfun_inl A .one).mapList).pair
    (tfun_const (.list A) (.list (.sum A .one)) [Sum.inr ()])).comp
    (tfun_append (.sum A .one))).congr ?_
  intro l
  rfl

/-- The general form of Lemma `lem:terms-define-append-hash`: a letter-to-letter renaming followed
by a fixed extra letter at the end. -/
lemma tfun_mapAppendFixed {A B : Ty} (hA : Finite A.Elt) (psi : A.Elt → B.Elt) (c : B.Elt) :
    IsRegularTermFun (A := .list A) (B := .list B) (fun l => l.map psi ++ [c]) := by
  refine ((((finite_domain_regular_list_function hA psi).mapList).pair
    (tfun_const (.list A) (.list B) [c])).comp (tfun_append B)).congr ?_
  intro l
  rfl

/-! ## String-to-string functions definable by terms -/

/-- A string-to-string function between finite alphabets is **definable by terms** if, whichever
types are used to name the two alphabets, the corresponding function between the two list types is
defined by a regular term. -/
def TermStrFun {X Y : Type} (g : List X → List Y) : Prop :=
  ∀ (A B : Ty), Finite A.Elt → Finite B.Elt → ∀ (eA : A.Elt ≃ X) (eB : Y ≃ B.Elt),
    IsRegularTermFun (A := .list A) (B := .list B) (fun l => (g (l.map eA)).map eB)

lemma TermStrFun.congr {X Y : Type} {g g' : List X → List Y} (h : TermStrFun g)
    (hgg : ∀ w, g w = g' w) : TermStrFun g' := by
  intro A B hA hB eA eB
  exact (h A B hA hB eA eB).congr (fun l => by rw [hgg])

/-- A letter-to-letter renaming of a list, which is the map of a function with a finite domain. -/
lemma tfun_mapRen {A B : Ty} (hA : Finite A.Elt) (h : A.Elt → B.Elt) :
    IsRegularTermFun (A := .list A) (B := .list B) (fun l => l.map h) :=
  (finite_domain_regular_list_function hA h).mapList

/-- **One naming of the alphabets suffices.** -/
lemma termStrFun_of_one {X Y : Type} {g : List X → List Y}
    (A B : Ty) (hB : Finite B.Elt) (eA : A.Elt ≃ X) (eB : Y ≃ B.Elt)
    (h : IsRegularTermFun (A := .list A) (B := .list B) (fun l => (g (l.map eA)).map eB)) :
    TermStrFun g := by
  intro A' B' hA' hB' eA' eB'
  have hrho := tfun_mapRen hA' (fun a => eA.symm (eA' a))
  have hsigma := tfun_mapRen hB (fun b => eB' (eB.symm b))
  refine ((hrho.comp h).comp hsigma).congr ?_
  intro l
  simp [List.map_map, Function.comp_def]

/-- If the input alphabet is empty then `TermStrFun` is vacuously true: no type has an empty set
of elements. -/
lemma termStrFun_of_isEmpty_dom {X Y : Type} (g : List X → List Y) (h : IsEmpty X) :
    TermStrFun g := by
  intro A _ _ _ eA _
  exact (h.false (eA default)).elim

/-- If the output alphabet is empty then `TermStrFun` is vacuously true. -/
lemma termStrFun_of_isEmpty_cod {X Y : Type} (g : List X → List Y) (h : IsEmpty Y) :
    TermStrFun g := by
  intro _ B _ _ _ eB
  exact (h.false (eB.symm default)).elim

/-- A constant string-to-string function is definable by terms. -/
lemma termStrFun_const {X Y : Type} (v : List Y) : TermStrFun (fun _ : List X => v) := by
  intro A B _ _ _ eB
  exact tfun_const (.list A) (.list B) (v.map eB)

lemma termStrFun_id (X : Type) : TermStrFun (fun w : List X => w) := by
  intro A B hA _ eA eB
  exact (tfun_mapRen hA (fun a => eB (eA a))).congr (fun l => by
    simp [Function.comp_def])

lemma TermStrFun.comp {X Y Z : Type} [Finite Y] {g₁ : List X → List Y} {g₂ : List Y → List Z}
    (h₁ : TermStrFun g₁) (h₂ : TermStrFun g₂) : TermStrFun (fun w => g₂ (g₁ w)) := by
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
    exact (termStrFun_const (X := X) (g₂ [])).congr (fun w => by rw [hg1])

/-- **A composition closure is covered as soon as its primes are.** -/
theorem termStrFun_of_compClosure {P : ∀ (A B : Type), (List A → List B) → Prop}
    (hP : ∀ {X Y : Type} {g : List X → List Y}, Finite X → Finite Y → P X Y g → TermStrFun g) :
    ∀ {X Y : Type} {g : List X → List Y}, CompClosure P X Y g → Finite X → Finite Y →
      TermStrFun g := by
  intro X Y g h
  induction h with
  | base hf => intro hX hY; exact hP hX hY hf
  | id X => intro _ _; exact termStrFun_id X
  | @comp X Y Z hY f g _ _ ihf ihg =>
      intro hX hZ
      exact ((ihf hX hY).comp (ihg hY hZ)).congr (fun _ => rfl)

/-! ## The easy primes -/

/-- Lemma `lem:terms-define-string-homomorphisms`, in the form used for the primes. -/
lemma termStrFun_homOf {X Y : Type} (phi : X → List Y) : TermStrFun (homOf phi) := by
  intro A B hA hB eA eB
  refine (terms_define_string_homomorphisms (B := B) hA (fun a => (phi (eA a)).map eB)).congr ?_
  intro l
  simp [homOf, List.map_map, Function.comp_def]

/-- String reversal is definable by terms; this is what resolves the symmetry between the
left-to-right and the right-to-left prime Mealy machines. -/
lemma termStrFun_reverse (X : Type) : TermStrFun (fun w : List X => w.reverse) := by
  intro A B hA _ eA eB
  refine ((tfun_mapRen hA (fun a => eB (eA a))).comp (tfun_reverse B)).congr ?_
  intro l
  simp [Function.comp_def]

/-- The prime that appends a fresh separator is definable by terms. -/
lemma termStrFun_sep {X Y : Type} (e : Option X ≃ Y) :
    TermStrFun (fun w : List X => w.map (fun a => e (some a)) ++ [e none]) := by
  intro A B hA _ eA eB
  refine (tfun_mapAppendFixed hA (fun a => eB (e (some (eA a)))) (eB (e none))).congr ?_
  intro l
  simp [List.map_map, Function.comp_def]

end Transducers
