/-
Derived combinators for the regular terms of Section *Combinators* of *Transducers*
(M. Bojańczyk).

This file is the toolbox of the *converse* direction of Theorem `thm:regular-terms`: the derived
terms that the book uses without comment -- swapping the coordinates of a product, the second form
of distributivity, applying two terms in parallel to the coordinates of a product, the empty list,
the singleton list, the concatenation of two lists, the inverse of split -- together with the three
numbered results of the section that are about terms alone:

* Claim `claim:bang-definable`, that `A → 1` is definable, is `Transducers.bang_definable`;
* Claim `claim:head`, that a `head` operation is definable, is `Transducers.claim_head`;
* Claim `claim:finite-type-bijection-disjoint-units`, that a finite type is in term-definable
  bijection with `1 + ⋯ + 1`, is `Transducers.finite_type_bijection_disjoint_units`.

The last one is proved here *from* Claim `claim:finite-domain-regular-list-function`
(`RequestProject/PartC/CombFinite.lean`), which is the opposite of the book's order: the book
reduces a finite domain to `1 + ⋯ + 1` and then uses co-pairing, while `CombFinite.lean` takes the
domain apart directly.  With that claim in hand a bijection between finite types is definable in
both directions for free, since both have a finite domain.  Nothing is lost: both statements are
proved, only the dependency between them is reversed.

The file also proves the *finite case distinction* `Transducers.tfun_finCases`, which is what the
book means when it says "using distributivity and co-pairing": a term may branch on a letter of a
finite type while carrying an arbitrary value along.  It is used for the Mealy machines and for
inverting the string representation.
-/
import RequestProject.PartC.CombFinite

namespace Transducers

/-! ## The atomic terms, as statements about `IsRegularTermFun` -/

lemma tfun_id (A : Ty) : IsRegularTermFun (A := A) (B := A) (fun a => a) :=
  ⟨RegTerm.id A, rfl⟩

lemma tfun_fst (A B : Ty) :
    IsRegularTermFun (A := .prod A B) (B := A) (fun p => p.1) := ⟨RegTerm.fst A B, rfl⟩

lemma tfun_snd (A B : Ty) :
    IsRegularTermFun (A := .prod A B) (B := B) (fun p => p.2) := ⟨RegTerm.snd A B, rfl⟩

lemma tfun_inl (A B : Ty) :
    IsRegularTermFun (A := A) (B := .sum A B) (fun a => Sum.inl a) := ⟨RegTerm.inl A B, rfl⟩

lemma tfun_inr (A B : Ty) :
    IsRegularTermFun (A := B) (B := .sum A B) (fun b => Sum.inr b) := ⟨RegTerm.inr A B, rfl⟩

lemma tfun_distr (A B C : Ty) :
    IsRegularTermFun (A := .prod A (.sum B C)) (B := .sum (.prod A B) (.prod A C))
      (fun x => Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2) :=
  ⟨RegTerm.distr A B C, rfl⟩

lemma tfun_cons (A : Ty) :
    IsRegularTermFun (A := .sum .one (.prod A (.list A))) (B := .list A)
      (fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x) := ⟨RegTerm.cons A, rfl⟩

lemma tfun_uncons (A : Ty) :
    IsRegularTermFun (A := .list A) (B := .sum .one (.prod A (.list A)))
      (fun l => match l with | [] => Sum.inl () | a :: l' => Sum.inr (a, l')) :=
  ⟨RegTerm.uncons A, rfl⟩

lemma tfun_reverse (A : Ty) :
    IsRegularTermFun (A := .list A) (B := .list A) (fun l => l.reverse) :=
  ⟨RegTerm.reverse A, rfl⟩

lemma tfun_concat (A : Ty) :
    IsRegularTermFun (A := .list (.list A)) (B := .list A) (fun l => l.flatten) :=
  ⟨RegTerm.concat A, rfl⟩

lemma tfun_split (A B : Ty) :
    IsRegularTermFun (A := .list (.sum A B)) (B := .prod (.list A) (.list (.prod B (.list A))))
      (fun l => splitList l) := ⟨RegTerm.split A B, rfl⟩

/-! ## Derived combinators -/

/-- Swapping the coordinates of a product. -/
lemma tfun_swap (A B : Ty) :
    IsRegularTermFun (A := .prod A B) (B := .prod B A) (fun p => (p.2, p.1)) :=
  (tfun_snd A B).pair (tfun_fst A B)

/-- Two terms applied in parallel to the two coordinates of a product; the book writes it
`f × g`.  This is the functoriality combinator of Definition `def:regular-terms`. -/
lemma tfun_prodMap {A B C D : Ty} {f : A.Elt → C.Elt} {g : B.Elt → D.Elt}
    (hf : IsRegularTermFun f) (hg : IsRegularTermFun g) :
    IsRegularTermFun (A := .prod A B) (B := .prod C D) (fun p => (f p.1, g p.2)) :=
  hf.prodMap hg

/-- Two terms applied to the two summands of a co-product; the book writes it `f + g`.  This is
the functoriality combinator of Definition `def:regular-terms`. -/
lemma tfun_sumMap {A B C D : Ty} {f : A.Elt → C.Elt} {g : B.Elt → D.Elt}
    (hf : IsRegularTermFun f) (hg : IsRegularTermFun g) :
    IsRegularTermFun (A := .sum A B) (B := .sum C D) (fun x => Sum.map f g x) :=
  hf.sumMap hg

/-- The second form of distributivity, `(A + B) × C → (A × C) + (B × C)`, which the book derives
from the first one using `swap`. -/
lemma tfun_distl (A B C : Ty) :
    IsRegularTermFun (A := .prod (.sum A B) C) (B := .sum (.prod A C) (.prod B C))
      (fun p => Sum.elim (fun a => Sum.inl (a, p.2)) (fun b => Sum.inr (b, p.2)) p.1) := by
  have h1 : IsRegularTermFun (A := .prod C A) (B := .sum (.prod A C) (.prod B C))
      (fun q => Sum.inl (q.2, q.1)) := (tfun_swap C A).comp (tfun_inl (.prod A C) (.prod B C))
  have h2 : IsRegularTermFun (A := .prod C B) (B := .sum (.prod A C) (.prod B C))
      (fun q => Sum.inr (q.2, q.1)) := (tfun_swap C B).comp (tfun_inr (.prod A C) (.prod B C))
  refine (((tfun_swap (.sum A B) C).comp (tfun_distr C A B)).comp (h1.copair h2)).congr ?_
  rintro ⟨x, c⟩
  cases x <;> rfl

/-! ## Claim `claim:bang-definable` -/

/-- **Claim `claim:bang-definable`.**  For every type `A`, the unique function `A → 1` is
definable by a term. -/
theorem bang_definable : ∀ A : Ty, IsRegularTermFun (A := A) (B := .one) (fun _ => ()) := by
  intro A
  induction A with
  | one => exact (tfun_id .one).congr (fun a => by cases a; rfl)
  | prod A B ihA _ => exact ((tfun_fst A B).comp ihA).congr (fun _ => rfl)
  | sum A B ihA ihB => exact (ihA.copair ihB).congr (fun x => by cases x <;> rfl)
  | list A ihA =>
      refine ((tfun_uncons A).comp
        (((tfun_id .one)).copair ((tfun_fst A (.list A)).comp ihA))).congr ?_
      intro l
      cases l with
      | nil => rfl
      | cons a l => rfl

/-- Every constant function is definable by a term. -/
lemma tfun_const (A B : Ty) (b : B.Elt) : IsRegularTermFun (A := A) (B := B) (fun _ => b) :=
  ((bang_definable A).comp (constTerm B b)).congr (fun _ => rfl)

/-- The term `1 → A` that invents an element of `A`, from the proof of Claim `claim:head`. -/
lemma tfun_invent (A : Ty) :
    IsRegularTermFun (A := .one) (B := A) (fun _ => (default : A.Elt)) := constTerm A default

/-! ## Lists: the empty list, singletons, concatenation, head and tail -/

lemma tfun_nil (A : Ty) : IsRegularTermFun (A := .one) (B := .list A) (fun _ => []) :=
  constTerm (.list A) []

/-- The singleton list. -/
lemma tfun_pure (A : Ty) : IsRegularTermFun (A := A) (B := .list A) (fun a => [a]) := by
  refine ((((tfun_id A).pair (tfun_const A (.list A) [])).comp
    (tfun_inr .one (.prod A (.list A)))).comp (tfun_cons A)).congr ?_
  intro a; rfl

/-- The concatenation of two lists, which the book calls `binconc`. -/
lemma tfun_append (A : Ty) :
    IsRegularTermFun (A := .prod (.list A) (.list A)) (B := .list A)
      (fun p : List A.Elt × List A.Elt => p.1 ++ p.2) := by
  refine (((tfun_prodMap (tfun_id (.list A)) (tfun_pure (.list A))).comp
      (tfun_inr .one (.prod (.list A) (.list (.list A))))).comp
      ((tfun_cons (.list A)).comp (tfun_concat A))).congr ?_
  have h : ∀ x y : List A.Elt, ([x, y] : List (List A.Elt)).flatten = x ++ y := by
    intro x y; simp
  rintro ⟨u, v⟩
  exact h u v

/-- **Claim `claim:head`.**  For every type `A` there is a term `A* → A` that returns the first
element of a nonempty list (and the default element of the type when the list is empty). -/
theorem claim_head (A : Ty) :
    IsRegularTermFun (A := .list A) (B := A) (fun l => l.headI) := by
  refine ((tfun_uncons A).comp ((tfun_invent A).copair (tfun_fst A (.list A)))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons a l => rfl

lemma tfun_tail (A : Ty) :
    IsRegularTermFun (A := .list A) (B := .list A) (fun l => l.tail) := by
  refine ((tfun_uncons A).comp
    ((tfun_const .one (.list A) []).copair (tfun_snd A (.list A)))).congr ?_
  intro l
  cases l with
  | nil => rfl
  | cons a l => rfl

/-- Prepending a fixed element to a list. -/
lemma tfun_consFixed (A : Ty) (a : A.Elt) :
    IsRegularTermFun (A := .list A) (B := .list A) (fun l => a :: l) := by
  refine ((((tfun_const (.list A) A a).pair (tfun_id (.list A))).comp
    (tfun_inr .one (.prod A (.list A)))).comp (tfun_cons A)).congr ?_
  intro l; rfl

/-! ## The inverse of split -/

/-- The inverse of the split function of Example `ex:split`: the concatenation of all the entries
in the left-to-right order. -/
def unsplitList {A B : Type} (p : List A × List (B × List A)) : List (A ⊕ B) :=
  p.1.map Sum.inl ++ (p.2.map (fun q => Sum.inr q.1 :: q.2.map Sum.inl)).flatten

lemma unsplitList_splitList {A B : Type} (l : List (A ⊕ B)) : unsplitList (splitList l) = l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      cases x with
      | inl a => simpa [unsplitList] using congrArg (fun v => Sum.inl a :: v) ih
      | inr b => simpa [unsplitList] using congrArg (fun v => Sum.inr b :: v) ih

/-- The inverse of split is definable by a term. -/
lemma tfun_unsplit (A B : Ty) :
    IsRegularTermFun (A := .prod (.list A) (.list (.prod B (.list A))))
      (B := .list (.sum A B)) (fun p => unsplitList p) := by
  have hentry : IsRegularTermFun (A := .prod B (.list A)) (B := .list (.sum A B))
      (fun q => Sum.inr q.1 :: (q.2.map Sum.inl)) := by
    refine ((((tfun_fst B (.list A)).comp
        ((tfun_inr A B).comp (tfun_pure (.sum A B)))).pair
      ((tfun_snd B (.list A)).comp ((tfun_inl A B).mapList))).comp
      (tfun_append (.sum A B))).congr ?_
    rintro ⟨b, v⟩
    rfl
  refine ((tfun_prodMap ((tfun_inl A B).mapList)
    (hentry.mapList.comp (tfun_concat (.sum A B)))).comp (tfun_append (.sum A B))).congr ?_
  rintro ⟨u, ps⟩
  rfl

/-! ## Types of the form `1 + ⋯ + 1`, and Claim `claim:finite-type-bijection-disjoint-units` -/

/-- The type `1 + ⋯ + 1` with `n + 1` copies of the unit type. -/
def Ty.units : ℕ → Ty
  | 0 => .one
  | n + 1 => .sum .one (Ty.units n)

lemma Ty.units_equiv_fin : ∀ n : ℕ, Nonempty ((Ty.units n).Elt ≃ Fin (n + 1))
  | 0 => ⟨Equiv.ofUnique Unit (Fin 1)⟩
  | n + 1 => by
      obtain ⟨e⟩ := Ty.units_equiv_fin n
      exact ⟨(Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) e).trans
        (finSumFinEquiv.trans (finCongr (by omega)))⟩

instance Ty.finite_units (n : ℕ) : Finite (Ty.units n).Elt := by
  obtain ⟨e⟩ := Ty.units_equiv_fin n
  exact Finite.of_equiv _ e.symm

/-- Every finite nonempty type is the set of elements of some type of the form `1 + ⋯ + 1`. -/
lemma exists_units_equiv (X : Type) [Finite X] [Nonempty X] :
    ∃ n : ℕ, Nonempty (X ≃ (Ty.units n).Elt) := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin X
  have hm : m ≠ 0 := by
    rintro rfl
    exact (e (Classical.arbitrary X)).elim0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨f⟩ := Ty.units_equiv_fin n
  exact ⟨n, ⟨e.trans f.symm⟩⟩

/-- Every finite nonempty type is the set of elements of some type. -/
lemma exists_ty_equiv (X : Type) [Finite X] [Nonempty X] :
    ∃ T : Ty, Nonempty (X ≃ T.Elt) ∧ Finite T.Elt := by
  obtain ⟨n, h⟩ := exists_units_equiv X
  exact ⟨Ty.units n, h, inferInstance⟩

/-- **Claim `claim:finite-type-bijection-disjoint-units`.**  Every finite type admits a bijection,
definable by a regular term in both directions, to a type of the form `1 + ⋯ + 1`. -/
theorem finite_type_bijection_disjoint_units (A : Ty) (hA : Finite A.Elt) :
    ∃ (n : ℕ) (e : A.Elt ≃ (Ty.units n).Elt),
      IsRegularTermFun (A := A) (B := Ty.units n) (fun a => e a) ∧
      IsRegularTermFun (A := Ty.units n) (B := A) (fun x => e.symm x) := by
  haveI := hA
  haveI : Nonempty A.Elt := ⟨default⟩
  obtain ⟨n, ⟨e⟩⟩ := exists_units_equiv A.Elt
  exact ⟨n, e, finite_domain_regular_list_function hA _,
    finite_domain_regular_list_function (Ty.finite_units n) _⟩

/-! ## Finite case distinction -/

private lemma tfun_unitsCases : ∀ (n : ℕ) {T U : Ty} {g : (Ty.units n).Elt → T.Elt → U.Elt},
    (∀ x, IsRegularTermFun (g x)) →
      IsRegularTermFun (A := .prod (Ty.units n) T) (B := U) (fun p => g p.1 p.2) := by
  intro n
  induction n with
  | zero =>
      intro T U g hg
      exact ((tfun_snd .one T).comp (hg ())).congr (fun p => by
        obtain ⟨u, t⟩ := p; cases u; rfl)
  | succ n ih =>
      intro T U g hg
      have h1 : IsRegularTermFun (A := .prod .one T) (B := U)
          (fun q => g (Sum.inl ()) q.2) := (tfun_snd .one T).comp (hg (Sum.inl ()))
      have h2 : IsRegularTermFun (A := .prod (Ty.units n) T) (B := U)
          (fun q => g (Sum.inr q.1) q.2) := ih (g := fun x t => g (Sum.inr x) t)
            (fun x => hg (Sum.inr x))
      refine ((tfun_distl .one (Ty.units n) T).comp (h1.copair h2)).congr ?_
      rintro ⟨x, t⟩
      cases x with
      | inl u => cases u; rfl
      | inr x => rfl

/-- **Finite case distinction.**  A term may branch on the value of a coordinate of a finite type,
carrying an arbitrary value along.  This is what the book means by "using distributivity and
co-pairing". -/
theorem tfun_finCases {F T U : Ty} (hF : Finite F.Elt) {g : F.Elt → T.Elt → U.Elt}
    (hg : ∀ x, IsRegularTermFun (g x)) :
    IsRegularTermFun (A := .prod F T) (B := U) (fun p => g p.1 p.2) := by
  obtain ⟨n, e, he, -⟩ := finite_type_bijection_disjoint_units F hF
  have h := tfun_unitsCases n (T := T) (U := U) (g := fun x t => g (e.symm x) t)
    (fun x => hg (e.symm x))
  refine ((tfun_prodMap he (tfun_id T)).comp h).congr ?_
  rintro ⟨x, t⟩
  simp

/-- A function with a finite domain, applied to a coordinate of a product, is definable. -/
lemma tfun_finCases' {F T U : Ty} (hF : Finite F.Elt) {g : F.Elt × T.Elt → U.Elt}
    (hg : ∀ x : F.Elt, IsRegularTermFun (fun t : T.Elt => g (x, t))) :
    IsRegularTermFun (A := .prod F T) (B := U) g :=
  (tfun_finCases hF (g := fun x t => g (x, t)) hg).congr (fun _ => rfl)

end Transducers
