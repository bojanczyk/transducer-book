/-
Rational terms, the variant of the regular terms of Definition `def:regular-terms` that Theorem
`thm:rational-terms` of Section *Combinators* of *Transducers* (M. Bojańczyk) introduces.

The theorem describes the variant in words: keep the atomic functions and the combinators of
Definition `def:regular-terms`, remove reverse and the diagonal, and add

* adjoining units, `A → A × 1` and `A → 1 × A`;
* left distributivity, `(A + B) × C → (A × C) + (B × C)`;
* the list deconstructor on the right, `A* → 1 + A* × A`.

`Transducers.RatTerm` is that list of constructors, and `Transducers.RatTerm.eval` is the
semantics, exactly as `Transducers.RegTerm` and `Transducers.RegTerm.eval` are for the regular
terms in `CombTerms.lean`.  The two conventions of that file are kept here: group prefix
multiplication carries the group structure and the finiteness of its underlying type, and every
atomic term is indexed by the types it is stated for.

Removing the diagonal removes pairing, which is why the three atomic functions are added; removing
reverse removes the symmetry between the left-to-right and the right-to-left machines, which is
what the list deconstructor on the right is for.
-/
import RequestProject.PartC.CombTerms

namespace Transducers

/-! ## Rationality under string representation, composed -/

/-- Rationality under string representation is preserved by composition. -/
lemma IsRationalUnderRepr.comp {A B C : Ty} {f : A.Elt → B.Elt} {g : B.Elt → C.Elt}
    (hf : IsRationalUnderRepr f) (hg : IsRationalUnderRepr g) :
    IsRationalUnderRepr (fun a => g (f a)) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => g' (f' w), isRationalFun_comp hf' hg', fun a => ?_⟩
  show g' (f' (A.repr a)) = C.repr (g (f a))
  rw [hfe a, hge (f a)]

lemma IsRationalUnderRepr.congr {A B : Ty} {f g : A.Elt → B.Elt} (h : IsRationalUnderRepr f)
    (hfg : ∀ a, f a = g a) : IsRationalUnderRepr g := by
  obtain ⟨f', hf', hfe⟩ := h
  exact ⟨f', hf', fun a => by rw [hfe a, hfg a]⟩

/-! ## The list deconstructor on the right -/

/-- The semantics of `unsnoc`: a list is either empty, or it is a list together with its last
entry. -/
def unsnocList {α : Type} : List α → Unit ⊕ (List α × α)
  | [] => Sum.inl ()
  | a :: l =>
      match unsnocList l with
      | Sum.inl _ => Sum.inr ([], a)
      | Sum.inr (u, b) => Sum.inr (a :: u, b)

@[simp] lemma unsnocList_nil {α : Type} : unsnocList ([] : List α) = Sum.inl () := rfl

@[simp] lemma unsnocList_singleton {α : Type} (a : α) : unsnocList [a] = Sum.inr ([], a) := rfl

lemma unsnocList_append_singleton {α : Type} (u : List α) (a : α) :
    unsnocList (u ++ [a]) = Sum.inr (u, a) := by
  induction u with
  | nil => rfl
  | cons b u ih => rw [List.cons_append, unsnocList, ih]

/-! ## Rational terms (Theorem `thm:rational-terms`) -/

/-- **Theorem `thm:rational-terms` (rational terms).**  The syntax of the rational terms: the
atomic terms and combinators of Definition `def:regular-terms` without reverse and without the
diagonal, together with adjoining units, left distributivity and the list deconstructor on the
right. -/
inductive RatTerm : Ty → Ty → Type
  /-- Identity `A → A`. -/
  | id (A : Ty) : RatTerm A A
  /-- First projection `A × B → A`. -/
  | fst (A B : Ty) : RatTerm (.prod A B) A
  /-- Second projection `A × B → B`. -/
  | snd (A B : Ty) : RatTerm (.prod A B) B
  /-- Left co-projection `A → A + B`. -/
  | inl (A B : Ty) : RatTerm A (.sum A B)
  /-- Right co-projection `B → A + B`. -/
  | inr (A B : Ty) : RatTerm B (.sum A B)
  /-- Co-diagonal `A + A → A`. -/
  | codiag (A : Ty) : RatTerm (.sum A A) A
  /-- Adjoining a unit on the right, `A → A × 1`. -/
  | appendOne (A : Ty) : RatTerm A (.prod A .one)
  /-- Adjoining a unit on the left, `A → 1 × A`. -/
  | prependOne (A : Ty) : RatTerm A (.prod .one A)
  /-- Distributivity `A × (B + C) → (A × B) + (A × C)`. -/
  | distr (A B C : Ty) : RatTerm (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C))
  /-- Left distributivity `(A + B) × C → (A × C) + (B × C)`. -/
  | distl (A B C : Ty) : RatTerm (.prod (.sum A B) C) (.sum (.prod A C) (.prod B C))
  /-- The list constructor `1 + A × A* → A*`. -/
  | cons (A : Ty) : RatTerm (.sum .one (.prod A (.list A))) (.list A)
  /-- The list deconstructor `A* → 1 + A × A*`. -/
  | uncons (A : Ty) : RatTerm (.list A) (.sum .one (.prod A (.list A)))
  /-- The list deconstructor on the right, `A* → 1 + A* × A`. -/
  | unsnoc (A : Ty) : RatTerm (.list A) (.sum .one (.prod (.list A) A))
  /-- Concatenation `A** → A*`. -/
  | concat (A : Ty) : RatTerm (.list (.list A)) (.list A)
  /-- Split `(A + B)* → A* × (B × A*)*`. -/
  | split (A B : Ty) : RatTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A))))
  /-- Group prefix multiplication `G* → G*`, for a group whose underlying set is a finite type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : RatTerm (.list G) (.list G)
  /-- Composition. -/
  | comp {A B C : Ty} : RatTerm A B → RatTerm B C → RatTerm A C
  /-- Functoriality for products: `f₁ × f₂`. -/
  | prodMap {A₁ A₂ B₁ B₂ : Ty} :
      RatTerm A₁ B₁ → RatTerm A₂ B₂ → RatTerm (.prod A₁ A₂) (.prod B₁ B₂)
  /-- Functoriality for co-products: `f₁ + f₂`. -/
  | sumMap {A₁ A₂ B₁ B₂ : Ty} :
      RatTerm A₁ B₁ → RatTerm A₂ B₂ → RatTerm (.sum A₁ A₂) (.sum B₁ B₂)
  /-- Functoriality for lists: `f*`. -/
  | map {A B : Ty} : RatTerm A B → RatTerm (.list A) (.list B)

/-- The semantics of a rational term: the type-to-type function that it defines. -/
def RatTerm.eval : {A B : Ty} → RatTerm A B → A.Elt → B.Elt
  | _, _, .id _ => fun x => x
  | _, _, .fst _ _ => fun x => x.1
  | _, _, .snd _ _ => fun x => x.2
  | _, _, .inl _ _ => fun x => Sum.inl x
  | _, _, .inr _ _ => fun x => Sum.inr x
  | _, _, .codiag _ => fun x => Sum.elim (fun a => a) (fun a => a) x
  | _, _, .appendOne _ => fun x => (x, ())
  | _, _, .prependOne _ => fun x => ((), x)
  | _, _, .distr _ _ _ => fun x =>
      Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2
  | _, _, .distl _ _ _ => fun x =>
      Sum.elim (fun a => Sum.inl (a, x.2)) (fun b => Sum.inr (b, x.2)) x.1
  | _, _, .cons _ => fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x
  | _, _, .uncons _ => fun l => match l with
      | [] => Sum.inl ()
      | a :: l' => Sum.inr (a, l')
  | _, _, .unsnoc _ => fun l => unsnocList l
  | _, _, .concat _ => fun l => l.flatten
  | _, _, .split _ _ => fun l => splitList l
  | _, _, .pref _ grp _ => fun l => @prefixProd _ (@Group.toDivisionMonoid _ grp).toMonoid l
  | _, _, .comp s t => fun x => t.eval (s.eval x)
  | _, _, .prodMap s t => fun p => (s.eval p.1, t.eval p.2)
  | _, _, .sumMap s t => fun x => Sum.map s.eval t.eval x
  | _, _, .map t => fun l => l.map t.eval

/-- A type-to-type function is *defined by a rational term* if it is the semantics of one. -/
def IsRatTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop := ∃ t : RatTerm A B, t.eval = f

lemma IsRatTermFun.of_term {A B : Ty} (t : RatTerm A B) : IsRatTermFun t.eval := ⟨t, rfl⟩

lemma IsRatTermFun.congr {A B : Ty} {f g : A.Elt → B.Elt} (h : IsRatTermFun f)
    (hfg : ∀ a, f a = g a) : IsRatTermFun g := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [ht]; exact funext hfg⟩

lemma IsRatTermFun.comp {A B C : Ty} {f : A.Elt → B.Elt} {g : B.Elt → C.Elt}
    (hf : IsRatTermFun f) (hg : IsRatTermFun g) : IsRatTermFun (fun a => g (f a)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.comp t, by funext a; rw [show (s.comp t).eval a = t.eval (s.eval a) from rfl, hs, ht]⟩

/-- The functoriality combinator `f₁ × f₂`. -/
lemma IsRatTermFun.prodMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsRatTermFun f) (hg : IsRatTermFun g) :
    IsRatTermFun (A := Ty.prod A₁ A₂) (B := Ty.prod B₁ B₂) (fun p => (f p.1, g p.2)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.prodMap t, by
    funext p
    rw [show (s.prodMap t).eval p = (s.eval p.1, t.eval p.2) from rfl, hs, ht]⟩

/-- The functoriality combinator `f₁ + f₂`. -/
lemma IsRatTermFun.sumMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsRatTermFun f) (hg : IsRatTermFun g) :
    IsRatTermFun (A := Ty.sum A₁ A₂) (B := Ty.sum B₁ B₂) (fun x => Sum.map f g x) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.sumMap t, by
    funext x
    rw [show (s.sumMap t).eval x = Sum.map s.eval t.eval x from rfl, hs, ht]⟩

/-- The functoriality combinator `f*`. -/
lemma IsRatTermFun.mapList {A B : Ty} {f : A.Elt → B.Elt} (hf : IsRatTermFun f) :
    IsRatTermFun (A := Ty.list A) (B := Ty.list B) (fun l => l.map f) := by
  obtain ⟨t, ht⟩ := hf
  exact ⟨t.map, by funext l; rw [show (t.map).eval l = l.map t.eval from rfl, ht]⟩

/-- **Co-pairing.**  As for the regular terms, the functions defined by rational terms are closed
under co-pairing: `f₁ + f₂` followed by the co-diagonal.  (Pairing, which the regular terms get
from the diagonal, is *not* available here, and must not be: it would give string duplication.) -/
theorem IsRatTermFun.copair {A B C : Ty} {f : A.Elt → C.Elt} {g : B.Elt → C.Elt}
    (hf : IsRatTermFun f) (hg : IsRatTermFun g) :
    IsRatTermFun (A := Ty.sum A B) (B := C) (Sum.elim f g) :=
  ((hf.sumMap hg).comp (IsRatTermFun.of_term (RatTerm.codiag C))).congr
    (fun x => by cases x <;> rfl)

/-! ## The atomic terms, as statements about `IsRatTermFun` -/

lemma rtfun_id (A : Ty) : IsRatTermFun (A := A) (B := A) (fun a => a) := ⟨RatTerm.id A, rfl⟩

lemma rtfun_fst (A B : Ty) :
    IsRatTermFun (A := .prod A B) (B := A) (fun p => p.1) := ⟨RatTerm.fst A B, rfl⟩

lemma rtfun_snd (A B : Ty) :
    IsRatTermFun (A := .prod A B) (B := B) (fun p => p.2) := ⟨RatTerm.snd A B, rfl⟩

lemma rtfun_inl (A B : Ty) :
    IsRatTermFun (A := A) (B := .sum A B) (fun a => Sum.inl a) := ⟨RatTerm.inl A B, rfl⟩

lemma rtfun_inr (A B : Ty) :
    IsRatTermFun (A := B) (B := .sum A B) (fun b => Sum.inr b) := ⟨RatTerm.inr A B, rfl⟩

lemma rtfun_appendOne (A : Ty) :
    IsRatTermFun (A := A) (B := .prod A .one) (fun a => (a, ())) := ⟨RatTerm.appendOne A, rfl⟩

lemma rtfun_prependOne (A : Ty) :
    IsRatTermFun (A := A) (B := .prod .one A) (fun a => ((), a)) := ⟨RatTerm.prependOne A, rfl⟩

lemma rtfun_distr (A B C : Ty) :
    IsRatTermFun (A := .prod A (.sum B C)) (B := .sum (.prod A B) (.prod A C))
      (fun x => Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2) :=
  ⟨RatTerm.distr A B C, rfl⟩

lemma rtfun_distl (A B C : Ty) :
    IsRatTermFun (A := .prod (.sum A B) C) (B := .sum (.prod A C) (.prod B C))
      (fun x => Sum.elim (fun a => Sum.inl (a, x.2)) (fun b => Sum.inr (b, x.2)) x.1) :=
  ⟨RatTerm.distl A B C, rfl⟩

lemma rtfun_cons (A : Ty) :
    IsRatTermFun (A := .sum .one (.prod A (.list A))) (B := .list A)
      (fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x) := ⟨RatTerm.cons A, rfl⟩

lemma rtfun_uncons (A : Ty) :
    IsRatTermFun (A := .list A) (B := .sum .one (.prod A (.list A)))
      (fun l => match l with | [] => Sum.inl () | a :: l' => Sum.inr (a, l')) :=
  ⟨RatTerm.uncons A, rfl⟩

lemma rtfun_unsnoc (A : Ty) :
    IsRatTermFun (A := .list A) (B := .sum .one (.prod (.list A) A))
      (fun l => unsnocList l) := ⟨RatTerm.unsnoc A, rfl⟩

lemma rtfun_concat (A : Ty) :
    IsRatTermFun (A := .list (.list A)) (B := .list A) (fun l => l.flatten) :=
  ⟨RatTerm.concat A, rfl⟩

lemma rtfun_split (A B : Ty) :
    IsRatTermFun (A := .list (.sum A B)) (B := .prod (.list A) (.list (.prod B (.list A))))
      (fun l => splitList l) := ⟨RatTerm.split A B, rfl⟩

end Transducers
