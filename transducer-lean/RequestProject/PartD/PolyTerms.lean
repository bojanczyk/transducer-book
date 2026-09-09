/-
Definition `def:polyregular-terms` (polyregular terms) of Section *A functional programming
language* of *Transducers* (M. Bojańczyk).

A *polyregular term* is a term built using the atomic functions and the combinators of Definition
`def:regular-terms`, extended by one more atomic function

    A*  --split-->  (A* × A*)*
    [a₁,…,aₙ] ↦ [([a₁,…,aₙ],[]), ([a₁,…,a_{n-1}],[aₙ]), …, ([],[a₁,…,aₙ])],

which lists all the ways of cutting the input list into a prefix and a suffix, the prefix getting
shorter as one moves to the right.  The semantics of the new atomic function is
`Transducers.splitsList` and the syntax of the terms is `Transducers.PolyTerm`, which repeats the
constructors of `Transducers.RegTerm` of `RequestProject/PartC/CombTerms.lean` and adds one.  The
repetition is deliberate: a polyregular term *is* a regular term with one more atomic function, and
`Transducers.PolyTerm.ofReg` embeds the regular terms into the polyregular ones, preserving the
semantics (`Transducers.PolyTerm.eval_ofReg`), so that every function defined by a regular term is
also defined by a polyregular one.
-/
import RequestProject.PartC.CombRepr

namespace Transducers

/-! ## The new atomic function -/

/-- **The atomic function `split` of Definition `def:polyregular-terms`.**  All the ways of cutting
a list into a prefix and a suffix, with the prefix getting shorter from left to right: the first
entry is `(l, [])` and the last one is `([], l)`. -/
def splitsList {X : Type} (l : List X) : List (List X × List X) :=
  (List.range (l.length + 1)).reverse.map (fun i => (l.take i, l.drop i))

@[simp] lemma splitsList_nil {X : Type} : splitsList ([] : List X) = [([], [])] := rfl

lemma splitsList_reverse {X : Type} (l : List X) :
    (splitsList l).reverse = (List.range (l.length + 1)).map (fun i => (l.take i, l.drop i)) := by
  rw [splitsList, ← List.map_reverse, List.reverse_reverse]

lemma splitsList_length {X : Type} (l : List X) : (splitsList l).length = l.length + 1 := by
  simp [splitsList]

/-! ## Polyregular terms (Definition `def:polyregular-terms`) -/

/-- **Definition `def:polyregular-terms` (Polyregular term).**  The syntax of the polyregular
terms: the atomic terms and the combinators of Definition `def:regular-terms`, together with the
new atomic function `split`. -/
inductive PolyTerm : Ty → Ty → Type
  /-- Identity `A → A`. -/
  | id (A : Ty) : PolyTerm A A
  /-- First projection `A × B → A`. -/
  | fst (A B : Ty) : PolyTerm (.prod A B) A
  /-- Second projection `A × B → B`. -/
  | snd (A B : Ty) : PolyTerm (.prod A B) B
  /-- Left co-projection `A → A + B`. -/
  | inl (A B : Ty) : PolyTerm A (.sum A B)
  /-- Right co-projection `B → A + B`. -/
  | inr (A B : Ty) : PolyTerm B (.sum A B)
  /-- Diagonal `A → A × A`. -/
  | diag (A : Ty) : PolyTerm A (.prod A A)
  /-- Co-diagonal `A + A → A`. -/
  | codiag (A : Ty) : PolyTerm (.sum A A) A
  /-- Distributivity `A × (B + C) → (A × B) + (A × C)`. -/
  | distr (A B C : Ty) : PolyTerm (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C))
  /-- The list constructor `1 + A × A* → A*`. -/
  | cons (A : Ty) : PolyTerm (.sum .one (.prod A (.list A))) (.list A)
  /-- The list deconstructor `A* → 1 + A × A*`. -/
  | uncons (A : Ty) : PolyTerm (.list A) (.sum .one (.prod A (.list A)))
  /-- Reverse `A* → A*`. -/
  | reverse (A : Ty) : PolyTerm (.list A) (.list A)
  /-- Concatenation `A** → A*`. -/
  | concat (A : Ty) : PolyTerm (.list (.list A)) (.list A)
  /-- Split `(A + B)* → A* × (B × A*)*` of Example `ex:block`. -/
  | split (A B : Ty) : PolyTerm (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A))))
  /-- Group prefix multiplication `G* → G*`, for a group whose underlying set is a finite type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) : PolyTerm (.list G) (.list G)
  /-- **The new atomic function** `A* → (A* × A*)*` of Definition `def:polyregular-terms`. -/
  | splits (A : Ty) : PolyTerm (.list A) (.list (.prod (.list A) (.list A)))
  /-- Composition. -/
  | comp {A B C : Ty} : PolyTerm A B → PolyTerm B C → PolyTerm A C
  /-- Functoriality for products: `f₁ × f₂`. -/
  | prodMap {A₁ A₂ B₁ B₂ : Ty} :
      PolyTerm A₁ B₁ → PolyTerm A₂ B₂ → PolyTerm (.prod A₁ A₂) (.prod B₁ B₂)
  /-- Functoriality for co-products: `f₁ + f₂`. -/
  | sumMap {A₁ A₂ B₁ B₂ : Ty} :
      PolyTerm A₁ B₁ → PolyTerm A₂ B₂ → PolyTerm (.sum A₁ A₂) (.sum B₁ B₂)
  /-- Functoriality for lists: `f*`. -/
  | map {A B : Ty} : PolyTerm A B → PolyTerm (.list A) (.list B)

/-- The semantics of a polyregular term: the type-to-type function that it defines. -/
def PolyTerm.eval : {A B : Ty} → PolyTerm A B → A.Elt → B.Elt
  | _, _, .id _ => fun x => x
  | _, _, .fst _ _ => fun x => x.1
  | _, _, .snd _ _ => fun x => x.2
  | _, _, .inl _ _ => fun x => Sum.inl x
  | _, _, .inr _ _ => fun x => Sum.inr x
  | _, _, .diag _ => fun x => (x, x)
  | _, _, .codiag _ => fun x => Sum.elim (fun a => a) (fun a => a) x
  | _, _, .distr _ _ _ => fun x =>
      Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2
  | _, _, .cons _ => fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x
  | _, _, .uncons _ => fun l => match l with
      | [] => Sum.inl ()
      | a :: l' => Sum.inr (a, l')
  | _, _, .reverse _ => fun l => l.reverse
  | _, _, .concat _ => fun l => l.flatten
  | _, _, .split _ _ => fun l => splitList l
  | _, _, .pref _ grp _ => fun l => @prefixProd _ (@Group.toDivisionMonoid _ grp).toMonoid l
  | _, _, .splits _ => fun l => splitsList l
  | _, _, .comp s t => fun x => t.eval (s.eval x)
  | _, _, .prodMap s t => fun p => (s.eval p.1, t.eval p.2)
  | _, _, .sumMap s t => fun x => Sum.map s.eval t.eval x
  | _, _, .map t => fun l => l.map t.eval

/-- A type-to-type function is *defined by a polyregular term* if it is the semantics of one. -/
def IsPolyregularTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop := ∃ t : PolyTerm A B, t.eval = f

/-! ## The regular terms are polyregular terms -/

/-- Every regular term is a polyregular term. -/
def PolyTerm.ofReg : {A B : Ty} → RegTerm A B → PolyTerm A B
  | _, _, .id A => .id A
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
  | _, _, .comp s t => .comp (ofReg s) (ofReg t)
  | _, _, .prodMap s t => .prodMap (ofReg s) (ofReg t)
  | _, _, .sumMap s t => .sumMap (ofReg s) (ofReg t)
  | _, _, .map t => .map (ofReg t)

/-- The embedding of the regular terms into the polyregular terms preserves the semantics. -/
theorem PolyTerm.eval_ofReg : ∀ {A B : Ty} (t : RegTerm A B), (PolyTerm.ofReg t).eval = t.eval
  | _, _, .id _ => rfl
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
      show (PolyTerm.comp (ofReg s) (ofReg t)).eval = _
      funext x
      show (ofReg t).eval ((ofReg s).eval x) = t.eval (s.eval x)
      rw [eval_ofReg s, eval_ofReg t]
  | _, _, .prodMap s t => by
      funext p
      show ((ofReg s).eval p.1, (ofReg t).eval p.2) = (s.eval p.1, t.eval p.2)
      rw [eval_ofReg s, eval_ofReg t]
  | _, _, .sumMap s t => by
      funext x
      show Sum.map (ofReg s).eval (ofReg t).eval x = Sum.map s.eval t.eval x
      rw [eval_ofReg s, eval_ofReg t]
  | _, _, .map t => by
      funext l
      show l.map (ofReg t).eval = l.map t.eval
      rw [eval_ofReg t]

/-! ## Elementary closure properties of the definable functions -/

/-- Every function defined by a regular term is defined by a polyregular term. -/
theorem IsPolyregularTermFun.of_regularTerm {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsRegularTermFun f) : IsPolyregularTermFun f := by
  obtain ⟨t, ht⟩ := h
  exact ⟨PolyTerm.ofReg t, by rw [PolyTerm.eval_ofReg, ht]⟩

lemma IsPolyregularTermFun.of_term {A B : Ty} (t : PolyTerm A B) :
    IsPolyregularTermFun t.eval := ⟨t, rfl⟩

lemma IsPolyregularTermFun.congr {A B : Ty} {f g : A.Elt → B.Elt} (h : IsPolyregularTermFun f)
    (hfg : ∀ a, f a = g a) : IsPolyregularTermFun g := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, by rw [ht]; exact funext hfg⟩

lemma IsPolyregularTermFun.comp {A B C : Ty} {f : A.Elt → B.Elt} {g : B.Elt → C.Elt}
    (hf : IsPolyregularTermFun f) (hg : IsPolyregularTermFun g) :
    IsPolyregularTermFun (fun a => g (f a)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.comp t, by
    funext a
    show t.eval (s.eval a) = g (f a)
    rw [hs, ht]⟩

lemma IsPolyregularTermFun.mapList {A B : Ty} {f : A.Elt → B.Elt} (hf : IsPolyregularTermFun f) :
    IsPolyregularTermFun (A := .list A) (B := .list B) (fun l => l.map f) := by
  obtain ⟨t, ht⟩ := hf
  exact ⟨t.map, by
    funext l
    show l.map t.eval = l.map f
    rw [ht]⟩

lemma IsPolyregularTermFun.prodMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsPolyregularTermFun f) (hg : IsPolyregularTermFun g) :
    IsPolyregularTermFun (A := .prod A₁ A₂) (B := .prod B₁ B₂) (fun p => (f p.1, g p.2)) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨s.prodMap t, by
    funext p
    show (s.eval p.1, t.eval p.2) = (f p.1, g p.2)
    rw [hs, ht]⟩

/-- The pairing of two functions defined by polyregular terms. -/
lemma IsPolyregularTermFun.pair {A B C : Ty} {f : A.Elt → B.Elt} {g : A.Elt → C.Elt}
    (hf : IsPolyregularTermFun f) (hg : IsPolyregularTermFun g) :
    IsPolyregularTermFun (A := A) (B := .prod B C) (fun a => (f a, g a)) :=
  ((IsPolyregularTermFun.of_term (PolyTerm.diag A)).comp (hf.prodMap hg)).congr (fun _ => rfl)

end Transducers
