/-
Part D, Section *A functional programming language*: Definition `def:higher-order-types` and
Definition `def:higher-order-terms`.

The higher-order types (`Transducers.HTy`) extend the grammar of Definition `def:types` -- the type
`Transducers.Ty` of `RequestProject/PartC/CombTypes.lean` -- by an arrow constructor, and the
higher-order polyregular terms (`Transducers.HTerm`) are the simply typed lambda calculus over the
atomic functions of Definition `def:polyregular-terms`, with `map` and `either` added.

Three decisions had to be taken when rendering Definition `def:higher-order-terms` in Lean; all
three are recorded in `THEOREMS.md` as well.

* **Variables.**  The book fixes a set of variables, each hard-wired with a type, and later --
  when terms have to be written as strings -- switches to De Bruijn indices.  The formalisation
  uses De Bruijn indices throughout: a term lives in a context `Γ : List HTy` of the types of the
  variables that are in scope, and a variable is a position in that context (`Transducers.HVar`).
  This is the standard intrinsically typed presentation, and it is the same language: the terms of
  the empty context are exactly the closed terms of the book.

* **List terms.**  The book's term constructor for lists takes `n` terms `a₁,…,aₙ : A` at once and
  builds `[a₁,…,aₙ] : A*`.  Here the same terms are built by the two constructors
  `Transducers.HTerm.nil` and `Transducers.HTerm.cons`, whose cons-chains are exactly the book's
  list terms, and which are much more comfortable to recurse over.

* **Group types.**  The atomic functions `pref` (group prefix multiplication, kept from Definition
  `def:regular-terms`) and `mult` (the product of a list, the atomic function of Lemma
  `lem:fewer-atomic`) are available only for *arrow-free* group types, that is, for a type `G` of
  Definition `def:types` with a finite group structure on the set it represents.  This is the only
  restriction of the book's "the atomic functions are now also allowed for higher-order types":
  every other atomic function is available at all higher-order types.  A group structure on a set
  of functions would have no meaning in the book, where the group is part of the data of the
  atomic function and is always a concrete finite group.

The semantics is the expected one: `Transducers.HTy.Sem` interprets a type as a set, the arrow
constructor as the set of *all* functions, and `Transducers.HTerm.eval` interprets a term of type
`A` in a context `Γ` as a function from the valuations of `Γ` to `A`.
-/
import RequestProject.PartD.PolyTerms

namespace Transducers

/-! ## Two facts about the atomic functions `split` and the block split -/

/-- Cutting a list into a prefix and a suffix commutes with `map`. -/
theorem splitsList_map {X Y : Type} (f : X → Y) (l : List X) :
    splitsList (l.map f) = (splitsList l).map (fun z => (z.1.map f, z.2.map f)) := by
  simp [splitsList, List.map_map, Function.comp_def, List.map_take, List.map_drop]

/-- The block split of Example `ex:block` commutes with `map`. -/
theorem splitList_map {A B A' B' : Type} (f : A → A') (g : B → B') :
    ∀ l : List (A ⊕ B), splitList (l.map (Sum.map f g))
      = ((splitList l).1.map f, (splitList l).2.map (fun z => (g z.1, z.2.map f)))
  | [] => rfl
  | Sum.inl a :: l => by simp [splitList_map f g l]
  | Sum.inr b :: l => by simp [splitList_map f g l]

/-! ## Higher-order types (Definition `def:higher-order-types`) -/

/-- **Definition `def:higher-order-types` (Higher-order types).**  The grammar of Definition
`def:types` -- the unit type, products, co-products and lists -- extended by an arrow
constructor. -/
inductive HTy : Type
  | one : HTy
  | prod : HTy → HTy → HTy
  | sum : HTy → HTy → HTy
  | list : HTy → HTy
  | arrow : HTy → HTy → HTy
  deriving DecidableEq

/-- The set represented by a higher-order type; the arrow constructor represents the set of all
total functions. -/
def HTy.Sem : HTy → Type
  | .one => Unit
  | .prod A B => A.Sem × B.Sem
  | .sum A B => A.Sem ⊕ B.Sem
  | .list A => List A.Sem
  | .arrow A B => A.Sem → B.Sem

/-- A higher-order type is *arrow-free* if the arrow constructor does not occur in it. -/
def HTy.ArrowFree : HTy → Prop
  | .one => True
  | .prod A B => A.ArrowFree ∧ B.ArrowFree
  | .sum A B => A.ArrowFree ∧ B.ArrowFree
  | .list A => A.ArrowFree
  | .arrow _ _ => False

/-- Every type of Definition `def:types` is a higher-order type. -/
def HTy.ofTy : Ty → HTy
  | .one => .one
  | .prod A B => .prod (ofTy A) (ofTy B)
  | .sum A B => .sum (ofTy A) (ofTy B)
  | .list A => .list (ofTy A)

lemma HTy.arrowFree_ofTy : ∀ A : Ty, (HTy.ofTy A).ArrowFree
  | .one => trivial
  | .prod A B => ⟨arrowFree_ofTy A, arrowFree_ofTy B⟩
  | .sum A B => ⟨arrowFree_ofTy A, arrowFree_ofTy B⟩
  | .list A => arrowFree_ofTy A

/-- Conversely, every arrow-free higher-order type comes from a type of Definition `def:types`. -/
lemma HTy.exists_ofTy : ∀ (H : HTy), H.ArrowFree → ∃ A : Ty, H = HTy.ofTy A := by
  intro H
  induction H with
  | one => exact fun _ => ⟨.one, rfl⟩
  | prod A B ihA ihB =>
      rintro ⟨hA, hB⟩
      obtain ⟨A', rfl⟩ := ihA hA
      obtain ⟨B', rfl⟩ := ihB hB
      exact ⟨.prod A' B', rfl⟩
  | sum A B ihA ihB =>
      rintro ⟨hA, hB⟩
      obtain ⟨A', rfl⟩ := ihA hA
      obtain ⟨B', rfl⟩ := ihB hB
      exact ⟨.sum A' B', rfl⟩
  | list A ihA =>
      intro hA
      obtain ⟨A', rfl⟩ := ihA hA
      exact ⟨.list A', rfl⟩
  | arrow A B _ _ => exact fun h => h.elim

/-- The set represented by an arrow-free higher-order type is the set represented by the
corresponding type of Definition `def:types`; this is the translation in one direction. -/
def HTy.toElt : (A : Ty) → (HTy.ofTy A).Sem → A.Elt
  | .one, x => x
  | .prod A B, x => (toElt A x.1, toElt B x.2)
  | .sum A B, x => Sum.map (toElt A) (toElt B) x
  | .list A, l => l.map (toElt A)

/-- The translation in the other direction. -/
def HTy.ofElt : (A : Ty) → A.Elt → (HTy.ofTy A).Sem
  | .one, x => x
  | .prod A B, x => (ofElt A x.1, ofElt B x.2)
  | .sum A B, x => Sum.map (ofElt A) (ofElt B) x
  | .list A, l => l.map (ofElt A)

@[simp] lemma HTy.toElt_ofElt : ∀ (A : Ty) (x : A.Elt), HTy.toElt A (HTy.ofElt A x) = x
  | .one, _ => rfl
  | .prod A B, x => by
      obtain ⟨x1, x2⟩ := x
      show (HTy.toElt A (HTy.ofElt A x1), HTy.toElt B (HTy.ofElt B x2)) = (x1, x2)
      rw [toElt_ofElt A, toElt_ofElt B]
  | .sum A B, x => by
      cases x with
      | inl a => show Sum.inl (HTy.toElt A (HTy.ofElt A a)) = _; rw [toElt_ofElt A]
      | inr b => show Sum.inr (HTy.toElt B (HTy.ofElt B b)) = _; rw [toElt_ofElt B]
  | .list A, l => by
      show (l.map (HTy.ofElt A)).map (HTy.toElt A) = l
      rw [List.map_map]
      rw [show ((HTy.toElt A) ∘ (HTy.ofElt A)) = id from funext (fun x => toElt_ofElt A x)]
      exact List.map_id l

@[simp] lemma HTy.ofElt_toElt : ∀ (A : Ty) (x : (HTy.ofTy A).Sem), HTy.ofElt A (HTy.toElt A x) = x
  | .one, x => rfl
  | .prod A B, x => by
      obtain ⟨x1, x2⟩ := x
      show (HTy.ofElt A (HTy.toElt A x1), HTy.ofElt B (HTy.toElt B x2)) = (x1, x2)
      rw [ofElt_toElt A, ofElt_toElt B]
  | .sum A B, x => by
      cases x with
      | inl a => show Sum.inl (HTy.ofElt A (HTy.toElt A a)) = _; rw [ofElt_toElt A]
      | inr b => show Sum.inr (HTy.ofElt B (HTy.toElt B b)) = _; rw [ofElt_toElt B]
  | .list A, l => by
      show (l.map (HTy.toElt A)).map (HTy.ofElt A) = l
      rw [List.map_map]
      rw [show ((HTy.ofElt A) ∘ (HTy.toElt A)) = id from funext (fun x => ofElt_toElt A x)]
      exact List.map_id l

/-! ## The atomic functions -/

/-- The product of a list of elements of an arrow-free group type. -/
def groupProd (G : Ty) (grp : Group G.Elt) (l : List (HTy.ofTy G).Sem) : (HTy.ofTy G).Sem :=
  letI := grp
  HTy.ofElt G (l.map (HTy.toElt G)).prod

/-- The prefix products of a list of elements of an arrow-free group type. -/
def groupPrefixProd (G : Ty) (grp : Group G.Elt) (l : List (HTy.ofTy G).Sem) :
    List (HTy.ofTy G).Sem :=
  letI := grp
  (prefixProd (l.map (HTy.toElt G))).map (HTy.ofElt G)

/-- **The atomic functions of Definition `def:higher-order-terms`.**  The atomic functions of
Definition `def:polyregular-terms`, at higher-order types, together with `map` and `either`.  An
atomic function is indexed by its (higher-order) type. -/
inductive HAtom : HTy → Type
  /-- Identity `A → A`. -/
  | idA (A : HTy) : HAtom (.arrow A A)
  /-- First projection `A × B → A`. -/
  | fst (A B : HTy) : HAtom (.arrow (.prod A B) A)
  /-- Second projection `A × B → B`. -/
  | snd (A B : HTy) : HAtom (.arrow (.prod A B) B)
  /-- Left co-projection `A → A + B`. -/
  | inl (A B : HTy) : HAtom (.arrow A (.sum A B))
  /-- Right co-projection `B → A + B`. -/
  | inr (A B : HTy) : HAtom (.arrow B (.sum A B))
  /-- Diagonal `A → A × A`. -/
  | diag (A : HTy) : HAtom (.arrow A (.prod A A))
  /-- Co-diagonal `A + A → A`. -/
  | codiag (A : HTy) : HAtom (.arrow (.sum A A) A)
  /-- Distributivity `A × (B + C) → A × B + A × C`. -/
  | distr (A B C : HTy) :
      HAtom (.arrow (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C)))
  /-- The list constructor `1 + A × A* → A*`. -/
  | consA (A : HTy) : HAtom (.arrow (.sum .one (.prod A (.list A))) (.list A))
  /-- The list deconstructor `A* → 1 + A × A*`. -/
  | uncons (A : HTy) : HAtom (.arrow (.list A) (.sum .one (.prod A (.list A))))
  /-- Reverse `A* → A*`. -/
  | reverse (A : HTy) : HAtom (.arrow (.list A) (.list A))
  /-- Concatenation `A** → A*`. -/
  | concat (A : HTy) : HAtom (.arrow (.list (.list A)) (.list A))
  /-- The block split `(A + B)* → A* × (B × A*)*` of Example `ex:block`. -/
  | blockSplit (A B : HTy) :
      HAtom (.arrow (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A)))))
  /-- Group prefix multiplication `G* → G*`, for an arrow-free group type. -/
  | pref (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
      HAtom (.arrow (.list (HTy.ofTy G)) (.list (HTy.ofTy G)))
  /-- The product `G* → G` of all the entries of a list, for an arrow-free group type.  This is
  the atomic function that replaces group prefix multiplication in Lemma `lem:fewer-atomic`. -/
  | mult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
      HAtom (.arrow (.list (HTy.ofTy G)) (HTy.ofTy G))
  /-- The atomic function `split` of Definition `def:polyregular-terms`,
  `A* → (A* × A*)*`. -/
  | splits (A : HTy) : HAtom (.arrow (.list A) (.list (.prod (.list A) (.list A))))
  /-- `map : (A → B) → A* → B*`. -/
  | map (A B : HTy) : HAtom (.arrow (.arrow A B) (.arrow (.list A) (.list B)))
  /-- `either : (A → C) → (B → C) → (A + B) → C`. -/
  | either (A B C : HTy) :
      HAtom (.arrow (.arrow A C) (.arrow (.arrow B C) (.arrow (.sum A B) C)))

/-- The semantics of an atomic function. -/
def HAtom.sem : {H : HTy} → HAtom H → H.Sem
  | _, .idA _ => fun x => x
  | _, .fst _ _ => fun x => x.1
  | _, .snd _ _ => fun x => x.2
  | _, .inl _ _ => fun x => Sum.inl x
  | _, .inr _ _ => fun x => Sum.inr x
  | _, .diag _ => fun x => (x, x)
  | _, .codiag _ => fun x => Sum.elim (fun a => a) (fun a => a) x
  | _, .distr _ _ _ => fun x =>
      Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2
  | _, .consA _ => fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x
  | _, .uncons _ => fun l => match l with
      | [] => Sum.inl ()
      | a :: l' => Sum.inr (a, l')
  | _, .reverse _ => fun l => l.reverse
  | _, .concat _ => fun l => l.flatten
  | _, .blockSplit _ _ => fun l => splitList l
  | _, .pref G grp _ => fun l => groupPrefixProd G grp l
  | _, .mult G grp _ => fun l => groupProd G grp l
  | _, .splits _ => fun l => splitsList l
  | _, .map _ _ => fun f l => l.map f
  | _, .either _ _ _ => fun f g x => Sum.elim f g x

/-- **The reduced set of atomic functions of Lemma `lem:fewer-atomic`**: the two projections, the
two co-projections, `uncons`, `concat`, `split`, `mult`, `map` and `either`. -/
def HAtom.Small : {H : HTy} → HAtom H → Prop
  | _, .fst _ _ => True
  | _, .snd _ _ => True
  | _, .inl _ _ => True
  | _, .inr _ _ => True
  | _, .uncons _ => True
  | _, .concat _ => True
  | _, .splits _ => True
  | _, .mult _ _ _ => True
  | _, .map _ _ => True
  | _, .either _ _ _ => True
  | _, _ => False

/-! ## The terms (Definition `def:higher-order-terms`) -/

/-- A variable: a position in the context, which fixes its type. -/
inductive HVar : List HTy → HTy → Type
  | zero {Γ : List HTy} {A : HTy} : HVar (A :: Γ) A
  | succ {Γ : List HTy} {A B : HTy} : HVar Γ A → HVar (B :: Γ) A

/-- A valuation of the variables of a context. -/
inductive HEnv : List HTy → Type
  | nil : HEnv []
  | cons {A : HTy} {Γ : List HTy} : A.Sem → HEnv Γ → HEnv (A :: Γ)

/-- The value of a variable in a valuation. -/
def HVar.lookup : {Γ : List HTy} → {A : HTy} → HVar Γ A → HEnv Γ → A.Sem
  | _, _, .zero, .cons x _ => x
  | _, _, .succ v, .cons _ e => v.lookup e

/-- **Definition `def:higher-order-terms` (Higher-order polyregular terms).**  The lambda calculus
over the atomic functions: variables, application, atomic functions, the unit term, pairs, list
terms and abstraction. -/
inductive HTerm : List HTy → HTy → Type
  /-- A variable. -/
  | var {Γ : List HTy} {A : HTy} (v : HVar Γ A) : HTerm Γ A
  /-- An atomic function. -/
  | atom {Γ : List HTy} {H : HTy} (a : HAtom H) : HTerm Γ H
  /-- Application. -/
  | app {Γ : List HTy} {A B : HTy} (f : HTerm Γ (.arrow A B)) (a : HTerm Γ A) : HTerm Γ B
  /-- Abstraction. -/
  | lam {Γ : List HTy} {A B : HTy} (b : HTerm (A :: Γ) B) : HTerm Γ (.arrow A B)
  /-- The unit term. -/
  | unit {Γ : List HTy} : HTerm Γ .one
  /-- A pair. -/
  | pair {Γ : List HTy} {A B : HTy} (a : HTerm Γ A) (b : HTerm Γ B) : HTerm Γ (.prod A B)
  /-- The empty list term. -/
  | nil {Γ : List HTy} {A : HTy} : HTerm Γ (.list A)
  /-- A list term, one entry at a time: the list terms `[a₁,…,aₙ]` of the book are the
  cons-chains. -/
  | cons {Γ : List HTy} {A : HTy} (a : HTerm Γ A) (l : HTerm Γ (.list A)) : HTerm Γ (.list A)

/-- The semantics of a term: a function from the valuations of its context to the set represented
by its type. -/
def HTerm.eval : {Γ : List HTy} → {H : HTy} → HTerm Γ H → HEnv Γ → H.Sem
  | _, _, .var v, e => v.lookup e
  | _, _, .atom a, _ => a.sem
  | _, _, .app f a, e => (f.eval e) (a.eval e)
  | _, _, .lam b, e => fun x => b.eval (.cons x e)
  | _, _, .unit, _ => ()
  | _, _, .pair a b, e => (a.eval e, b.eval e)
  | _, _, .nil, _ => []
  | _, _, .cons a l, e => a.eval e :: l.eval e

@[simp] lemma HTerm.eval_var {Γ : List HTy} {A : HTy} (v : HVar Γ A) (e : HEnv Γ) :
    (HTerm.var v).eval e = v.lookup e := rfl

@[simp] lemma HTerm.eval_atom {Γ : List HTy} {H : HTy} (a : HAtom H) (e : HEnv Γ) :
    (HTerm.atom (Γ := Γ) a).eval e = a.sem := rfl

@[simp] lemma HTerm.eval_app {Γ : List HTy} {A B : HTy} (f : HTerm Γ (.arrow A B))
    (a : HTerm Γ A) (e : HEnv Γ) : (f.app a).eval e = (f.eval e) (a.eval e) := rfl

@[simp] lemma HTerm.eval_lam {Γ : List HTy} {A B : HTy} (b : HTerm (A :: Γ) B) (e : HEnv Γ) :
    (HTerm.lam b).eval e = fun x => b.eval (.cons x e) := rfl

@[simp] lemma HTerm.eval_pair {Γ : List HTy} {A B : HTy} (a : HTerm Γ A) (b : HTerm Γ B)
    (e : HEnv Γ) : (a.pair b).eval e = (a.eval e, b.eval e) := rfl

@[simp] lemma HTerm.eval_nil {Γ : List HTy} {A : HTy} (e : HEnv Γ) :
    (HTerm.nil (Γ := Γ) (A := A)).eval e = [] := rfl

@[simp] lemma HTerm.eval_cons {Γ : List HTy} {A : HTy} (a : HTerm Γ A) (l : HTerm Γ (.list A))
    (e : HEnv Γ) : (a.cons l).eval e = a.eval e :: l.eval e := rfl

/-- A term uses only the reduced set of atomic functions of Lemma `lem:fewer-atomic`. -/
def HTerm.Small : {Γ : List HTy} → {H : HTy} → HTerm Γ H → Prop
  | _, _, .var _ => True
  | _, _, .atom a => a.Small
  | _, _, .app f a => f.Small ∧ a.Small
  | _, _, .lam b => b.Small
  | _, _, .unit => True
  | _, _, .pair a b => a.Small ∧ b.Small
  | _, _, .nil => True
  | _, _, .cons a l => a.Small ∧ l.Small

/-! ## The functions defined by higher-order terms -/

/-- A function between two types of Definition `def:types` is *defined by a higher-order term* if
some closed term of the corresponding arrow type has it as its semantics. -/
def IsHigherOrderTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ t : HTerm [] (.arrow (HTy.ofTy A) (HTy.ofTy B)),
    ∀ a : A.Elt, HTy.toElt B (t.eval .nil (HTy.ofElt A a)) = f a

/-- The same notion, for the terms that use only the reduced set of atomic functions of Lemma
`lem:fewer-atomic`. -/
def IsSmallHigherOrderTermFun {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ t : HTerm [] (.arrow (HTy.ofTy A) (HTy.ofTy B)),
    t.Small ∧ ∀ a : A.Elt, HTy.toElt B (t.eval .nil (HTy.ofElt A a)) = f a

end Transducers
