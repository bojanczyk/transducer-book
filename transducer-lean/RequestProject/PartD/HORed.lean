/-
Part D, Section *A functional programming language*: substitution and the reduction rules.

Section *Expressive completeness* of the book evaluates higher-order polyregular terms by
reduction: the β-rule

    (λ x. a) b  ⇝  a[x ↦ b]

together with the rules of Figure `fig:reduction-rules` for the atomic functions, all of them
applicable to subterms.  This file renders that notion of one-step reduction as
`Transducers.HStep`, for the reduced set of atomic functions of Lemma `lem:fewer-atomic` (the book
fixes that set for the whole of Section *Expressive completeness*), and proves the book's
observation that a reduction step changes neither the type nor the semantics of a term
(`Transducers.HStep.eval_eq`; the type is preserved by construction, since `HStep` relates two
terms of the same type in the same context).

Everything before the reduction rules is the substitution machinery that the β-rule needs.  The
terms of `RequestProject/PartD/HOSyntax.lean` are intrinsically typed and use De Bruijn indices, so
substitution is the usual pair of recursions: a renaming acts on terms (`Transducers.HTerm.rename`)
and is used to weaken a substitution under a binder, and a substitution acts on terms
(`Transducers.HTerm.subst`).  `Transducers.HTerm.subst1` substitutes for the variable bound by the
outermost `λ`, which is what the β-rule uses.

Two conventions in rendering Figure `fig:reduction-rules`.

* **List terms.**  The book's list term `[a₁,…,aₙ]` is a cons-chain here, and
  `Transducers.HTerm.mkList` builds it from a Lean list of terms.  A rule whose premise is that an
  argument *is* a list term -- those for `concat`, `split`, `map` -- is stated for an argument of
  the form `mkList l`.  The rules for `uncons`, on the other hand, only look at the head
  constructor of the argument, which is what the book's `uncons []` and `uncons [a₁,…,aₙ]` say.

* **Group values.**  The rule for `mult` requires its arguments to be *group values*, terms built
  from the term constructors for the unit, products and co-products, which the book notes are in
  bijection with the elements of the group.  `Transducers.HTerm.ofValue` is that bijection: it
  builds, for an arrow-free type, the term that represents an element of the set it denotes.  So
  the rule reads: `mult` applied to the list term of the representations of `g₁,…,gₙ` reduces to
  the representation of their product.
-/
import RequestProject.PartD.HOBound

namespace Transducers

namespace HTerm

/-! ## Renaming -/

/-- A renaming of the variables of a context `Γ` by variables of a context `Δ`. -/
def Ren (Γ Δ : List HTy) : Type := (A : HTy) → HVar Γ A → HVar Δ A

/-- The identity renaming. -/
def Ren.id (Γ : List HTy) : Ren Γ Γ := fun _ v => v

/-- Weakening: the renaming that shifts every variable past one new binder. -/
def Ren.wk (Γ : List HTy) (A : HTy) : Ren Γ (A :: Γ) := fun _ v => v.succ

/-- A renaming acts under a binder. -/
def Ren.lift {Γ Δ : List HTy} (A : HTy) (r : Ren Γ Δ) : Ren (A :: Γ) (A :: Δ) :=
  fun _ v =>
    match v with
    | .zero => .zero
    | .succ w => .succ (r _ w)

/-- The action of a renaming on a term. -/
def rename : {Γ : List HTy} → {H : HTy} → HTerm Γ H → {Δ : List HTy} → Ren Γ Δ → HTerm Δ H
  | _, _, .var v, _, r => .var (r _ v)
  | _, _, .atom a, _, _ => .atom a
  | _, _, .app f a, _, r => .app (f.rename r) (a.rename r)
  | _, _, .lam b, _, r => .lam (b.rename (Ren.lift _ r))
  | _, _, .unit, _, _ => .unit
  | _, _, .pair a b, _, r => .pair (a.rename r) (b.rename r)
  | _, _, .nil, _, _ => .nil
  | _, _, .cons a l, _, r => .cons (a.rename r) (l.rename r)

/-! ## Substitution -/

/-- A substitution: a term of the context `Δ` for every variable of the context `Γ`. -/
def Sub (Γ Δ : List HTy) : Type := (A : HTy) → HVar Γ A → HTerm Δ A

/-- A substitution acts under a binder. -/
def Sub.lift {Γ Δ : List HTy} (A : HTy) (s : Sub Γ Δ) : Sub (A :: Γ) (A :: Δ) :=
  fun _ v =>
    match v with
    | .zero => .var .zero
    | .succ w => (s _ w).rename (Ren.wk Δ A)

/-- The action of a substitution on a term. -/
def subst : {Γ : List HTy} → {H : HTy} → HTerm Γ H → {Δ : List HTy} → Sub Γ Δ → HTerm Δ H
  | _, _, .var v, _, s => s _ v
  | _, _, .atom a, _, _ => .atom a
  | _, _, .app f a, _, s => .app (f.subst s) (a.subst s)
  | _, _, .lam b, _, s => .lam (b.subst (Sub.lift _ s))
  | _, _, .unit, _, _ => .unit
  | _, _, .pair a b, _, s => .pair (a.subst s) (b.subst s)
  | _, _, .nil, _, _ => .nil
  | _, _, .cons a l, _, s => .cons (a.subst s) (l.subst s)

/-- The substitution that replaces the variable bound by the outermost `λ` by a term, and leaves
the other variables alone. -/
def Sub.single {Γ : List HTy} {A : HTy} (u : HTerm Γ A) : Sub (A :: Γ) Γ :=
  fun _ v =>
    match v with
    | .zero => u
    | .succ w => .var w

/-- `b[x ↦ u]`, where `x` is the variable bound by the outermost `λ`. -/
def subst1 {Γ : List HTy} {A B : HTy} (b : HTerm (A :: Γ) B) (u : HTerm Γ A) : HTerm Γ B :=
  b.subst (Sub.single u)

/-! ## Valuations as functions -/

end HTerm

/-- A valuation built from a function on variables. -/
def HEnv.ofFun : (Γ : List HTy) → ((A : HTy) → HVar Γ A → A.Sem) → HEnv Γ
  | [], _ => .nil
  | _ :: Γ, f => .cons (f _ .zero) (HEnv.ofFun Γ (fun B v => f B v.succ))

@[simp] lemma HEnv.lookup_ofFun : {Γ : List HTy} → {A : HTy} → (v : HVar Γ A) →
    (f : (A : HTy) → HVar Γ A → A.Sem) → v.lookup (HEnv.ofFun Γ f) = f A v
  | _, _, .zero, _ => rfl
  | _, _, .succ w, f => HEnv.lookup_ofFun w (fun B v => f B v.succ)

/-- Two valuations that agree on every variable are equal. -/
lemma HEnv.ext : {Γ : List HTy} → {e e' : HEnv Γ} →
    (∀ (A : HTy) (v : HVar Γ A), v.lookup e = v.lookup e') → e = e'
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x e, .cons y e', h => by
      have hx : x = y := h _ .zero
      have he : e = e' := HEnv.ext (fun A v => h A v.succ)
      rw [hx, he]

namespace HTerm

/-- The valuation obtained by reading a valuation through a renaming. -/
def renEnv {Γ Δ : List HTy} (r : Ren Γ Δ) (e : HEnv Δ) : HEnv Γ :=
  HEnv.ofFun Γ (fun A v => (r A v).lookup e)

@[simp] lemma lookup_renEnv {Γ Δ : List HTy} {A : HTy} (r : Ren Γ Δ) (e : HEnv Δ)
    (v : HVar Γ A) : v.lookup (renEnv r e) = (r A v).lookup e :=
  HEnv.lookup_ofFun v _

lemma renEnv_lift {Γ Δ : List HTy} (A : HTy) (r : Ren Γ Δ) (x : A.Sem) (e : HEnv Δ) :
    renEnv (Ren.lift A r) (.cons x e) = .cons x (renEnv r e) := by
  refine HEnv.ext (fun B v => ?_)
  cases v with
  | zero => simp [Ren.lift, HVar.lookup]
  | succ w => simp [Ren.lift, HVar.lookup]

lemma eval_rename : {Γ : List HTy} → {H : HTy} → (t : HTerm Γ H) → {Δ : List HTy} →
    (r : Ren Γ Δ) → (e : HEnv Δ) → (t.rename r).eval e = t.eval (renEnv r e)
  | _, _, .var v, _, r, e => by simp [rename]
  | _, _, .atom a, _, _, _ => rfl
  | _, _, .app f a, _, r, e => by
      simp [rename, eval_rename f r e, eval_rename a r e]
  | _, _, .lam b, _, r, e => by
      funext x
      simp only [rename, eval]
      rw [eval_rename b (Ren.lift _ r) (.cons x e), renEnv_lift]
  | _, _, .unit, _, _, _ => rfl
  | _, _, .pair a b, _, r, e => by
      simp [rename, eval_rename a r e, eval_rename b r e]
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons a l, _, r, e => by
      simp [rename, eval_rename a r e, eval_rename l r e]

/-- The valuation obtained by reading a valuation through a substitution. -/
def subEnv {Γ Δ : List HTy} (s : Sub Γ Δ) (e : HEnv Δ) : HEnv Γ :=
  HEnv.ofFun Γ (fun A v => (s A v).eval e)

@[simp] lemma lookup_subEnv {Γ Δ : List HTy} {A : HTy} (s : Sub Γ Δ) (e : HEnv Δ)
    (v : HVar Γ A) : v.lookup (subEnv s e) = (s A v).eval e :=
  HEnv.lookup_ofFun v _

lemma renEnv_wk {Γ : List HTy} (A : HTy) (x : A.Sem) (e : HEnv Γ) :
    renEnv (Ren.wk Γ A) (.cons x e) = e :=
  HEnv.ext (fun _ v => by simp [Ren.wk, HVar.lookup])

lemma subEnv_lift {Γ Δ : List HTy} (A : HTy) (s : Sub Γ Δ) (x : A.Sem) (e : HEnv Δ) :
    subEnv (Sub.lift A s) (.cons x e) = .cons x (subEnv s e) := by
  refine HEnv.ext (fun B v => ?_)
  cases v with
  | zero => simp [Sub.lift, HVar.lookup]
  | succ w => simp [Sub.lift, HVar.lookup, eval_rename, renEnv_wk]

lemma eval_subst : {Γ : List HTy} → {H : HTy} → (t : HTerm Γ H) → {Δ : List HTy} →
    (s : Sub Γ Δ) → (e : HEnv Δ) → (t.subst s).eval e = t.eval (subEnv s e)
  | _, _, .var v, _, s, e => by simp [subst]
  | _, _, .atom a, _, _, _ => rfl
  | _, _, .app f a, _, s, e => by
      simp [subst, eval_subst f s e, eval_subst a s e]
  | _, _, .lam b, _, s, e => by
      funext x
      simp only [subst, eval]
      rw [eval_subst b (Sub.lift _ s) (.cons x e), subEnv_lift]
  | _, _, .unit, _, _, _ => rfl
  | _, _, .pair a b, _, s, e => by
      simp [subst, eval_subst a s e, eval_subst b s e]
  | _, _, .nil, _, _, _ => rfl
  | _, _, .cons a l, _, s, e => by
      simp [subst, eval_subst a s e, eval_subst l s e]

lemma subEnv_single {Γ : List HTy} {A : HTy} (u : HTerm Γ A) (e : HEnv Γ) :
    subEnv (Sub.single u) e = .cons (u.eval e) e :=
  HEnv.ext (fun B v => by cases v with
    | zero => simp [Sub.single, HVar.lookup]
    | succ w => simp [Sub.single, HVar.lookup])

/-- The semantics of `b[x ↦ u]`: the semantics of `b` in the valuation extended by the value
of `u`. -/
lemma eval_subst1 {Γ : List HTy} {A B : HTy} (b : HTerm (A :: Γ) B) (u : HTerm Γ A)
    (e : HEnv Γ) : (b.subst1 u).eval e = b.eval (.cons (u.eval e) e) := by
  rw [subst1, eval_subst, subEnv_single]

/-! ## List terms and value terms -/

/-- The book's list term `[a₁,…,aₙ]`, as a cons-chain. -/
def mkList {Γ : List HTy} {A : HTy} : List (HTerm Γ A) → HTerm Γ (.list A)
  | [] => .nil
  | a :: l => .cons a (mkList l)

@[simp] lemma eval_mkList {Γ : List HTy} {A : HTy} (l : List (HTerm Γ A)) (e : HEnv Γ) :
    (mkList l).eval e = l.map (fun a => a.eval e) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [mkList, ih]

/-- The term that represents an element of an arrow-free type: the *values* of the book, built
from the term constructors for the unit, products, co-products and lists. -/
def ofValue {Γ : List HTy} : (A : Ty) → (HTy.ofTy A).Sem → HTerm Γ (HTy.ofTy A)
  | .one, _ => .unit
  | .prod A B, x => .pair (ofValue A x.1) (ofValue B x.2)
  | .sum A B, x =>
      match x with
      | .inl a => .app (.atom (.inl (HTy.ofTy A) (HTy.ofTy B))) (ofValue A a)
      | .inr b => .app (.atom (.inr (HTy.ofTy A) (HTy.ofTy B))) (ofValue B b)
  | .list A, l => mkList (l.map (ofValue A))

@[simp] lemma eval_ofValue {Γ : List HTy} : (A : Ty) → (x : (HTy.ofTy A).Sem) → (e : HEnv Γ) →
    (ofValue A x).eval e = x
  | .one, _, _ => rfl
  | .prod A B, x, e => by
      show ((ofValue A x.1).eval e, (ofValue B x.2).eval e) = x
      rw [eval_ofValue A x.1 e, eval_ofValue B x.2 e]
      rfl
  | .sum A B, x, e => by
      cases x with
      | inl a => show Sum.inl ((ofValue A a).eval e) = _; rw [eval_ofValue A a e]
      | inr b => show Sum.inr ((ofValue B b).eval e) = _; rw [eval_ofValue B b e]
  | .list A, l, e => by
      have h : ∀ x, (ofValue (Γ := Γ) A x).eval e = x := fun x => eval_ofValue A x e
      simp only [ofValue, eval_mkList, List.map_map, Function.comp_def, h]
      exact List.map_id l

/-! ## The size of a term -/

/-- The number of nodes of the syntax tree of a term, counting a cons-chain node by node.  This
is used only as an induction measure; the *height* of `def:resource-bound` is
`Transducers.HTerm.height`. -/
def size : {Γ : List HTy} → {H : HTy} → HTerm Γ H → ℕ
  | _, _, .var _ => 1
  | _, _, .atom _ => 1
  | _, _, .app f a => 1 + f.size + a.size
  | _, _, .lam b => 1 + b.size
  | _, _, .unit => 1
  | _, _, .pair a b => 1 + a.size + b.size
  | _, _, .nil => 1
  | _, _, .cons a l => 1 + a.size + l.size

end HTerm

/-! ## One-step reduction -/

/-- **The reduction rules of Section *Expressive completeness***: the β-rule, the rules of Figure
`fig:reduction-rules` for the reduced set of atomic functions of Lemma `lem:fewer-atomic`, and the
congruence rules that let a rule be applied to a subterm. -/
inductive HStep : {Γ : List HTy} → {H : HTy} → HTerm Γ H → HTerm Γ H → Prop
  /-- `(λ x. b) u ⇝ b[x ↦ u]`. -/
  | beta {Γ : List HTy} {A B : HTy} (b : HTerm (A :: Γ) B) (u : HTerm Γ A) :
      HStep (.app (.lam b) u) (b.subst1 u)
  /-- `fst (a,b) ⇝ a`. -/
  | fst {Γ : List HTy} {A B : HTy} (a : HTerm Γ A) (b : HTerm Γ B) :
      HStep (.app (.atom (.fst A B)) (.pair a b)) a
  /-- `snd (a,b) ⇝ b`. -/
  | snd {Γ : List HTy} {A B : HTy} (a : HTerm Γ A) (b : HTerm Γ B) :
      HStep (.app (.atom (.snd A B)) (.pair a b)) b
  /-- `uncons [] ⇝ left 1`. -/
  | unconsNil {Γ : List HTy} {A : HTy} :
      HStep (.app (.atom (.uncons A)) (.nil (Γ := Γ)))
        (.app (.atom (.inl .one (.prod A (.list A)))) .unit)
  /-- `uncons (a :: l) ⇝ right (a, l)`. -/
  | unconsCons {Γ : List HTy} {A : HTy} (a : HTerm Γ A) (l : HTerm Γ (.list A)) :
      HStep (.app (.atom (.uncons A)) (.cons a l))
        (.app (.atom (.inr .one (.prod A (.list A)))) (.pair a l))
  /-- `concat [ℓ₁,…,ℓₙ] ⇝ ℓ₁ ⋯ ℓₙ`, where each `ℓᵢ` is a list term. -/
  | concat {Γ : List HTy} {A : HTy} (L : List (List (HTerm Γ A))) :
      HStep (.app (.atom (.concat A)) (HTerm.mkList (L.map HTerm.mkList)))
        (HTerm.mkList L.flatten)
  /-- `split [a₁,…,aₙ] ⇝ [([a₁,…,aₙ],[]),…,([],[a₁,…,aₙ])]`. -/
  | splits {Γ : List HTy} {A : HTy} (l : List (HTerm Γ A)) :
      HStep (.app (.atom (.splits A)) (HTerm.mkList l))
        (HTerm.mkList ((splitsList l).map
          (fun p => .pair (HTerm.mkList p.1) (HTerm.mkList p.2))))
  /-- `mult [g₁,…,gₙ] ⇝ g`, where the `gᵢ` are group values and `g` is their product. -/
  | mult {Γ : List HTy} (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt)
      (l : List (HTy.ofTy G).Sem) :
      HStep (.app (.atom (.mult G grp hfin)) (HTerm.mkList (l.map (HTerm.ofValue (Γ := Γ) G))))
        (HTerm.ofValue G (groupProd G grp l))
  /-- `map f [a₁,…,aₙ] ⇝ [f a₁,…,f aₙ]`. -/
  | map {Γ : List HTy} {A B : HTy} (f : HTerm Γ (.arrow A B)) (l : List (HTerm Γ A)) :
      HStep (.app (.app (.atom (.map A B)) f) (HTerm.mkList l))
        (HTerm.mkList (l.map (fun a => .app f a)))
  /-- `either f g (left a) ⇝ f a`. -/
  | eitherInl {Γ : List HTy} {A B C : HTy} (f : HTerm Γ (.arrow A C)) (g : HTerm Γ (.arrow B C))
      (a : HTerm Γ A) :
      HStep (.app (.app (.app (.atom (.either A B C)) f) g) (.app (.atom (.inl A B)) a))
        (.app f a)
  /-- `either f g (right b) ⇝ g b`. -/
  | eitherInr {Γ : List HTy} {A B C : HTy} (f : HTerm Γ (.arrow A C)) (g : HTerm Γ (.arrow B C))
      (b : HTerm Γ B) :
      HStep (.app (.app (.app (.atom (.either A B C)) f) g) (.app (.atom (.inr A B)) b))
        (.app g b)
  /-- A rule applied in the function part of an application. -/
  | appL {Γ : List HTy} {A B : HTy} {f f' : HTerm Γ (.arrow A B)} (a : HTerm Γ A) :
      HStep f f' → HStep (.app f a) (.app f' a)
  /-- A rule applied in the argument of an application. -/
  | appR {Γ : List HTy} {A B : HTy} (f : HTerm Γ (.arrow A B)) {a a' : HTerm Γ A} :
      HStep a a' → HStep (.app f a) (.app f a')
  /-- A rule applied in the body of an abstraction. -/
  | lam {Γ : List HTy} {A B : HTy} {b b' : HTerm (A :: Γ) B} :
      HStep b b' → HStep (HTerm.lam b) (HTerm.lam b')
  /-- A rule applied in the first component of a pair. -/
  | pairL {Γ : List HTy} {A B : HTy} {a a' : HTerm Γ A} (b : HTerm Γ B) :
      HStep a a' → HStep (.pair a b) (.pair a' b)
  /-- A rule applied in the second component of a pair. -/
  | pairR {Γ : List HTy} {A B : HTy} (a : HTerm Γ A) {b b' : HTerm Γ B} :
      HStep b b' → HStep (.pair a b) (.pair a b')
  /-- A rule applied in an entry of a list term. -/
  | consL {Γ : List HTy} {A : HTy} {a a' : HTerm Γ A} (l : HTerm Γ (.list A)) :
      HStep a a' → HStep (.cons a l) (.cons a' l)
  /-- A rule applied in the tail of a list term. -/
  | consR {Γ : List HTy} {A : HTy} (a : HTerm Γ A) {l l' : HTerm Γ (.list A)} :
      HStep l l' → HStep (.cons a l) (.cons a l')

/-- A term is in *normal form* if no reduction rule applies to it. -/
def HTerm.Normal {Γ : List HTy} {H : HTy} (t : HTerm Γ H) : Prop :=
  ∀ t' : HTerm Γ H, ¬ HStep t t'

/-- **A reduction step does not change the semantics of a term.**  (It does not change its type
either, which is true by construction: `HStep` relates two terms of the same type.) -/
theorem HStep.eval_eq : {Γ : List HTy} → {H : HTy} → {t t' : HTerm Γ H} → HStep t t' →
    ∀ e : HEnv Γ, t.eval e = t'.eval e := by
  intro Γ H t t' h
  induction h with
  | beta b u => intro e; simp [HTerm.eval_subst1]
  | fst a b => intro e; rfl
  | snd a b => intro e; rfl
  | unconsNil => intro e; rfl
  | unconsCons a l => intro e; rfl
  | concat L =>
      intro e
      simp [HAtom.sem, List.map_map, Function.comp_def, List.map_flatten]
  | splits l =>
      intro e
      simp [HAtom.sem, splitsList_map, List.map_map, Function.comp_def]
  | mult G grp hfin l =>
      intro e
      simp [HAtom.sem, List.map_map, Function.comp_def]
  | map f l =>
      intro e
      simp [HAtom.sem, List.map_map, Function.comp_def]
  | eitherInl f g a => intro e; rfl
  | eitherInr f g b => intro e; rfl
  | appL a _ ih => intro e; simp [HTerm.eval, ih e]
  | appR f _ ih => intro e; simp [HTerm.eval, ih e]
  | lam _ ih => intro e; funext x; exact ih (.cons x e)
  | pairL b _ ih => intro e; simp [HTerm.eval, ih e]
  | pairR a _ ih => intro e; simp [HTerm.eval, ih e]
  | consL l _ ih => intro e; simp [HTerm.eval, ih e]
  | consR a _ ih => intro e; simp [HTerm.eval, ih e]

end Transducers
