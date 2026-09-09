/-
Part D, Section *A functional programming language*: Lemma `lem:fewer-atomic`.

The expressive power of the higher-order polyregular terms does not change if the atomic functions
are restricted to the two projections, the two co-projections, `uncons`, `concat`, `split`, `mult`,
`map` and `either`: the terms below define the remaining eight atomic functions -- `id`, `diag`,
`codiag`, `distr`, `cons`, `reverse`, the block split of Example `ex:block`, and group prefix
multiplication -- and `Transducers.HTerm.toSmall` replaces every atomic function of a term by its
definition, without changing the semantics.

The first five terms are the ones displayed in the book.  The last three are the exercises that the
book refers to, and all three run over the cuts of the input list, using the new atomic function
`split` of Definition `def:polyregular-terms`:

* `reverse` keeps the first entry of the suffix of every cut, taken in the order in which `split`
  produces the cuts -- the prefix getting shorter -- which reverses the list (Example
  `ex:reverse-from-split`);
* the block split keeps, for every cut whose suffix begins with an entry `b` from `B`, the pair of
  `b` with the block of entries from `A` that follows it, and that block is itself computed by
  running over the cuts of the remaining list;
* group prefix multiplication takes the product of every non-empty prefix.

The identities that these computations satisfy are proved in `RequestProject/PartD/HOFewerAux.lean`.
-/
import RequestProject.PartD.HOFewerAux

namespace Transducers

namespace HTerm

/-! ## The five terms of the book -/

/-- `id = λx.x`. -/
def idTerm (Γ : List HTy) (A : HTy) : HTerm Γ (.arrow A A) := .lam (.var .zero)

/-- `diag = λx.(x,x)`. -/
def diagTerm (Γ : List HTy) (A : HTy) : HTerm Γ (.arrow A (.prod A A)) :=
  .lam (.pair (.var .zero) (.var .zero))

/-- `codiag = either (λx.x) (λx.x)`. -/
def codiagTerm (Γ : List HTy) (A : HTy) : HTerm Γ (.arrow (.sum A A) A) :=
  ((HTerm.atom (.either A A A)).app (.lam (.var .zero))).app (.lam (.var .zero))

/-- `distr = λx. either (λy. inl (fst x, y)) (λy. inr (fst x, y)) (snd x)`. -/
def distrTerm (Γ : List HTy) (A B C : HTy) :
    HTerm Γ (.arrow (.prod A (.sum B C)) (.sum (.prod A B) (.prod A C))) :=
  .lam
    ((((HTerm.atom (.either B C (.sum (.prod A B) (.prod A C)))).app
        (.lam ((HTerm.atom (.inl (.prod A B) (.prod A C))).app
          (.pair ((HTerm.atom (.fst A (.sum B C))).app (.var (.succ .zero))) (.var .zero))))).app
        (.lam ((HTerm.atom (.inr (.prod A B) (.prod A C))).app
          (.pair ((HTerm.atom (.fst A (.sum B C))).app (.var (.succ .zero)))
            (.var .zero))))).app
      ((HTerm.atom (.snd A (.sum B C))).app (.var .zero)))

/-- `cons = either (λy. []) (λy. [fst y] ++ snd y)`, written with the list term constructors. -/
def consTerm (Γ : List HTy) (A : HTy) :
    HTerm Γ (.arrow (.sum .one (.prod A (.list A))) (.list A)) :=
  ((HTerm.atom (.either .one (.prod A (.list A)) (.list A))).app (.lam .nil)).app
    (.lam (.cons ((HTerm.atom (.fst A (.list A))).app (.var .zero))
      ((HTerm.atom (.snd A (.list A))).app (.var .zero))))

/-! ## Reverse -/

/-- The first entry of a list, as a list of at most one entry. -/
def headAsListTerm (Γ : List HTy) (A : HTy) : HTerm Γ (.arrow (.list A) (.list A)) :=
  .lam
    ((((HTerm.atom (.either .one (.prod A (.list A)) (.list A))).app (.lam .nil)).app
        (.lam (.cons ((HTerm.atom (.fst A (.list A))).app (.var .zero)) .nil))).app
      ((HTerm.atom (.uncons A)).app (.var .zero)))

@[simp] lemma headAsListTerm_eval {Γ : List HTy} {A : HTy} (e : HEnv Γ) :
    (headAsListTerm Γ A).eval e = fun l => headAsList l := by
  funext l
  cases l <;> rfl

/-- **Example `ex:reverse-from-split`.**  `reverse = λl. concat (map (λz. headAsList (snd z))
(split l))`. -/
def reverseTerm (Γ : List HTy) (A : HTy) : HTerm Γ (.arrow (.list A) (.list A)) :=
  .lam
    ((HTerm.atom (.concat A)).app
      (((HTerm.atom (.map (.prod (.list A) (.list A)) (.list A))).app
          (.lam ((headAsListTerm _ A).app
            ((HTerm.atom (.snd (.list A) (.list A))).app (.var .zero))))).app
        ((HTerm.atom (.splits A)).app (.var .zero))))

@[simp] lemma reverseTerm_eval {Γ : List HTy} {A : HTy} (e : HEnv Γ) :
    (reverseTerm Γ A).eval e = fun l => l.reverse := by
  funext l
  simp only [reverseTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HAtom.sem,
    headAsListTerm_eval, HTerm.eval_var, HVar.lookup]
  exact flatten_headAsList_splits l

/-! ## The block split -/

section Block

variable (Γ : List HTy) (A B : HTy)

/-- The entries of a list over `A + B` that come from `B`. -/
def inrListTerm : HTerm Γ (.arrow (.list (.sum A B)) (.list B)) :=
  .lam
    ((HTerm.atom (.concat B)).app
      (((HTerm.atom (.map (.sum A B) (.list B))).app
          (.lam ((((HTerm.atom (.either A B (.list B))).app (.lam .nil)).app
            (.lam (.cons (.var .zero) .nil))).app (.var .zero)))).app (.var .zero)))

@[simp] lemma inrListTerm_eval {Γ : List HTy} {A B : HTy} (e : HEnv Γ) :
    (inrListTerm Γ A B).eval e = fun u => inrPart u := by
  funext u
  simp only [inrListTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HAtom.sem,
    HTerm.eval_var, HVar.lookup, HTerm.eval_nil, HTerm.eval_cons]
  rw [inrPart]
  congr 1
  refine List.map_congr_left (fun x _ => ?_)
  cases x <;> rfl

/-- The first entry of a list over `A + B`, if it comes from `A`. -/
def headInlTerm : HTerm Γ (.arrow (.list (.sum A B)) (.list A)) :=
  .lam
    ((((HTerm.atom (.either .one (.prod (.sum A B) (.list (.sum A B))) (.list A))).app
        (.lam .nil)).app
        (.lam
          ((((HTerm.atom (.either A B (.list A))).app
              (.lam (.cons (.var .zero) .nil))).app (.lam .nil)).app
            ((HTerm.atom (.fst (.sum A B) (.list (.sum A B)))).app (.var .zero))))).app
      ((HTerm.atom (.uncons (.sum A B))).app (.var .zero)))

@[simp] lemma headInlTerm_eval {Γ : List HTy} {A B : HTy} (e : HEnv Γ) :
    (headInlTerm Γ A B).eval e = fun v => headInl v := by
  funext v
  match v with
  | [] => rfl
  | Sum.inl a :: v => rfl
  | Sum.inr b :: v => rfl

/-- The longest prefix of entries from `A`. -/
def twiTerm : HTerm Γ (.arrow (.list (.sum A B)) (.list A)) :=
  .lam
    ((HTerm.atom (.concat A)).app
      (((HTerm.atom (.map (.prod (.list (.sum A B)) (.list (.sum A B))) (.list A))).app
          (.lam
            ((((HTerm.atom (.either .one (.prod B (.list B)) (.list A))).app
                (.lam ((headInlTerm _ A B).app
                  ((HTerm.atom (.snd (.list (.sum A B)) (.list (.sum A B)))).app
                    (.var (.succ .zero)))))).app (.lam .nil)).app
              ((HTerm.atom (.uncons B)).app
                ((inrListTerm _ A B).app
                  ((HTerm.atom (.fst (.list (.sum A B)) (.list (.sum A B)))).app
                    (.var .zero))))))).app
        ((reverseTerm _ _).app ((HTerm.atom (.splits (.sum A B))).app (.var .zero)))))

set_option maxHeartbeats 1000000 in
@[simp] lemma twiTerm_eval {Γ : List HTy} {A B : HTy} (e : HEnv Γ) :
    (twiTerm Γ A B).eval e = fun m => twiFun m := by
  funext m
  simp only [twiTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HAtom.sem,
    HTerm.eval_var, HVar.lookup, HTerm.eval_nil, reverseTerm_eval, inrListTerm_eval,
    headInlTerm_eval]
  rw [twiFun]
  congr 1
  refine List.map_congr_left (fun z _ => ?_)
  cases inrPart z.1 <;> simp

/-- The second component of the block split. -/
def bsTerm : HTerm Γ (.arrow (.list (.sum A B)) (.list (.prod B (.list A)))) :=
  .lam
    ((HTerm.atom (.concat (.prod B (.list A)))).app
      (((HTerm.atom (.map (.prod (.list (.sum A B)) (.list (.sum A B)))
            (.list (.prod B (.list A))))).app
          (.lam
            ((((HTerm.atom (.either .one (.prod (.sum A B) (.list (.sum A B)))
                  (.list (.prod B (.list A))))).app (.lam .nil)).app
                (.lam
                  ((((HTerm.atom (.either A B (.list (.prod B (.list A))))).app
                      (.lam .nil)).app
                      (.lam (.cons (.pair (.var .zero)
                        ((twiTerm _ A B).app
                          ((HTerm.atom (.snd (.sum A B) (.list (.sum A B)))).app
                            (.var (.succ .zero))))) .nil))).app
                    ((HTerm.atom (.fst (.sum A B) (.list (.sum A B)))).app (.var .zero))))).app
              ((HTerm.atom (.uncons (.sum A B))).app
                ((HTerm.atom (.snd (.list (.sum A B)) (.list (.sum A B)))).app
                  (.var .zero)))))).app
        ((reverseTerm _ _).app ((HTerm.atom (.splits (.sum A B))).app (.var .zero)))))

set_option maxHeartbeats 1000000 in
@[simp] lemma bsTerm_eval {Γ : List HTy} {A B : HTy} (e : HEnv Γ) :
    (bsTerm Γ A B).eval e = fun l => bsFun l := by
  funext l
  simp only [bsTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HAtom.sem,
    HTerm.eval_var, HVar.lookup, HTerm.eval_nil, HTerm.eval_cons, HTerm.eval_pair,
    reverseTerm_eval, twiTerm_eval]
  rw [bsFun]
  congr 1
  refine List.map_congr_left (fun z _ => ?_)
  cases z.2 with
  | nil => simp
  | cons x rest => cases x <;> simp

/-- **The block split of Example `ex:block`**, which the book removes from the atomic functions in
an exercise; that exercise carries a label the sources of this copy of the book do not define, so
it is referred to here by what it says. -/
def blockSplitTerm :
    HTerm Γ (.arrow (.list (.sum A B)) (.prod (.list A) (.list (.prod B (.list A))))) :=
  .lam (.pair ((twiTerm _ A B).app (.var .zero)) ((bsTerm _ A B).app (.var .zero)))

@[simp] lemma blockSplitTerm_eval {Γ : List HTy} {A B : HTy} (e : HEnv Γ) :
    (blockSplitTerm Γ A B).eval e = fun l => splitList l := by
  funext l
  simp only [blockSplitTerm, HTerm.eval_lam, HTerm.eval_pair, HTerm.eval_app, HTerm.eval_var,
    HVar.lookup, twiTerm_eval, bsTerm_eval]
  rw [twiFun_eq, bsFun_eq]
  rfl

end Block

/-! ## Group prefix multiplication -/

section Pref

variable (Γ : List HTy) (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt)

/-- **Group prefix multiplication, from the product of a list**: the prefix products are the
products of the non-empty prefixes.  This is the exercise the book refers to when it replaces
group prefix multiplication by `mult`; that exercise carries a label the sources of this copy of
the book do not define. -/
def prefTerm : HTerm Γ (.arrow (.list (HTy.ofTy G)) (.list (HTy.ofTy G))) :=
  .lam
    ((HTerm.atom (.concat (HTy.ofTy G))).app
      (((HTerm.atom (.map (.prod (.list (HTy.ofTy G)) (.list (HTy.ofTy G)))
            (.list (HTy.ofTy G)))).app
          (.lam
            ((((HTerm.atom (.either .one (.prod (HTy.ofTy G) (.list (HTy.ofTy G)))
                  (.list (HTy.ofTy G)))).app (.lam .nil)).app
                (.lam (.cons ((HTerm.atom (.mult G grp hfin)).app
                  ((HTerm.atom (.fst (.list (HTy.ofTy G)) (.list (HTy.ofTy G)))).app
                    (.var (.succ .zero)))) .nil))).app
              ((HTerm.atom (.uncons (HTy.ofTy G))).app
                ((HTerm.atom (.fst (.list (HTy.ofTy G)) (.list (HTy.ofTy G)))).app
                  (.var .zero)))))).app
        ((reverseTerm _ _).app ((HTerm.atom (.splits (HTy.ofTy G))).app (.var .zero)))))

set_option maxHeartbeats 1000000 in
lemma prefTerm_eval {Γ : List HTy} {G : Ty} {grp : Group G.Elt} {hfin : Finite G.Elt}
    (e : HEnv Γ) :
    (prefTerm Γ G grp hfin).eval e = fun l => groupPrefixProd G grp l := by
  letI := grp
  funext l
  simp only [prefTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HAtom.sem,
    HTerm.eval_var, HVar.lookup, HTerm.eval_nil, HTerm.eval_cons, reverseTerm_eval]
  -- every cut contributes the product of its prefix, computed in the group itself
  refine Eq.trans (congrArg List.flatten (List.map_congr_left
    (g := fun z => (prefStep (z.1.map (HTy.toElt G))).map (HTy.ofElt G)) ?_)) ?_
  · intro z _
    cases hz : z.1 with
    | nil => simp [hz]
    | cons x rest => simp [hz, groupProd]
  · exact groupPrefixProd_eq l

end Pref

/-! ## Lemma `lem:fewer-atomic` -/

/-- The definition of an atomic function by a term that uses only the reduced set of atomic
functions. -/
def _root_.Transducers.HAtom.smallImpl : {H : HTy} → HAtom H → (Γ : List HTy) → HTerm Γ H
  | _, .idA A, Γ => idTerm Γ A
  | _, .diag A, Γ => diagTerm Γ A
  | _, .codiag A, Γ => codiagTerm Γ A
  | _, .distr A B C, Γ => distrTerm Γ A B C
  | _, .consA A, Γ => consTerm Γ A
  | _, .reverse A, Γ => reverseTerm Γ A
  | _, .blockSplit A B, Γ => blockSplitTerm Γ A B
  | _, .pref G grp hfin, Γ => prefTerm Γ G grp hfin
  | _, a, Γ => HTerm.atom (Γ := Γ) a

theorem _root_.Transducers.HAtom.smallImpl_small :
    ∀ {H : HTy} (a : HAtom H) (Γ : List HTy), (a.smallImpl Γ).Small := by
  intro H a Γ
  cases a <;> repeat' constructor

theorem _root_.Transducers.HAtom.smallImpl_eval :
    ∀ {H : HTy} (a : HAtom H) {Γ : List HTy} (e : HEnv Γ), (a.smallImpl Γ).eval e = a.sem := by
  intro H a Γ e
  cases a with
  | idA A => rfl
  | diag A => rfl
  | codiag A => funext x; cases x <;> rfl
  | distr A B C => funext x; obtain ⟨u, v⟩ := x; cases v <;> rfl
  | consA A => funext x; cases x <;> rfl
  | reverse A => exact reverseTerm_eval e
  | blockSplit A B => exact blockSplitTerm_eval e
  | pref G grp hfin => exact prefTerm_eval e
  | fst A B => rfl
  | snd A B => rfl
  | inl A B => rfl
  | inr A B => rfl
  | uncons A => rfl
  | concat A => rfl
  | splits A => rfl
  | mult G grp hfin => rfl
  | map A B => rfl
  | either A B C => rfl

/-- Every atomic function of a term is replaced by its definition in the reduced set. -/
def toSmall : {Γ : List HTy} → {H : HTy} → HTerm Γ H → HTerm Γ H
  | _, _, .var v => .var v
  | Γ, _, .atom a => a.smallImpl Γ
  | _, _, .app f a => .app f.toSmall a.toSmall
  | _, _, .lam b => .lam b.toSmall
  | _, _, .unit => .unit
  | _, _, .pair a b => .pair a.toSmall b.toSmall
  | _, _, .nil => .nil
  | _, _, .cons a l => .cons a.toSmall l.toSmall

theorem toSmall_small : ∀ {Γ : List HTy} {H : HTy} (t : HTerm Γ H), t.toSmall.Small
  | _, _, .var _ => trivial
  | Γ, _, .atom a => a.smallImpl_small Γ
  | _, _, .app f a => ⟨toSmall_small f, toSmall_small a⟩
  | _, _, .lam b => toSmall_small b
  | _, _, .unit => trivial
  | _, _, .pair a b => ⟨toSmall_small a, toSmall_small b⟩
  | _, _, .nil => trivial
  | _, _, .cons a l => ⟨toSmall_small a, toSmall_small l⟩

theorem toSmall_eval : ∀ {Γ : List HTy} {H : HTy} (t : HTerm Γ H) (e : HEnv Γ),
    t.toSmall.eval e = t.eval e
  | _, _, .var _, _ => rfl
  | _, _, .atom a, e => a.smallImpl_eval e
  | _, _, .app f a, e => by
      show (f.toSmall.eval e) (a.toSmall.eval e) = (f.eval e) (a.eval e)
      rw [toSmall_eval f e, toSmall_eval a e]
  | _, _, .lam b, e => by
      funext x
      exact toSmall_eval b (.cons x e)
  | _, _, .unit, _ => rfl
  | _, _, .pair a b, e => by
      show (a.toSmall.eval e, b.toSmall.eval e) = (a.eval e, b.eval e)
      rw [toSmall_eval a e, toSmall_eval b e]
  | _, _, .nil, _ => rfl
  | _, _, .cons a l, e => by
      show a.toSmall.eval e :: l.toSmall.eval e = a.eval e :: l.eval e
      rw [toSmall_eval a e, toSmall_eval l e]

end HTerm

/-- **Lemma `lem:fewer-atomic`.**  The expressive power of the higher-order polyregular terms does
not change if the set of atomic functions is restricted to the co-projections, the two projections,
`uncons`, `concat`, `split`, `mult`, `map` and `either`: every term has the same semantics as a
term that uses only those. -/
theorem exists_small_higherOrderTerm {Γ : List HTy} {H : HTy} (t : HTerm Γ H) :
    ∃ t' : HTerm Γ H, t'.Small ∧ ∀ e : HEnv Γ, t'.eval e = t.eval e :=
  ⟨t.toSmall, HTerm.toSmall_small t, HTerm.toSmall_eval t⟩

/-- **Lemma `lem:fewer-atomic`, for the functions between arrow-free types that the terms
define.** -/
theorem isSmallHigherOrderTermFun_of_isHigherOrderTermFun {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsHigherOrderTermFun f) : IsSmallHigherOrderTermFun f := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t.toSmall, HTerm.toSmall_small t, fun a => by rw [HTerm.toSmall_eval t]; exact ht a⟩

end Transducers
