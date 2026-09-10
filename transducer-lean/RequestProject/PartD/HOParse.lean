/-
Part D, Section *A functional programming language*: Lemma
`claim:parsing-is-regular-with-resource-bounds`.

For a resource bound `(𝒜,h)` of Definition `def:resource-bound`, the set of strings that represent
a closed term consistent with the bound is a regular language.  The book's proof is a
"straightforward induction on the height", and that is what is done here: the language of the
representations of the terms of height at most `n+1` is built from the languages of the
representations of the terms of height at most `n` by finitely many unions, concatenations and one
Kleene star, and the regular languages are closed under those operations
(`RequestProject/Common/RegLangClosure.lean`).

Two points deserve a comment.

* The induction is on the height alone, and it is uniform in the context: the statement proved is
  that `Transducers.termLang 𝒜 Γ n A` -- the representations of the terms of type `A`, in the
  context `Γ`, of height at most `n`, with all types in `𝒜` -- is regular *for every* context `Γ`
  and every type `A`.  There is no need to know that only finitely many contexts arise, because at
  each step only finitely many languages of the previous level are used.

* The one place where a Kleene star is needed is the list terms.  A cons-chain
  `cons a₁ (⋯ (cons aₚ t))` has the height of the book's list term `[a₁,…,aₚ]`, one more than the
  heights of the entries, so the tail of a chain does *not* have smaller height and the recursion
  cannot go through it.  The chain is therefore read as a star: an arbitrary number of entries of
  height at most `n`, each preceded by the letter `⟨cons⟩`, followed by a term that is not a `cons`
  (`Transducers.headLang`), whose immediate subterms do have height at most `n`.
-/
import RequestProject.Common.RegLangClosure
import RequestProject.PartD.HOStr

namespace Transducers

open Language Computability

/-! ## The languages of the induction -/

/-- The representations of the terms of type `A`, in the context `Γ`, whose height is at most `n`
and all of whose types belong to `S`. -/
def termLang (S : Finset HTy) (Γ : List HTy) (n : ℕ) (A : HTy) : Language HSym :=
  {w | ∃ t : HTerm Γ A, t.height ≤ n ∧ t.types ⊆ S ∧ t.repr = w}

/-- One entry of a cons-chain: the letter `⟨cons⟩` followed by the representation of an entry.
This is the empty language unless the type is a list type. -/
def consEntry (S : Finset HTy) (Γ : List HTy) (n : ℕ) : (A : HTy) → Language HSym
  | .list X => {w | ∃ u ∈ termLang S Γ n X, w = HSym.cons :: u}
  | _ => 0

/-- The representations of the variables and of the atomic functions of a given type. -/
def varAtomPart (Γ : List HTy) (A : HTy) : Language HSym :=
  {w | (∃ v : HVar Γ A, w = List.replicate (v.idx + 1) HSym.up) ∨ ∃ a : HAtom A, w = [a.sym] }

/-- The representations of the applications of type `A` whose function part has type `C`. -/
def appAt (S : Finset HTy) (Γ : List HTy) (n : ℕ) (A : HTy) : (C : HTy) → Language HSym
  | .arrow B A' =>
      {w | A' = A ∧ ∃ u ∈ termLang S Γ n (.arrow B A'), ∃ v ∈ termLang S Γ n B,
        w = HSym.app :: (u ++ v)}
  | _ => 0

/-- The representations of the applications of type `A` whose two parts have height at most `n`;
the type of the function part is one of the finitely many types of `S`. -/
def appPart (S : Finset HTy) (Γ : List HTy) (n : ℕ) (A : HTy) : Language HSym :=
  {w | ∃ C ∈ S, w ∈ appAt S Γ n A C}

/-- The representations of the terms whose head constructor is the one that belongs to the type:
the unit term, a pair, the empty list term, an abstraction.  A term of a co-product type is never
built by a constructor, and a `cons` is dealt with separately. -/
def ctorPart (S : Finset HTy) (Γ : List HTy) (n : ℕ) : (A : HTy) → Language HSym
  | .one => {w | w = [HSym.one]}
  | .prod X Y => {w | ∃ u ∈ termLang S Γ n X, ∃ v ∈ termLang S Γ n Y,
      w = HSym.lpar :: (u ++ HSym.comma :: (v ++ [HSym.rpar]))}
  | .sum _ _ => 0
  | .list _ => {w | w = [HSym.nil]}
  | .arrow X Y => {w | ∃ u ∈ termLang S (X :: Γ) n Y, w = HSym.lam :: (X.reprTy ++ u)}

/-- The representations of the terms of height at most `n+1` that are *not* built by `cons`. -/
def headLang (S : Finset HTy) (Γ : List HTy) (n : ℕ) (A : HTy) : Language HSym :=
  {w | A ∈ S ∧ (w ∈ varAtomPart Γ A ∨ w ∈ appPart S Γ n A ∨ w ∈ ctorPart S Γ n A)}

/-- The right-hand side of the induction step: a cons-chain of entries of height at most `n`,
followed by a term that is not a `cons`. -/
def stepLang (S : Finset HTy) (Γ : List HTy) (n : ℕ) (A : HTy) : Language HSym :=
  {w | ∃ u ∈ (consEntry S Γ n A)∗, ∃ v ∈ headLang S Γ n A, w = u ++ v}

/-! ## The induction step, as an equality of languages -/

private lemma mem_stepLang_of_head {S : Finset HTy} {Γ : List HTy} {n : ℕ} {A : HTy}
    {w : List HSym} (h : w ∈ headLang S Γ n A) : w ∈ stepLang S Γ n A :=
  ⟨[], Language.nil_mem_kstar _, w, h, (List.nil_append w).symm⟩

private lemma repr_mem_stepLang (S : Finset HTy) (n : ℕ) :
    ∀ {Γ : List HTy} {A : HTy} (t : HTerm Γ A), t.height ≤ n + 1 → t.types ⊆ S →
      t.repr ∈ stepLang S Γ n A := by
  intro Γ A t
  induction t with
  | var v =>
      intro _ ht
      exact mem_stepLang_of_head ⟨ht (by simp [HTerm.types]), Or.inl (Or.inl ⟨v, rfl⟩)⟩
  | atom a =>
      intro _ ht
      exact mem_stepLang_of_head ⟨ht (by simp [HTerm.types]), Or.inl (Or.inr ⟨a, rfl⟩)⟩
  | @app _ B C f a _ _ =>
      intro hh ht
      have hfa : f.height ≤ n ∧ a.height ≤ n := by
        simp only [HTerm.height] at hh
        omega
      have hts : (f.app a).types = insert C (f.types ∪ a.types) := rfl
      rw [hts] at ht
      have hC : C ∈ S := ht (Finset.mem_insert_self _ _)
      have hfs : f.types ⊆ S := fun x hx =>
        ht (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
      have has : a.types ⊆ S := fun x hx =>
        ht (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
      refine mem_stepLang_of_head ⟨hC, Or.inr (Or.inl ⟨HTy.arrow B C,
        hfs (HTerm.mem_types f), ?_⟩)⟩
      show _ ∈ appAt S _ n C (HTy.arrow B C)
      exact ⟨rfl, f.repr, ⟨f, hfa.1, hfs, rfl⟩, a.repr, ⟨a, hfa.2, has, rfl⟩, rfl⟩
  | @lam _ X Y b _ =>
      intro hh ht
      have hb : b.height ≤ n := by
        simp only [HTerm.height] at hh
        omega
      have hts : (HTerm.lam b).types = insert (HTy.arrow X Y) b.types := rfl
      rw [hts] at ht
      refine mem_stepLang_of_head
        ⟨ht (Finset.mem_insert_self _ _), Or.inr (Or.inr ?_)⟩
      show _ ∈ ctorPart S _ n (HTy.arrow X Y)
      exact ⟨b.repr, ⟨b, hb, fun x hx => ht (Finset.mem_insert_of_mem hx), rfl⟩, rfl⟩
  | unit =>
      intro _ ht
      refine mem_stepLang_of_head ⟨ht (by simp [HTerm.types]), Or.inr (Or.inr ?_)⟩
      show _ ∈ ctorPart S _ n HTy.one
      rfl
  | @pair _ X Y a b _ _ =>
      intro hh ht
      have hab : a.height ≤ n ∧ b.height ≤ n := by
        simp only [HTerm.height] at hh
        omega
      have hts : (a.pair b).types = insert (HTy.prod X Y) (a.types ∪ b.types) := rfl
      rw [hts] at ht
      refine mem_stepLang_of_head
        ⟨ht (Finset.mem_insert_self _ _), Or.inr (Or.inr ?_)⟩
      show _ ∈ ctorPart S _ n (HTy.prod X Y)
      exact ⟨a.repr, ⟨a, hab.1, fun x hx =>
          ht (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)), rfl⟩,
        b.repr, ⟨b, hab.2, fun x hx =>
          ht (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)), rfl⟩, rfl⟩
  | @nil _ X =>
      intro _ ht
      refine mem_stepLang_of_head ⟨ht (by simp [HTerm.types]), Or.inr (Or.inr ?_)⟩
      show _ ∈ ctorPart S _ n (HTy.list X)
      rfl
  | @cons _ X a l _ ihl =>
      intro hh ht
      have ha : a.height ≤ n := by
        simp only [HTerm.height] at hh
        omega
      have hl : l.height ≤ n + 1 := by
        simp only [HTerm.height] at hh
        omega
      have hts : (a.cons l).types = insert (HTy.list X) (a.types ∪ l.types) := rfl
      rw [hts] at ht
      have has : a.types ⊆ S := fun x hx =>
        ht (Finset.mem_insert_of_mem (Finset.mem_union_left _ hx))
      have hls : l.types ⊆ S := fun x hx =>
        ht (Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
      obtain ⟨u, hu, v, hv, huv⟩ := ihl hl hls
      refine ⟨HSym.cons :: (a.repr ++ u), ?_, v, hv, ?_⟩
      · have hsplit : HSym.cons :: (a.repr ++ u) = (HSym.cons :: a.repr) ++ u := rfl
        rw [hsplit]
        refine append_mem_kstar (mem_kstar_of_mem ?_) hu
        show _ ∈ consEntry S _ n (HTy.list X)
        exact ⟨a.repr, ⟨a, ha, has, rfl⟩, rfl⟩
      · rw [HTerm.repr_cons, huv]
        simp

private lemma stepLang_subset (S : Finset HTy) (n : ℕ) (Γ : List HTy) (A : HTy) :
    ∀ (L : List (List HSym)), (∀ z ∈ L, z ∈ consEntry S Γ n A) →
      ∀ v ∈ headLang S Γ n A, L.flatten ++ v ∈ termLang S Γ (n + 1) A := by
  intro L
  induction L with
  | nil =>
      intro _ v hv
      obtain ⟨hA, hv⟩ := hv
      simp only [List.flatten_nil, List.nil_append]
      rcases hv with (⟨x, rfl⟩ | ⟨a, rfl⟩) | ⟨C, hC, hv⟩ | hv
      · refine ⟨HTerm.var x, Nat.le_add_left 1 n, ?_, rfl⟩
        intro y hy
        simp only [HTerm.types, Finset.mem_singleton] at hy
        exact hy ▸ hA
      · refine ⟨HTerm.atom a, Nat.le_add_left 1 n, ?_, rfl⟩
        intro y hy
        simp only [HTerm.types, Finset.mem_singleton] at hy
        exact hy ▸ hA
      · match C, hv with
        | .one, hv => exact hv.elim
        | .prod _ _, hv => exact hv.elim
        | .sum _ _, hv => exact hv.elim
        | .list _, hv => exact hv.elim
        | .arrow B A', hv =>
            obtain ⟨hAA, u, ⟨f, hf, hfs, rfl⟩, w, ⟨a, ha, has, rfl⟩, rfl⟩ := hv
            subst hAA
            refine ⟨f.app a, ?_, ?_, rfl⟩
            · simp only [HTerm.height]
              omega
            · intro y hy
              have hy' : y ∈ insert A' (f.types ∪ a.types) := hy
              rcases Finset.mem_insert.mp hy' with h | h
              · exact h ▸ hA
              · rcases Finset.mem_union.mp h with h | h
                exacts [hfs h, has h]
      · match A, hA, hv with
        | .one, hA, hv =>
            refine ⟨HTerm.unit, Nat.le_add_left 1 n, ?_, (hv : _ = _).symm⟩
            intro y hy
            simp only [HTerm.types, Finset.mem_singleton] at hy
            exact hy ▸ hA
        | .prod X Y, hA, hv =>
            obtain ⟨u, ⟨a, ha, has, rfl⟩, w, ⟨b, hb, hbs, rfl⟩, rfl⟩ := hv
            refine ⟨a.pair b, ?_, ?_, rfl⟩
            · simp only [HTerm.height]
              omega
            · intro y hy
              have hy' : y ∈ insert (HTy.prod X Y) (a.types ∪ b.types) := hy
              rcases Finset.mem_insert.mp hy' with h | h
              · exact h ▸ hA
              · rcases Finset.mem_union.mp h with h | h
                exacts [has h, hbs h]
        | .sum _ _, _, hv => exact hv.elim
        | .list X, hA, hv =>
            refine ⟨HTerm.nil, Nat.le_add_left 1 n, ?_, (hv : _ = _).symm⟩
            intro y hy
            simp only [HTerm.types, Finset.mem_singleton] at hy
            exact hy ▸ hA
        | .arrow X Y, hA, hv =>
            obtain ⟨u, ⟨b, hb, hbs, rfl⟩, rfl⟩ := hv
            refine ⟨HTerm.lam b, ?_, ?_, rfl⟩
            · simp only [HTerm.height]
              omega
            · intro y hy
              have hy' : y ∈ insert (HTy.arrow X Y) b.types := hy
              rcases Finset.mem_insert.mp hy' with h | h
              · exact h ▸ hA
              · exact hbs h
  | cons z L ih =>
      intro hz v hv
      have hzc : z ∈ consEntry S Γ n A := hz z (List.mem_cons_self ..)
      have hrest : ∀ y ∈ L, y ∈ consEntry S Γ n A := fun y hy => hz y (List.mem_cons_of_mem _ hy)
      obtain ⟨l, hlh, hlt, hlr⟩ := ih hrest v hv
      match A, hzc, l, hlh, hlt, hlr with
      | .one, hzc, _, _, _, _ => exact hzc.elim
      | .prod _ _, hzc, _, _, _, _ => exact hzc.elim
      | .sum _ _, hzc, _, _, _, _ => exact hzc.elim
      | .arrow _ _, hzc, _, _, _, _ => exact hzc.elim
      | .list X, hzc, l, hlh, hlt, hlr =>
          obtain ⟨u, ⟨a, ha, has, rfl⟩, rfl⟩ := hzc
          refine ⟨a.cons l, ?_, ?_, ?_⟩
          · simp only [HTerm.height]
            omega
          · intro y hy
            have hy' : y ∈ insert (HTy.list X) (a.types ∪ l.types) := hy
            rcases Finset.mem_insert.mp hy' with h | h
            · exact hlt (h ▸ HTerm.mem_types l)
            · rcases Finset.mem_union.mp h with h | h
              exacts [has h, hlt h]
          · rw [HTerm.repr_cons, hlr]
            simp

/-- The induction step: the representations of the terms of height at most `n+1` are the
cons-chains of entries of height at most `n` followed by a term that is not a `cons`. -/
theorem termLang_succ (S : Finset HTy) (Γ : List HTy) (n : ℕ) (A : HTy) :
    termLang S Γ (n + 1) A = stepLang S Γ n A := by
  ext w
  constructor
  · rintro ⟨t, hh, ht, rfl⟩
    exact repr_mem_stepLang S n t hh ht
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hu
    exact stepLang_subset S n Γ A L hL v hv

/-! ## Regularity, by induction on the height -/

private lemma isRegular_varAtomPart (Γ : List HTy) (A : HTy) :
    (varAtomPart Γ A).IsRegular := by
  classical
  refine isRegular_of_subset_finite
    (F := ((Finset.range (Γ.length + 1)).image fun i => List.replicate (i + 1) HSym.up)
      ∪ (Finset.univ.image fun c : HSym => [c])) ?_
  rintro w (⟨v, rfl⟩ | ⟨a, rfl⟩)
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v.idx,
      Finset.mem_range.mpr (Nat.lt_succ_of_lt v.idx_lt), rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a.sym, Finset.mem_univ _, rfl⟩)

/-- Every language of the induction is regular. -/
theorem termLang_isRegular (S : Finset HTy) :
    ∀ (n : ℕ) (Γ : List HTy) (A : HTy), (termLang S Γ n A).IsRegular := by
  intro n
  induction n with
  | zero =>
      intro Γ A
      have h0 : termLang S Γ 0 A = (0 : Language HSym) := by
        ext w
        refine ⟨fun hw => ?_, fun hw => hw.elim⟩
        obtain ⟨t, hh, -, -⟩ := hw
        exact absurd (le_trans (HTerm.one_le_height t) hh) (by omega)
      rw [h0]
      exact isRegular_zero
  | succ n ih =>
      intro Γ A
      rw [termLang_succ]
      have hcons : (consEntry S Γ n A).IsRegular := by
        match A with
        | .one => exact isRegular_zero
        | .prod _ _ => exact isRegular_zero
        | .sum _ _ => exact isRegular_zero
        | .arrow _ _ => exact isRegular_zero
        | .list X =>
            refine isRegular_of_eq ?_
              (isRegular_concat (isRegular_singleton [HSym.cons]) (ih Γ X))
            ext w
            constructor
            · rintro ⟨-, rfl, v, hv, rfl⟩
              exact ⟨v, hv, rfl⟩
            · rintro ⟨u, hu, rfl⟩
              exact ⟨[HSym.cons], rfl, u, hu, rfl⟩
      have happ : (appPart S Γ n A).IsRegular := by
        refine isRegular_biUnion_finset S (fun C => appAt S Γ n A C) fun C _ => ?_
        match C with
        | .one => exact isRegular_zero
        | .prod _ _ => exact isRegular_zero
        | .sum _ _ => exact isRegular_zero
        | .list _ => exact isRegular_zero
        | .arrow B A' =>
            refine isRegular_prop_and (A' = A) ?_
            refine isRegular_of_eq ?_
              (isRegular_concat (isRegular_singleton [HSym.app])
                (isRegular_concat (ih Γ (.arrow B A')) (ih Γ B)))
            ext w
            constructor
            · rintro ⟨-, rfl, -, ⟨p, hp, q, hq, rfl⟩, rfl⟩
              exact ⟨p, hp, q, hq, rfl⟩
            · rintro ⟨p, hp, q, hq, rfl⟩
              exact ⟨[HSym.app], rfl, p ++ q, ⟨p, hp, q, hq, rfl⟩, rfl⟩
      have hctor : (ctorPart S Γ n A).IsRegular := by
        match A with
        | .one => exact isRegular_singleton _
        | .sum _ _ => exact isRegular_zero
        | .list _ => exact isRegular_singleton _
        | .prod X Y =>
            refine isRegular_of_eq ?_
              (isRegular_concat (isRegular_singleton [HSym.lpar])
                (isRegular_concat (ih Γ X)
                  (isRegular_concat (isRegular_singleton [HSym.comma])
                    (isRegular_concat (ih Γ Y) (isRegular_singleton [HSym.rpar])))))
            ext w
            constructor
            · rintro ⟨-, rfl, -, ⟨p, hp, -, ⟨-, rfl, -, ⟨q, hq, -, rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩
              exact ⟨p, hp, q, hq, by simp⟩
            · rintro ⟨p, hp, q, hq, rfl⟩
              exact ⟨[HSym.lpar], rfl, _, ⟨p, hp, _, ⟨[HSym.comma], rfl, _,
                ⟨q, hq, [HSym.rpar], rfl, rfl⟩, rfl⟩, rfl⟩, by simp⟩
        | .arrow X Y =>
            refine isRegular_of_eq ?_
              (isRegular_concat (isRegular_singleton (HSym.lam :: X.reprTy)) (ih (X :: Γ) Y))
            ext w
            constructor
            · rintro ⟨-, rfl, u, hu, rfl⟩
              exact ⟨u, hu, by simp⟩
            · rintro ⟨u, hu, rfl⟩
              exact ⟨HSym.lam :: X.reprTy, rfl, u, hu, by simp⟩
      have hhead : (headLang S Γ n A).IsRegular :=
        isRegular_prop_and (A ∈ S)
          (isRegular_union (isRegular_varAtomPart Γ A) (isRegular_union happ hctor))
      exact isRegular_concat (isRegular_kstar hcons) hhead

/-! ## Lemma `claim:parsing-is-regular-with-resource-bounds` -/

/-- **Lemma `claim:parsing-is-regular-with-resource-bounds`.**  For every resource bound, the set
of strings that represent a closed term consistent with the bound is a regular language. -/
theorem parsing_isRegular_of_resourceBound (R : ResourceBound) :
    Language.IsRegular
      {w : List HSym | ∃ (H : HTy) (t : HTerm [] H), R.Consistent t ∧ t.repr = w} := by
  have he : {w : List HSym | ∃ H ∈ R.types, w ∈ termLang R.types [] R.height H}
      = {w : List HSym | ∃ (H : HTy) (t : HTerm [] H), R.Consistent t ∧ t.repr = w} := by
    ext w
    constructor
    · rintro ⟨H, -, t, hh, ht, rfl⟩
      exact ⟨H, t, ⟨hh, ht⟩, rfl⟩
    · rintro ⟨H, t, ⟨hh, ht⟩, rfl⟩
      exact ⟨H, ht (HTerm.mem_types t), t, hh, ht, rfl⟩
  exact he ▸ isRegular_biUnion_finset R.types _ fun H _ => termLang_isRegular R.types R.height [] H

/-! ## Two sanity checks

The language of the lemma is not the empty one: below are the representations of the unit term and
of the list term `[1]`, each with a resource bound that it is consistent with. -/

example : [HSym.one] ∈
    {w : List HSym | ∃ (H : HTy) (t : HTerm [] H),
      (⟨{HTy.one}, 1, le_refl 1⟩ : ResourceBound).Consistent t ∧ t.repr = w} :=
  ⟨HTy.one, HTerm.unit, ⟨le_refl 1, by simp [HTerm.types]⟩, rfl⟩

example : [HSym.cons, HSym.one, HSym.nil] ∈
    {w : List HSym | ∃ (H : HTy) (t : HTerm [] H),
      (⟨{HTy.one, HTy.list HTy.one}, 2, by omega⟩ : ResourceBound).Consistent t ∧ t.repr = w} :=
  ⟨HTy.list HTy.one, HTerm.cons HTerm.unit HTerm.nil,
    ⟨by simp [HTerm.height], by simp [HTerm.types]⟩, rfl⟩

end Transducers
