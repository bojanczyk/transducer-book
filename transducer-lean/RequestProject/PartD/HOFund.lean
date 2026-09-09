/-
Part D, Section *A functional programming language*: the fundamental lemma of the logical relation
of `RequestProject/PartD/HORel.lean`.

`Transducers.HTerm.rel_eval` says that a term which uses only the reduced set of atomic functions
of Lemma `lem:fewer-atomic` sends related valuations of its free variables to a related family.
The work is in the ten atomic functions of the reduced set: each of them gets one lemma below, and
the two that carry the content are `map` -- whose body may use the parameter, which is what the map
with a parameter of `RequestProject/PartD/HOPoly.lean` is for -- and `concat`, where the two levels
of indices of a list of lists are combined into one.
-/
import RequestProject.PartD.HORel

namespace Transducers

open Comb

/-! ## Auxiliary facts about lists -/

/-- The last entry of the running products of a list is the product of the list. -/
theorem scanl_getLast?_mul {M : Type} [Monoid M] :
    ∀ (l : List M) (h : M), (l.scanl (· * ·) h).getLast? = some (h * l.prod)
  | [], h => by simp
  | a :: l, h => by
      have hs : ((a :: l).scanl (· * ·) h) = h :: (l.scanl (· * ·) (h * a)) := by
        simp [List.scanl]
      have hne : (l.scanl (· * ·) (h * a)) ≠ [] := by
        cases l <;> simp [List.scanl]
      obtain ⟨x, xs, hx⟩ : ∃ x xs, (l.scanl (· * ·) (h * a)) = x :: xs := by
        cases hl : (l.scanl (· * ·) (h * a)) with
        | nil => exact absurd hl hne
        | cons x xs => exact ⟨x, xs, rfl⟩
      rw [hs, hx, List.getLast?_cons_cons, ← hx, scanl_getLast?_mul l (h * a)]
      rw [List.prod_cons, mul_assoc]

/-- The product of a list is the last of its prefix products, and the neutral element if the list
is empty. -/
theorem prefixProd_getLast? {M : Type} [Monoid M] :
    ∀ l : List M, (prefixProd l).getLast? = if l = [] then none else some l.prod
  | [] => rfl
  | a :: l => by
      have hs : ((a :: l).scanl (· * ·) 1) = 1 :: (l.scanl (· * ·) (1 * a)) := by
        simp [List.scanl]
      have h := scanl_getLast?_mul l (1 * a)
      show ((a :: l).scanl (· * ·) 1).tail.getLast? = _
      rw [hs]
      show (l.scanl (· * ·) (1 * a)).getLast? = _
      rw [h]
      simp [List.prod_cons]

/-! ## More regular functions between types -/

/-- The head of a list, with a default value. -/
theorem isRegularUnderRepr_headD (A : Ty) (d : A.Elt) :
    IsRegularUnderRepr (A := .list A) (B := A) (fun u => u.headD d) := by
  refine ((isRegularUnderRepr_head A).comp
    (IsRegularUnderRepr.copair (isRegularUnderRepr_const (A := .one) (B := A) d)
      (isRegularUnderRepr_id A))).congr (fun u => ?_)
  cases u <;> rfl

/-- Putting a fixed element in front of a list. -/
theorem isRegularUnderRepr_consConst (A : Ty) (c : A.Elt) :
    IsRegularUnderRepr (A := .list A) (B := .list A) (fun u => c :: u) := by
  refine ((IsRegularUnderRepr.pair (isRegularUnderRepr_const (A := .list A) (B := A) c)
    (isRegularUnderRepr_id (.list A))).comp
    ((isRegularUnderRepr_inr .one (.prod A (.list A))).comp
      (isRegularUnderRepr_cons A))).congr (fun u => rfl)

/-- **The product of a list of group elements is regular under string representation**: it is the
last of the prefix products of the list. -/
theorem isRegularUnderRepr_listProd (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    IsRegularUnderRepr (A := .list G) (B := G) (fun v => v.prod) := by
  letI := grp
  haveI := hfin
  have hlast : IsRegularUnderRepr (A := .list G) (B := G)
      (fun u => Sum.elim (fun _ => (1 : G.Elt)) (fun g => g)
        (match u.reverse with | [] => Sum.inl () | g :: _ => Sum.inr g)) :=
    (isRegularUnderRepr_reverse G).comp
      ((isRegularUnderRepr_head G).comp
        (IsRegularUnderRepr.copair (isRegularUnderRepr_const (A := .one) (B := G) 1)
          (isRegularUnderRepr_id G)))
  refine ((isRegularUnderRepr_pref G).comp hlast).congr (fun v => ?_)
  show Sum.elim (fun _ => (1 : G.Elt)) (fun g => g)
    (match (prefixProd v).reverse with | [] => Sum.inl () | g :: _ => Sum.inr g) = v.prod
  have h := prefixProd_getLast? (M := G.Elt) v
  by_cases hv : v = []
  · rw [hv]; rfl
  · rw [if_neg hv] at h
    have hrev : (prefixProd v).reverse.head? = some v.prod := by
      rw [List.head?_reverse, h]
    cases hr : (prefixProd v).reverse with
    | nil => rw [hr] at hrev; simp at hrev
    | cons g gs =>
        rw [hr] at hrev
        simp only [List.head?_cons, Option.some.injEq] at hrev
        exact hrev

/-! ## Related valuations -/

/-- The value of the first variable of a valuation. -/
def HEnv.head : {A : HTy} → {Γ : List HTy} → HEnv (A :: Γ) → A.Sem
  | _, _, .cons x _ => x

/-- The valuation of the remaining variables. -/
def HEnv.tail : {A : HTy} → {Γ : List HTy} → HEnv (A :: Γ) → HEnv Γ
  | _, _, .cons _ e => e

@[simp] lemma HEnv.head_cons {A : HTy} {Γ : List HTy} (x : A.Sem) (e : HEnv Γ) :
    (HEnv.cons x e).head = x := rfl

@[simp] lemma HEnv.tail_cons {A : HTy} {Γ : List HTy} (x : A.Sem) (e : HEnv Γ) :
    (HEnv.cons x e).tail = e := rfl

@[simp] lemma HVar.lookup_zero {A : HTy} {Γ : List HTy} (e : HEnv (A :: Γ)) :
    (HVar.zero (Γ := Γ) (A := A)).lookup e = e.head := by
  cases e; rfl

@[simp] lemma HVar.lookup_succ {A B : HTy} {Γ : List HTy} (v : HVar Γ A) (e : HEnv (B :: Γ)) :
    (v.succ).lookup e = v.lookup e.tail := by
  cases e; rfl

/-- A family of valuations of a context is *related* if the value of every variable is a related
family. -/
def RelEnv : (Γ : List HTy) → (P : Ty) → (P.Elt → HEnv Γ) → Prop
  | [], _, _ => True
  | H :: Γ, P, g => Rel H P (fun p => (g p).head) ∧ RelEnv Γ P (fun p => (g p).tail)

theorem RelEnv.reindex : ∀ (Γ : List HTy) {P Q : Ty} {g : P.Elt → HEnv Γ} {r : Q.Elt → P.Elt},
    RelEnv Γ P g → IsPolyregularUnderRepr r → RelEnv Γ Q (fun q => g (r q))
  | [], _, _, _, _, _, _ => trivial
  | _ :: Γ, _, _, _, _, h, hr => ⟨Rel.reindex _ h.1 hr, RelEnv.reindex Γ h.2 hr⟩

theorem HVar.rel_lookup : ∀ {Γ : List HTy} {A : HTy} (v : HVar Γ A) {P : Ty}
    {g : P.Elt → HEnv Γ}, RelEnv Γ P g → Rel A P (fun p => v.lookup (g p))
  | _, _, .zero, _, g, h => h.1.congr (fun p => (HVar.lookup_zero (g p)).symm)
  | _, _, .succ v, _, g, h =>
      (HVar.rel_lookup v h.2).congr (fun p => (HVar.lookup_succ v (g p)).symm)

/-! ## The list term constructors are related -/

section Terms

variable {P : Ty}

/-- The empty list term. -/
theorem rel_nil (A : HTy) : Rel (.list A) P (fun _ => ([] : List A.Sem)) := by
  obtain ⟨cA, hcA⟩ := Rel.exists_const A
  exact ⟨.one, fun _ => [], fun _ => cA,
    isPolyregularUnderRepr_const (A := P) (B := .list .one) [],
    hcA (.prod P .one), fun _ => rfl⟩

/-- Putting a related family in front of a related list. -/
theorem rel_cons {A : HTy} {a : P.Elt → A.Sem} {L : P.Elt → List A.Sem}
    (ha : Rel A P a) (hL : Rel (.list A) P L) : Rel (.list A) P (fun p => a p :: L p) := by
  obtain ⟨Q, l, e, hl, he, heq⟩ := hL
  refine ⟨.sum .one Q, fun p => Sum.inl () :: (l p).map Sum.inr,
    fun z => Sum.elim (fun _ => a z.1) (fun q => e (z.1, q)) z.2, ?_, ?_, ?_⟩
  · exact (hl.comp (IsRegularUnderRepr.mapList
      (isRegularUnderRepr_inr .one Q)).isPolyregularUnderRepr).comp
      (isRegularUnderRepr_consConst (.sum .one Q) (Sum.inl ())).isPolyregularUnderRepr
  · have htag : IsPolyregularUnderRepr (A := .prod P (.sum .one Q)) (B := .sum .one .one)
        (fun z => Sum.map (fun _ => ()) (fun _ => ()) z.2) :=
      ((isRegularUnderRepr_snd P (.sum .one Q)).comp
        (isRegularUnderRepr_sumTag .one Q)).isPolyregularUnderRepr
    have h1 : Rel A (.prod P (.sum .one Q)) (fun z => a z.1) :=
      Rel.reindex A (P := P) (Q := .prod P (.sum .one Q)) ha
        (isRegularUnderRepr_fst P (.sum .one Q)).isPolyregularUnderRepr
    have h2 : Rel A (.prod P (.sum .one Q))
        (fun z => e (z.1, Sum.elim (fun _ => default) (fun q => q) z.2)) := by
      refine Rel.reindex A (P := .prod P Q) (Q := .prod P (.sum .one Q)) he ?_
      exact IsPolyregularUnderRepr.prodMap
        (isRegularUnderRepr_id P).isPolyregularUnderRepr
        (isRegularUnderRepr_elimDefaultRight .one Q).isPolyregularUnderRepr
    refine (Rel.glue A htag h1 h2).congr (fun z => ?_)
    obtain ⟨p, x⟩ := z
    cases x <;> rfl
  · intro p
    beta_reduce
    rw [heq p]
    simp [List.map_map, Function.comp_def]

end Terms

/-! ## The atomic functions of the reduced set are related -/

section Atoms

variable {P : Ty}

theorem rel_atom_fst (A B : HTy) : Rel (.arrow (.prod A B) A) P (fun _ => fun x => x.1) :=
  fun _ _ _ _ ha => ha.1

theorem rel_atom_snd (A B : HTy) : Rel (.arrow (.prod A B) B) P (fun _ => fun x => x.2) :=
  fun _ _ _ _ ha => ha.2

theorem rel_atom_inl (A B : HTy) :
    Rel (.arrow A (.sum A B)) P (fun _ => fun x => Sum.inl x) := by
  intro Q _ _ a ha
  obtain ⟨cB, hcB⟩ := Rel.exists_const B
  exact ⟨a, fun _ => cB, ha, hcB Q,
    (isPolyregularUnderRepr_const (A := Q) (B := .sum .one .one) (Sum.inl ())).congr
      (fun _ => rfl),
    fun _ => Or.inl rfl⟩

theorem rel_atom_inr (A B : HTy) :
    Rel (.arrow B (.sum A B)) P (fun _ => fun x => Sum.inr x) := by
  intro Q _ _ b hb
  obtain ⟨cA, hcA⟩ := Rel.exists_const A
  exact ⟨fun _ => cA, b, hcA Q, hb,
    (isPolyregularUnderRepr_const (A := Q) (B := .sum .one .one) (Sum.inr ())).congr
      (fun _ => rfl),
    fun _ => Or.inr rfl⟩

theorem rel_atom_uncons (A : HTy) :
    Rel (.arrow (.list A) (.sum .one (.prod A (.list A)))) P
      (fun _ => fun l => match l with | [] => Sum.inl () | a :: l' => Sum.inr (a, l')) := by
  intro Q _ _ L hL
  obtain ⟨Q₁, l, e, hl, he, heq⟩ := hL
  refine ⟨fun _ => (), fun q => (e (q, (l q).headD default),
      (l q).tail.map (fun x => e (q, x))), trivial, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine Rel.reindex A (P := .prod Q Q₁) (Q := Q) he ?_
    exact IsPolyregularUnderRepr.pair (isRegularUnderRepr_id Q).isPolyregularUnderRepr
      (hl.comp (isRegularUnderRepr_headD Q₁ default).isPolyregularUnderRepr)
  · exact ⟨Q₁, fun q => (l q).tail, e,
      hl.comp (isRegularUnderRepr_tail Q₁).isPolyregularUnderRepr, he, fun _ => rfl⟩
  · refine (hl.comp (isRegularUnderRepr_isEmpty Q₁).isPolyregularUnderRepr).congr (fun q => ?_)
    beta_reduce
    rw [heq q]
    cases l q <;> rfl
  · intro q
    beta_reduce
    rw [heq q]
    cases hlq : l q with
    | nil => exact Or.inl rfl
    | cons x xs =>
        refine Or.inr ?_
        simp

theorem rel_atom_concat (A : HTy) :
    Rel (.arrow (.list (.list A)) (.list A)) P (fun _ => fun l => l.flatten) := by
  intro Q _ _ L hL
  obtain ⟨Q₁, l₁, e₁, hl₁, he₁, heq₁⟩ := hL
  obtain ⟨Q₂, l₂, e₂, hl₂, he₂, heq₂⟩ := he₁
  refine ⟨.prod Q₁ Q₂,
    fun q => ((l₁ q).map (fun x => (l₂ (q, x)).map (fun y => (x, y)))).flatten,
    fun z => e₂ ((z.1, z.2.1), z.2.2), ?_, ?_, ?_⟩
  · have hF : IsPolyregularUnderRepr (A := .prod Q Q₁) (B := .list (.prod Q₁ Q₂))
        (fun x => (l₂ x).map (fun y => (x.2, y))) := by
      refine IsPolyregularUnderRepr.mapParam (P := .prod Q Q₁) (Q := Q₂) (R := .prod Q₁ Q₂)
        (f := fun z => (z.1.2, z.2)) hl₂ ?_
      exact (IsRegularUnderRepr.pair
        ((isRegularUnderRepr_fst (.prod Q Q₁) Q₂).comp (isRegularUnderRepr_snd Q Q₁))
        (isRegularUnderRepr_snd (.prod Q Q₁) Q₂)).isPolyregularUnderRepr
    exact (IsPolyregularUnderRepr.mapParam (P := Q) (Q := Q₁) (R := .list (.prod Q₁ Q₂))
      hl₁ hF).comp (isRegularUnderRepr_concat (.prod Q₁ Q₂)).isPolyregularUnderRepr
  · refine Rel.reindex A (P := .prod (.prod Q Q₁) Q₂) (Q := .prod Q (.prod Q₁ Q₂)) he₂ ?_
    exact (IsRegularUnderRepr.pair
      (IsRegularUnderRepr.pair (isRegularUnderRepr_fst Q (.prod Q₁ Q₂))
        ((isRegularUnderRepr_snd Q (.prod Q₁ Q₂)).comp (isRegularUnderRepr_fst Q₁ Q₂)))
      ((isRegularUnderRepr_snd Q (.prod Q₁ Q₂)).comp
        (isRegularUnderRepr_snd Q₁ Q₂))).isPolyregularUnderRepr
  · intro q
    beta_reduce
    rw [heq₁ q]
    simp only [List.map_flatten, List.map_map, Function.comp_def]
    congr 1
    refine List.map_congr_left (fun x _ => ?_)
    rw [heq₂ (q, x)]

theorem rel_atom_splits (A : HTy) :
    Rel (.arrow (.list A) (.list (.prod (.list A) (.list A)))) P
      (fun _ => fun l => splitsList l) := by
  intro Q _ _ L hL
  obtain ⟨Q₁, l, e, hl, he, heq⟩ := hL
  have hreindex : IsPolyregularUnderRepr
      (A := .prod (.prod Q (.prod (.list Q₁) (.list Q₁))) Q₁) (B := .prod Q Q₁)
      (fun w => (w.1.1, w.2)) :=
    (IsRegularUnderRepr.pair
      ((isRegularUnderRepr_fst (.prod Q (.prod (.list Q₁) (.list Q₁))) Q₁).comp
        (isRegularUnderRepr_fst Q (.prod (.list Q₁) (.list Q₁))))
      (isRegularUnderRepr_snd (.prod Q (.prod (.list Q₁) (.list Q₁))) Q₁)).isPolyregularUnderRepr
  refine ⟨.prod (.list Q₁) (.list Q₁), fun q => splitsList (l q),
    fun z => (z.2.1.map (fun x => e (z.1, x)), z.2.2.map (fun x => e (z.1, x))), ?_, ⟨?_, ?_⟩, ?_⟩
  · exact hl.comp (isPolyregularUnderRepr_splits Q₁)
  · exact ⟨Q₁, fun z => z.2.1, fun w => e (w.1.1, w.2),
      ((isRegularUnderRepr_snd Q (.prod (.list Q₁) (.list Q₁))).comp
        (isRegularUnderRepr_fst (.list Q₁) (.list Q₁))).isPolyregularUnderRepr,
      Rel.reindex A he hreindex, fun _ => rfl⟩
  · exact ⟨Q₁, fun z => z.2.2, fun w => e (w.1.1, w.2),
      ((isRegularUnderRepr_snd Q (.prod (.list Q₁) (.list Q₁))).comp
        (isRegularUnderRepr_snd (.list Q₁) (.list Q₁))).isPolyregularUnderRepr,
      Rel.reindex A he hreindex, fun _ => rfl⟩
  · intro q
    beta_reduce
    rw [heq q, splitsList_map]
    rfl

theorem rel_atom_mult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
    Rel (.arrow (.list (HTy.ofTy G)) (HTy.ofTy G)) P (fun _ => fun l => groupProd G grp l) := by
  letI := grp
  haveI := hfin
  intro Q _ _ L hL
  obtain ⟨Q₁, l, e, hl, he, heq⟩ := hL
  have he' := (Rel.iff_polyregular G (P := .prod Q Q₁) e).mp he
  refine (Rel.iff_polyregular G (P := Q) _).mpr ?_
  refine ((IsPolyregularUnderRepr.mapParam (P := Q) (Q := Q₁) (R := G) hl he').comp
    (isRegularUnderRepr_listProd G grp hfin).isPolyregularUnderRepr).congr (fun q => ?_)
  show ((l q).map (fun x => HTy.toElt G (e (q, x)))).prod = HTy.toElt G (groupProd G grp (L q))
  rw [show HTy.toElt G (groupProd G grp (L q)) = ((L q).map (HTy.toElt G)).prod from
    HTy.toElt_ofElt G _]
  rw [heq q, List.map_map]
  rfl

theorem rel_atom_map (A B : HTy) :
    Rel (.arrow (.arrow A B) (.arrow (.list A) (.list B))) P (fun _ => fun f l => l.map f) := by
  intro _ _ _ F hF Q' r' hr' L hL
  obtain ⟨Q₁, l, e, hl, he, heq⟩ := hL
  refine ⟨Q₁, l, fun z => F (r' z.1) (e z), hl, ?_, ?_⟩
  · exact (hF (.prod Q' Q₁) (fun z => r' z.1)
      ((isRegularUnderRepr_fst Q' Q₁).isPolyregularUnderRepr.comp hr') e he).congr (fun _ => rfl)
  · intro q
    beta_reduce
    rw [heq q, List.map_map]
    rfl

theorem rel_atom_either (A B C : HTy) :
    Rel (.arrow (.arrow A C) (.arrow (.arrow B C) (.arrow (.sum A B) C))) P
      (fun _ => fun f g x => Sum.elim f g x) := by
  intro _ _ _ F hF _ r₂ hr₂ G hG Q₃ r₃ hr₃ x hx
  obtain ⟨a, b, ha, hb, htag, hcons⟩ := hx
  have hu : Rel C Q₃ (fun q => F (r₂ (r₃ q)) (a q)) :=
    (hF Q₃ (fun q => r₂ (r₃ q)) (hr₃.comp hr₂) a ha).congr (fun _ => rfl)
  have hv : Rel C Q₃ (fun q => G (r₃ q) (b q)) :=
    (hG Q₃ r₃ hr₃ b hb).congr (fun _ => rfl)
  refine (Rel.glue C (t := fun q => Sum.map (fun _ => ()) (fun _ => ()) (x q)) htag hu hv).congr
    (fun q => ?_)
  rcases hcons q with hq | hq <;> rw [hq] <;> rfl

end Atoms

/-! ## The fundamental lemma -/

/-- **The fundamental lemma.**  A term that uses only the reduced set of atomic functions of Lemma
`lem:fewer-atomic` sends a related family of valuations of its free variables to a related family
of values. -/
theorem HTerm.rel_eval : ∀ {Γ : List HTy} {H : HTy} (t : HTerm Γ H), t.Small →
    ∀ {P : Ty} {g : P.Elt → HEnv Γ}, RelEnv Γ P g → Rel H P (fun p => t.eval (g p))
  | _, _, .var v, _, _, _, hg => (HVar.rel_lookup v hg).congr (fun _ => rfl)
  | _, _, .atom a, hs, _, _, _ => by
      cases a with
      | fst A B => exact rel_atom_fst A B
      | snd A B => exact rel_atom_snd A B
      | inl A B => exact rel_atom_inl A B
      | inr A B => exact rel_atom_inr A B
      | uncons A => exact rel_atom_uncons A
      | concat A => exact rel_atom_concat A
      | splits A => exact rel_atom_splits A
      | map A B => exact rel_atom_map A B
      | either A B C => exact rel_atom_either A B C
      | mult G grp hfin => exact rel_atom_mult G grp hfin
      | idA A => exact False.elim hs
      | diag A => exact False.elim hs
      | codiag A => exact False.elim hs
      | distr A B C => exact False.elim hs
      | consA A => exact False.elim hs
      | reverse A => exact False.elim hs
      | blockSplit A B => exact False.elim hs
      | pref G grp hfin => exact False.elim hs
  | _, _, .app f a, hs, _, _, hg =>
      ((HTerm.rel_eval f hs.1 hg) _ (fun p => p)
        (isRegularUnderRepr_id _).isPolyregularUnderRepr _
        (HTerm.rel_eval a hs.2 hg)).congr (fun _ => rfl)
  | _, _, .lam b, hs, _, g, hg => by
      intro Q r hr x hx
      exact (HTerm.rel_eval b hs (P := Q) (g := fun q => .cons (x q) (g (r q)))
        ⟨hx.congr (fun _ => rfl), RelEnv.reindex _ hg hr⟩).congr (fun _ => rfl)
  | _, _, .unit, _, _, _, _ => trivial
  | _, _, .pair a b, hs, _, _, hg =>
      ⟨(HTerm.rel_eval a hs.1 hg).congr (fun _ => rfl),
        (HTerm.rel_eval b hs.2 hg).congr (fun _ => rfl)⟩
  | _, _, .nil, _, _, _, _ => (rel_nil _).congr (fun _ => rfl)
  | _, _, .cons a l, hs, _, _, hg =>
      (rel_cons (HTerm.rel_eval a hs.1 hg) (HTerm.rel_eval l hs.2 hg)).congr (fun _ => rfl)

/-! ## The hard direction of Theorem `thm:higher-order-terms` -/

/-- **Every function between arrow-free types that is defined by a term with the reduced set of
atomic functions is polyregular under string representation.** -/
theorem isPolyregularUnderRepr_of_smallHigherOrderTermFun {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsSmallHigherOrderTermFun f) : IsPolyregularUnderRepr f := by
  obtain ⟨t, hsmall, ht⟩ := h
  have hrel : Rel (.arrow (HTy.ofTy A) (HTy.ofTy B)) .one
      (fun _ => t.eval .nil) :=
    (HTerm.rel_eval t hsmall (P := .one) (g := fun _ => .nil) trivial).congr (fun _ => rfl)
  have hid : Rel (HTy.ofTy A) A (fun a => HTy.ofElt A a) := by
    refine (Rel.iff_polyregular A (P := A) _).mpr ?_
    exact (isRegularUnderRepr_id A).isPolyregularUnderRepr.congr
      (fun a => (HTy.toElt_ofElt A a).symm)
  have happ : Rel (HTy.ofTy B) A (fun a => t.eval .nil (HTy.ofElt A a)) :=
    (hrel A (fun _ => ()) (isPolyregularUnderRepr_const (A := A) (B := .one) ())
      (fun a => HTy.ofElt A a) hid).congr (fun _ => rfl)
  exact ((Rel.iff_polyregular B (P := A) _).mp happ).congr ht

end Transducers
