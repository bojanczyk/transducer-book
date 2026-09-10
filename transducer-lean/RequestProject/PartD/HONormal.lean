/-
Part D, Section *A functional programming language*: Lemma `lem:normal-forms-of-arrow-free-terms`.

The lemma says that a closed term whose type is arrow-free is in normal form if and only if it is
built using the value constructors `(a,b)`, `[a₁,…,aₙ]`, `left a`, `right b` and `1`.  Those terms
are `Transducers.HTerm.IsValue`, and the lemma is `Transducers.normal_iff_isValue`.

As everywhere in Section *Expressive completeness*, the atomic functions are the reduced set of
Lemma `lem:fewer-atomic` (`Transducers.HTerm.Small`); this hypothesis cannot be dropped, because an
atomic function outside that set -- `diag`, say -- has no reduction rule, so `diag a` would be a
closed normal term of product type that is not a pair.

The book proves the lemma by "an inspection of the shapes of closed terms in normal form", and that
inspection is `Transducers.HTerm.Shape` below: a closed term of the reduced language that is in
normal form is a value, an abstraction, or an atomic function applied to fewer arguments than its
reduction rule requires -- and the last two possibilities have arrow type.  `Shape` records the
classification *hereditarily* in the value cases, which is what makes the induction go through: the
argument of `concat`, of `split`, of `map` and of `mult` must be recognised as a list term, entry by
entry, before the rule applies to it, and the argument of `mult` must moreover be recognised as a
list of group values.
-/
import RequestProject.PartD.HORed

namespace Transducers

namespace HTerm

/-! ## Values -/

/-- **The value terms of Lemma `lem:normal-forms-of-arrow-free-terms`**: the terms built using the
term constructors `1`, `(a,b)` and `[a₁,…,aₙ]` (a cons-chain here) and the co-projections
`left a`, `right b`. -/
inductive IsValue : {Γ : List HTy} → {A : HTy} → HTerm Γ A → Prop
  | unit {Γ : List HTy} : IsValue (HTerm.unit (Γ := Γ))
  | pair {Γ : List HTy} {A B : HTy} {a : HTerm Γ A} {b : HTerm Γ B} :
      IsValue a → IsValue b → IsValue (a.pair b)
  | nil {Γ : List HTy} {A : HTy} : IsValue (HTerm.nil (Γ := Γ) (A := A))
  | cons {Γ : List HTy} {A : HTy} {a : HTerm Γ A} {l : HTerm Γ (.list A)} :
      IsValue a → IsValue l → IsValue (a.cons l)
  | inl {Γ : List HTy} {A B : HTy} {a : HTerm Γ A} :
      IsValue a → IsValue (HTerm.app (HTerm.atom (HAtom.inl A B)) a)
  | inr {Γ : List HTy} {A B : HTy} {b : HTerm Γ B} :
      IsValue b → IsValue (HTerm.app (HTerm.atom (HAtom.inr A B)) b)

/-! ## Elementary facts about normal forms -/

lemma one_le_size {Γ : List HTy} {H : HTy} (t : HTerm Γ H) : 1 ≤ t.size := by
  cases t <;> simp only [size] <;> omega

lemma normal_var {Γ : List HTy} {A : HTy} (v : HVar Γ A) : (HTerm.var v).Normal := by
  intro t' h; cases h

lemma normal_atom {Γ : List HTy} {H : HTy} (a : HAtom H) :
    (HTerm.atom (Γ := Γ) a).Normal := by
  intro t' h; cases h

lemma Normal.appL {Γ : List HTy} {A B : HTy} {f : HTerm Γ (.arrow A B)} {x : HTerm Γ A}
    (h : (f.app x).Normal) : f.Normal := fun _ hs => h _ (HStep.appL x hs)

lemma Normal.appR {Γ : List HTy} {A B : HTy} {f : HTerm Γ (.arrow A B)} {x : HTerm Γ A}
    (h : (f.app x).Normal) : x.Normal := fun _ hs => h _ (HStep.appR f hs)

lemma Normal.pairL {Γ : List HTy} {A B : HTy} {a : HTerm Γ A} {b : HTerm Γ B}
    (h : (a.pair b).Normal) : a.Normal := fun _ hs => h _ (HStep.pairL b hs)

lemma Normal.pairR {Γ : List HTy} {A B : HTy} {a : HTerm Γ A} {b : HTerm Γ B}
    (h : (a.pair b).Normal) : b.Normal := fun _ hs => h _ (HStep.pairR a hs)

lemma Normal.consL {Γ : List HTy} {A : HTy} {a : HTerm Γ A} {l : HTerm Γ (.list A)}
    (h : (a.cons l).Normal) : a.Normal := fun _ hs => h _ (HStep.consL l hs)

lemma Normal.consR {Γ : List HTy} {A : HTy} {a : HTerm Γ A} {l : HTerm Γ (.list A)}
    (h : (a.cons l).Normal) : l.Normal := fun _ hs => h _ (HStep.consR a hs)

/-- An atomic function that is one of the two co-projections. -/
def _root_.Transducers.HAtom.IsCoproj : {H : HTy} → HAtom H → Prop
  | _, .inl _ _ => True
  | _, .inr _ _ => True
  | _, _ => False

/-- The term is a co-projection.  This is how the shape of a value that is an application is read
off below: the reduction rules are inverted through it rather than by a case distinction on the
type of the term, because the type of the rule for `mult` is `HTy.ofTy G`, which cannot be matched
against a type constructor. -/
def HeadCoproj : {Γ : List HTy} → {H : HTy} → HTerm Γ H → Prop
  | _, _, .atom a => a.IsCoproj
  | _, _, .var _ => False
  | _, _, .app _ _ => False
  | _, _, .lam _ => False
  | _, _, .unit => False
  | _, _, .pair _ _ => False
  | _, _, .nil => False
  | _, _, .cons _ _ => False

lemma normal_of_headCoproj {Γ : List HTy} {H : HTy} :
    (t : HTerm Γ H) → HeadCoproj t → t.Normal
  | .atom a, _ => normal_atom a
  | .var _, h => h.elim
  | .app _ _, h => h.elim
  | .lam _, h => h.elim
  | .unit, h => h.elim
  | .pair _ _, h => h.elim
  | .nil, h => h.elim
  | .cons _ _, h => h.elim

/-- A value that is an application has a co-projection at its head. -/
lemma IsValue.head_coproj {Γ : List HTy} {A B : HTy} {f : HTerm Γ (.arrow A B)} {x : HTerm Γ A}
    (hv : IsValue (f.app x)) : HeadCoproj f := by
  cases hv with
  | inl _ => trivial
  | inr _ => trivial

/-- The argument of a value that is an application is a value. -/
lemma IsValue.app_arg {Γ : List HTy} {A B : HTy} {f : HTerm Γ (.arrow A B)} {x : HTerm Γ A}
    (hv : IsValue (f.app x)) : IsValue x := by
  cases hv with
  | inl ha => exact ha
  | inr hb => exact hb

/-- No reduction rule applies to a value. -/
lemma _root_.Transducers.HStep.not_isValue : {Γ : List HTy} → {A : HTy} → {t t' : HTerm Γ A} → HStep t t' →
    ¬ IsValue t := by
  intro Γ A t t' h
  induction h with
  | beta _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | fst _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | snd _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | unconsNil => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | unconsCons _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | concat _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | splits _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | mult _ _ _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | map _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | eitherInl _ _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | eitherInr _ _ _ => intro hv; simpa [HeadCoproj, HAtom.IsCoproj] using hv.head_coproj
  | appL _ hs _ => exact fun hv => normal_of_headCoproj _ hv.head_coproj _ hs
  | appR _ _ ih => exact fun hv => ih hv.app_arg
  | lam _ _ => intro hv; cases hv
  | pairL _ _ ih => intro hv; cases hv with | pair ha _ => exact ih ha
  | pairR _ _ ih => intro hv; cases hv with | pair _ hb => exact ih hb
  | consL _ _ ih => intro hv; cases hv with | cons ha _ => exact ih ha
  | consR _ _ ih => intro hv; cases hv with | cons _ hl => exact ih hl

/-- A value is in normal form. -/
lemma IsValue.normal {Γ : List HTy} {A : HTy} {t : HTerm Γ A} (hv : IsValue t) : t.Normal :=
  fun _ hs => hs.not_isValue hv

/-- A value of list type is a list term whose entries are values. -/
lemma IsValue.listForm : {Γ : List HTy} → {A : HTy} → {t : HTerm Γ (.list A)} → IsValue t →
    ∃ l : List (HTerm Γ A), t = mkList l ∧ ∀ a ∈ l, IsValue a
  | _, _, _, .nil => ⟨[], rfl, by simp⟩
  | _, _, _, .cons (a := a) ha hl => by
      obtain ⟨l, rfl, hall⟩ := hl.listForm
      refine ⟨a :: l, rfl, ?_⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hall _ hb

/-- A closed value whose type is arrow-free is the term that represents its own semantics. -/
lemma IsValue.eq_ofValue : ∀ (G : Ty) (t : HTerm [] (HTy.ofTy G)), IsValue t →
    t = ofValue G (t.eval .nil) := by
  intro G
  induction G with
  | one =>
      intro t hv
      cases hv
      rfl
  | prod A B ihA ihB =>
      intro t hv
      cases hv with
      | pair ha hb =>
          show _ = HTerm.pair _ _
          simp only [eval_pair]
          rw [← ihA _ ha, ← ihB _ hb]
  | sum A B ihA ihB =>
      intro t hv
      cases hv with
      | inl ha =>
          show _ = HTerm.app _ _
          rw [← ihA _ ha]
      | inr hb =>
          show _ = HTerm.app _ _
          rw [← ihB _ hb]
  | list A ihA =>
      intro t hv
      obtain ⟨l, rfl, hall⟩ := hv.listForm
      show _ = mkList _
      rw [eval_mkList, List.map_map]
      have h : l.map (ofValue A ∘ fun a => a.eval HEnv.nil) = l := by
        refine (List.map_congr_left ?_).trans (List.map_id l)
        intro a ha
        exact (ihA a (hall a ha)).symm
      rw [h]

/-! ## The shapes of closed terms in normal form -/

/-- **The inspection of shapes behind Lemma `lem:normal-forms-of-arrow-free-terms`**: the possible
shapes of a closed term of the reduced language that is in normal form.  It is a value (the first
four constructors, which are hereditary), an abstraction, or an atomic function applied to fewer
arguments than its reduction rule requires; the last two possibilities have arrow type. -/
inductive Shape : {H : HTy} → HTerm [] H → Prop
  | unit : Shape HTerm.unit
  | pair {A B : HTy} {a : HTerm [] A} {b : HTerm [] B} : Shape a → Shape b → Shape (a.pair b)
  | nil {A : HTy} : Shape (HTerm.nil (Γ := []) (A := A))
  | cons {A : HTy} {a : HTerm [] A} {l : HTerm [] (.list A)} :
      Shape a → Shape l → Shape (a.cons l)
  | lam {A B : HTy} (b : HTerm [A] B) : Shape (HTerm.lam b)
  | atomFst (A B : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.fst A B))
  | atomSnd (A B : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.snd A B))
  | atomInl (A B : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.inl A B))
  | atomInr (A B : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.inr A B))
  | atomUncons (A : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.uncons A))
  | atomConcat (A : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.concat A))
  | atomSplits (A : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.splits A))
  | atomMult (G : Ty) (grp : Group G.Elt) (hfin : Finite G.Elt) :
      Shape (HTerm.atom (Γ := []) (HAtom.mult G grp hfin))
  | atomMap (A B : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.map A B))
  | atomEither (A B C : HTy) : Shape (HTerm.atom (Γ := []) (HAtom.either A B C))
  | inlApp {A B : HTy} {a : HTerm [] A} :
      Shape a → Shape (HTerm.app (HTerm.atom (HAtom.inl A B)) a)
  | inrApp {A B : HTy} {b : HTerm [] B} :
      Shape b → Shape (HTerm.app (HTerm.atom (HAtom.inr A B)) b)
  | mapApp {A B : HTy} (f : HTerm [] (.arrow A B)) :
      Shape (HTerm.app (HTerm.atom (HAtom.map A B)) f)
  | eitherApp1 {A B C : HTy} (f : HTerm [] (.arrow A C)) :
      Shape (HTerm.app (HTerm.atom (HAtom.either A B C)) f)
  | eitherApp2 {A B C : HTy} (f : HTerm [] (.arrow A C)) (g : HTerm [] (.arrow B C)) :
      Shape (HTerm.app (HTerm.app (HTerm.atom (HAtom.either A B C)) f) g)

/-- A term of list type with a shape is a list term whose entries have shapes. -/
lemma Shape.listForm : {A : HTy} → {t : HTerm [] (.list A)} → Shape t →
    ∃ l : List (HTerm [] A), t = mkList l ∧ ∀ a ∈ l, Shape a
  | _, _, .nil => ⟨[], rfl, by simp⟩
  | _, _, .cons (a := a) ha hl => by
      obtain ⟨l, rfl, hall⟩ := hl.listForm
      refine ⟨a :: l, rfl, ?_⟩
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact hall _ hb

/-- A term with a shape whose type is arrow-free is a value. -/
lemma Shape.isValue : {H : HTy} → {t : HTerm [] H} → Shape t → H.ArrowFree → IsValue t
  | _, _, .unit, _ => .unit
  | _, _, .pair ha hb, h => .pair (ha.isValue h.1) (hb.isValue h.2)
  | _, _, .nil, _ => .nil
  | _, _, .cons ha hl, h => .cons (ha.isValue h) (hl.isValue h)
  | _, _, .lam _, h => h.elim
  | _, _, .atomFst _ _, h => h.elim
  | _, _, .atomSnd _ _, h => h.elim
  | _, _, .atomInl _ _, h => h.elim
  | _, _, .atomInr _ _, h => h.elim
  | _, _, .atomUncons _, h => h.elim
  | _, _, .atomConcat _, h => h.elim
  | _, _, .atomSplits _, h => h.elim
  | _, _, .atomMult _ _ _, h => h.elim
  | _, _, .atomMap _ _, h => h.elim
  | _, _, .atomEither _ _ _, h => h.elim
  | _, _, .inlApp ha, h => .inl (ha.isValue h.1)
  | _, _, .inrApp hb, h => .inr (hb.isValue h.2)
  | _, _, .mapApp _, h => h.elim
  | _, _, .eitherApp1 _, h => h.elim
  | _, _, .eitherApp2 _ _, h => h.elim

/-- A list of list terms is the image of a list of lists. -/
lemma exists_map_mkList {A : HTy} : ∀ (l : List (HTerm [] (.list A))),
    (∀ a ∈ l, ∃ L : List (HTerm [] A), a = mkList L) →
    ∃ L : List (List (HTerm [] A)), l = L.map mkList
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
      obtain ⟨L₀, rfl⟩ := h a (List.mem_cons_self ..)
      obtain ⟨L, hL⟩ := exists_map_mkList l (fun b hb => h b (List.mem_cons_of_mem _ hb))
      exact ⟨L₀ :: L, by rw [List.map_cons, ← hL]⟩

/-- **The inspection of shapes**: every closed term of the reduced language that is in normal form
has one of the shapes of `Transducers.HTerm.Shape`. -/
theorem shape_of_normal : ∀ (n : ℕ) {H : HTy} (t : HTerm [] H), t.size ≤ n → t.Small →
    t.Normal → Shape t := by
  intro n
  induction n with
  | zero =>
      intro H t hsz
      exact absurd (one_le_size t) (by omega)
  | succ n ih =>
      intro H t hsz hsm hn
      cases t with
      | var v => cases v
      | unit => exact .unit
      | nil => exact .nil
      | lam b => exact .lam b
      | pair a b =>
          have h1 : a.size ≤ n := by simp only [size] at hsz; omega
          have h2 : b.size ≤ n := by simp only [size] at hsz; omega
          exact .pair (ih a h1 hsm.1 hn.pairL) (ih b h2 hsm.2 hn.pairR)
      | cons a l =>
          have h1 : a.size ≤ n := by simp only [size] at hsz; omega
          have h2 : l.size ≤ n := by simp only [size] at hsz; omega
          exact .cons (ih a h1 hsm.1 hn.consL) (ih l h2 hsm.2 hn.consR)
      | atom a =>
          cases a with
          | fst A B => exact .atomFst A B
          | snd A B => exact .atomSnd A B
          | inl A B => exact .atomInl A B
          | inr A B => exact .atomInr A B
          | uncons A => exact .atomUncons A
          | concat A => exact .atomConcat A
          | splits A => exact .atomSplits A
          | mult G grp hfin => exact .atomMult G grp hfin
          | map A B => exact .atomMap A B
          | either A B C => exact .atomEither A B C
          | _ => exact hsm.elim
      | app f x =>
          have hf : f.size ≤ n := by simp only [size] at hsz; omega
          have hx : x.size ≤ n := by simp only [size] at hsz; omega
          have hsx : Shape x := ih x hx hsm.2 hn.appR
          have hsf : Shape f := ih f hf hsm.1 hn.appL
          cases hsf with
          | lam b => exact absurd (HStep.beta b x) (hn _)
          | atomInl A B => exact .inlApp hsx
          | atomInr A B => exact .inrApp hsx
          | atomMap A B => exact .mapApp x
          | atomEither A B C => exact .eitherApp1 x
          | eitherApp1 f' => exact .eitherApp2 f' x
          | atomFst A B =>
              cases hsx with
              | pair ha hb => exact absurd (HStep.fst _ _) (hn _)
          | atomSnd A B =>
              cases hsx with
              | pair ha hb => exact absurd (HStep.snd _ _) (hn _)
          | atomUncons A =>
              cases hsx with
              | nil => exact absurd HStep.unconsNil (hn _)
              | cons ha hl => exact absurd (HStep.unconsCons _ _) (hn _)
          | atomSplits A =>
              obtain ⟨l, rfl, _⟩ := hsx.listForm
              exact absurd (HStep.splits l) (hn _)
          | atomConcat A =>
              obtain ⟨l, rfl, hall⟩ := hsx.listForm
              obtain ⟨L, rfl⟩ := exists_map_mkList l
                (fun a ha => let ⟨L', hL', _⟩ := (hall a ha).listForm; ⟨L', hL'⟩)
              exact absurd (HStep.concat L) (hn _)
          | atomMult G grp hfin =>
              obtain ⟨l, rfl, hall⟩ := hsx.listForm
              have hval : ∀ a ∈ l, IsValue a := fun a ha =>
                (hall a ha).isValue (HTy.arrowFree_ofTy G)
              have hrep : (l.map (fun a => a.eval HEnv.nil)).map (ofValue G) = l := by
                rw [List.map_map]
                refine (List.map_congr_left ?_).trans (List.map_id l)
                intro a ha
                exact (IsValue.eq_ofValue G a (hval a ha)).symm
              have := HStep.mult (Γ := []) G grp hfin (l.map (fun a => a.eval HEnv.nil))
              rw [hrep] at this
              exact absurd this (hn _)
          | mapApp f' =>
              obtain ⟨l, rfl, _⟩ := hsx.listForm
              exact absurd (HStep.map f' l) (hn _)
          | eitherApp2 f' g' =>
              cases hsx with
              | inlApp ha => exact absurd (HStep.eitherInl _ _ _) (hn _)
              | inrApp hb => exact absurd (HStep.eitherInr _ _ _) (hn _)

end HTerm

/-- **Lemma `lem:normal-forms-of-arrow-free-terms`.**  A closed term whose type is arrow-free is in
normal form if and only if it is built using the value constructors `1`, `(a,b)`, `[a₁,…,aₙ]`,
`left a` and `right b`.

As in the whole of Section *Expressive completeness*, the atomic functions are the reduced set of
Lemma `lem:fewer-atomic`, which is the hypothesis `t.Small`; the statement is false without it,
since an atomic function with no reduction rule, such as `diag`, gives a closed normal term of
product type that is not a pair. -/
theorem normal_iff_isValue {H : HTy} (hH : H.ArrowFree) (t : HTerm [] H) (hsm : t.Small) :
    t.Normal ↔ t.IsValue :=
  ⟨fun hn => (HTerm.shape_of_normal t.size t (le_refl _) hsm hn).isValue hH,
    fun hv => hv.normal⟩

end Transducers
