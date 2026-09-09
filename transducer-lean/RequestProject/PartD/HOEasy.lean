/-
Part D, Section *A functional programming language*: the easy direction of Theorem
`thm:higher-order-terms`.

The higher-order polyregular terms of Definition `def:higher-order-terms` were designed as an
extension of the polyregular terms of Definition `def:polyregular-terms`: the atomic functions are
the same, and the four combinators are definable, composition and the two functoriality
combinators for products and co-products by abstraction, and the functoriality combinator for
lists by the atomic function `map`.  `Transducers.HTerm.ofPolyTerm` is that translation, and
`Transducers.HTerm.ofPolyTerm_eval` says that it preserves the semantics.
-/
import RequestProject.PartD.HOSyntax

namespace Transducers

namespace HTerm

/-- **Every polyregular term is a higher-order polyregular term.** -/
def ofPolyTerm : {A B : Ty} → PolyTerm A B → (Γ : List HTy) →
    HTerm Γ (.arrow (HTy.ofTy A) (HTy.ofTy B))
  | _, _, .id A, _ => .atom (.idA (HTy.ofTy A))
  | _, _, .fst A B, _ => .atom (.fst (HTy.ofTy A) (HTy.ofTy B))
  | _, _, .snd A B, _ => .atom (.snd (HTy.ofTy A) (HTy.ofTy B))
  | _, _, .inl A B, _ => .atom (.inl (HTy.ofTy A) (HTy.ofTy B))
  | _, _, .inr A B, _ => .atom (.inr (HTy.ofTy A) (HTy.ofTy B))
  | _, _, .diag A, _ => .atom (.diag (HTy.ofTy A))
  | _, _, .codiag A, _ => .atom (.codiag (HTy.ofTy A))
  | _, _, .distr A B C, _ => .atom (.distr (HTy.ofTy A) (HTy.ofTy B) (HTy.ofTy C))
  | _, _, .cons A, _ => .atom (.consA (HTy.ofTy A))
  | _, _, .uncons A, _ => .atom (.uncons (HTy.ofTy A))
  | _, _, .reverse A, _ => .atom (.reverse (HTy.ofTy A))
  | _, _, .concat A, _ => .atom (.concat (HTy.ofTy A))
  | _, _, .split A B, _ => .atom (.blockSplit (HTy.ofTy A) (HTy.ofTy B))
  | _, _, .pref G grp hfin, _ => .atom (.pref G grp hfin)
  | _, _, .splits A, _ => .atom (.splits (HTy.ofTy A))
  | _, _, .comp s t, Γ =>
      .lam ((ofPolyTerm t (_ :: Γ)).app ((ofPolyTerm s (_ :: Γ)).app (.var .zero)))
  | _, _, .prodMap s t, Γ =>
      .lam (.pair
        ((ofPolyTerm s (_ :: Γ)).app ((HTerm.atom (.fst _ _)).app (.var .zero)))
        ((ofPolyTerm t (_ :: Γ)).app ((HTerm.atom (.snd _ _)).app (.var .zero))))
  | _, _, .sumMap s t, _ =>
      .lam
        ((((HTerm.atom (.either _ _ _)).app
            (.lam ((HTerm.atom (.inl _ _)).app ((ofPolyTerm s _).app (.var .zero))))).app
            (.lam ((HTerm.atom (.inr _ _)).app ((ofPolyTerm t _).app (.var .zero))))).app
          (.var .zero))
  | _, _, .map t, _ =>
      .lam
        (((HTerm.atom (.map _ _)).app (.lam ((ofPolyTerm t _).app (.var .zero)))).app
          (.var .zero))

/-- **The translation preserves the semantics.** -/
theorem ofPolyTerm_eval : ∀ {A B : Ty} (t : PolyTerm A B) {Γ : List HTy} (e : HEnv Γ),
    (ofPolyTerm t Γ).eval e = fun x => HTy.ofElt B (t.eval (HTy.toElt A x))
  | _, _, .id A, _, _ => by
      funext x
      exact (HTy.ofElt_toElt A x).symm
  | _, _, .fst A B, _, _ => by
      funext x
      show x.1 = HTy.ofElt A (HTy.toElt A x.1)
      rw [HTy.ofElt_toElt]
  | _, _, .snd A B, _, _ => by
      funext x
      show x.2 = HTy.ofElt B (HTy.toElt B x.2)
      rw [HTy.ofElt_toElt]
  | _, _, .inl A B, _, _ => by
      funext x
      show Sum.inl x = Sum.map (HTy.ofElt A) (HTy.ofElt B) (Sum.inl (HTy.toElt A x))
      rw [Sum.map_inl, HTy.ofElt_toElt]
  | _, _, .inr A B, _, _ => by
      funext x
      show Sum.inr x = Sum.map (HTy.ofElt A) (HTy.ofElt B) (Sum.inr (HTy.toElt B x))
      rw [Sum.map_inr, HTy.ofElt_toElt]
  | _, _, .diag A, _, _ => by
      funext x
      show (x, x) = (HTy.ofElt A (HTy.toElt A x), HTy.ofElt A (HTy.toElt A x))
      rw [HTy.ofElt_toElt]
  | _, _, .codiag A, _, _ => by
      funext x
      cases x with
      | inl a => show a = HTy.ofElt A (HTy.toElt A a); rw [HTy.ofElt_toElt]
      | inr a => show a = HTy.ofElt A (HTy.toElt A a); rw [HTy.ofElt_toElt]
  | _, _, .distr A B C, _, _ => by
      funext x
      obtain ⟨u, v⟩ := x
      cases v with
      | inl b =>
          show Sum.inl (u, b) = Sum.map _ _ (Sum.inl (HTy.toElt A u, HTy.toElt B b))
          show Sum.inl (u, b)
            = Sum.inl (HTy.ofElt A (HTy.toElt A u), HTy.ofElt B (HTy.toElt B b))
          rw [HTy.ofElt_toElt, HTy.ofElt_toElt]
      | inr c =>
          show Sum.inr (u, c) = Sum.map _ _ (Sum.inr (HTy.toElt A u, HTy.toElt C c))
          show Sum.inr (u, c)
            = Sum.inr (HTy.ofElt A (HTy.toElt A u), HTy.ofElt C (HTy.toElt C c))
          rw [HTy.ofElt_toElt, HTy.ofElt_toElt]
  | _, _, .cons A, _, _ => by
      funext x
      cases x with
      | inl u => rfl
      | inr p =>
          show p.1 :: p.2
            = (HTy.ofElt A (HTy.toElt A p.1)) :: (p.2.map (HTy.toElt A)).map (HTy.ofElt A)
          rw [HTy.ofElt_toElt, List.map_map,
            show ((HTy.ofElt A) ∘ (HTy.toElt A)) = id from funext (fun y => HTy.ofElt_toElt A y),
            List.map_id]
  | _, _, .uncons A, _, _ => by
      funext l
      cases l with
      | nil => rfl
      | cons a l =>
          show Sum.inr (a, l)
            = Sum.map (fun x => x)
                (fun p => (HTy.ofElt A p.1, p.2.map (HTy.ofElt A)))
                (Sum.inr (HTy.toElt A a, l.map (HTy.toElt A)))
          show Sum.inr (a, l)
            = Sum.inr (HTy.ofElt A (HTy.toElt A a), (l.map (HTy.toElt A)).map (HTy.ofElt A))
          rw [HTy.ofElt_toElt, List.map_map,
            show ((HTy.ofElt A) ∘ (HTy.toElt A)) = id from funext (fun y => HTy.ofElt_toElt A y),
            List.map_id]
  | _, _, .reverse A, _, _ => by
      funext l
      show l.reverse = ((l.map (HTy.toElt A)).reverse).map (HTy.ofElt A)
      rw [← List.map_reverse, List.map_map,
        show ((HTy.ofElt A) ∘ (HTy.toElt A)) = id from funext (fun y => HTy.ofElt_toElt A y),
        List.map_id]
  | _, _, .concat A, _, _ => by
      funext l
      show l.flatten = HTy.ofElt (.list A) ((HTy.toElt (.list (.list A)) l).flatten)
      have h : (HTy.toElt (.list (.list A)) l).flatten = HTy.toElt (.list A) l.flatten := by
        show ((l.map (fun u => HTy.toElt (.list A) u)).flatten) = (l.flatten).map (HTy.toElt A)
        rw [List.map_flatten]
        rfl
      rw [h, HTy.ofElt_toElt]
  | _, _, .split A B, _, _ => by
      funext l
      show splitList l
        = HTy.ofElt (.prod (.list A) (.list (.prod B (.list A))))
            (splitList (HTy.toElt (.list (.sum A B)) l))
      have h : splitList (HTy.toElt (.list (.sum A B)) l)
          = HTy.toElt (.prod (.list A) (.list (.prod B (.list A)))) (splitList l) := by
        show splitList (l.map (Sum.map (HTy.toElt A) (HTy.toElt B))) = _
        rw [splitList_map]
        rfl
      rw [h, HTy.ofElt_toElt]
  | _, _, .pref G grp hfin, _, _ => by
      funext l
      rfl
  | _, _, .splits A, _, _ => by
      funext l
      show splitsList l
        = HTy.ofElt (.list (.prod (.list A) (.list A))) (splitsList (HTy.toElt (.list A) l))
      have h : splitsList (HTy.toElt (.list A) l)
          = HTy.toElt (.list (.prod (.list A) (.list A))) (splitsList l) := by
        show splitsList (l.map (HTy.toElt A)) = _
        rw [splitsList_map]
        rfl
      rw [h, HTy.ofElt_toElt]
  | _, _, .comp s t, Γ, e => by
      funext x
      show ((ofPolyTerm t (_ :: Γ)).eval (.cons x e)) ((ofPolyTerm s (_ :: Γ)).eval (.cons x e) x)
        = _
      rw [ofPolyTerm_eval s (.cons x e), ofPolyTerm_eval t (.cons x e)]
      show HTy.ofElt _ (t.eval (HTy.toElt _ (HTy.ofElt _ (s.eval (HTy.toElt _ x))))) = _
      rw [HTy.toElt_ofElt]
      rfl
  | _, _, .prodMap s t, Γ, e => by
      funext x
      show ((ofPolyTerm s (_ :: Γ)).eval (.cons x e) x.1,
        (ofPolyTerm t (_ :: Γ)).eval (.cons x e) x.2) = _
      rw [ofPolyTerm_eval s (.cons x e), ofPolyTerm_eval t (.cons x e)]
      rfl
  | _, _, .sumMap s t, Γ, e => by
      funext x
      cases x with
      | inl a =>
          show Sum.inl (((ofPolyTerm s _).eval _) a) = _
          rw [ofPolyTerm_eval s]
          rfl
      | inr b =>
          show Sum.inr (((ofPolyTerm t _).eval _) b) = _
          rw [ofPolyTerm_eval t]
          rfl
  | _, _, .map t, Γ, e => by
      funext l
      simp only [ofPolyTerm, HTerm.eval_lam, HTerm.eval_app, HTerm.eval_atom, HTerm.eval_var,
        HAtom.sem, ofPolyTerm_eval t]
      show l.map (fun x => HTy.ofElt _ (t.eval (HTy.toElt _ x)))
        = ((l.map (HTy.toElt _)).map t.eval).map (HTy.ofElt _)
      rw [List.map_map, List.map_map]
      rfl

end HTerm

/-- **The easy direction of Theorem `thm:higher-order-terms`.**  Every function that is defined by
a polyregular term is defined by a higher-order term. -/
theorem isHigherOrderTermFun_of_isPolyregularTermFun {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsPolyregularTermFun f) : IsHigherOrderTermFun f := by
  obtain ⟨t, ht⟩ := h
  refine ⟨HTerm.ofPolyTerm t [], fun a => ?_⟩
  rw [HTerm.ofPolyTerm_eval t]
  show HTy.toElt B (HTy.ofElt B (t.eval (HTy.toElt A (HTy.ofElt A a)))) = f a
  rw [HTy.toElt_ofElt, HTy.toElt_ofElt, ht]

end Transducers
