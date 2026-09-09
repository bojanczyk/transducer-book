/-
Part D: polyregular functions between types, under the string representation, and the fact that
the combinators of Definition `def:regular-terms` preserve polyregularity.

Definition `def:polyregular-functions` is about string-to-string functions;  Theorem
`thm:polyregular-terms` is about type-to-type functions, and compares them with the polyregular
functions "under string representation", exactly as Theorem `thm:regular-terms` does for the
regular functions.  The notion is `Transducers.IsPolyregularUnderRepr` below, the literal analogue
of `Transducers.IsRegularUnderRepr` of `RequestProject/PartC/CombTypes.lean`.

The rest of the file repeats, for the polyregular functions, the three proofs of
`RequestProject/PartC/CombCombinators.lean` -- pairing, co-pairing and map -- which is possible
because the closure properties they use are available for the polyregular functions too:
concatenation and case distinction over a regular language
(`RequestProject/PartD/PolySum.lean`), and the map lifting
(`RequestProject/PartD/PolyMapLift.lean`).
-/
import RequestProject.PartD.PolySum
import RequestProject.PartC.CombStatements

namespace Transducers

open Comb

/-! ## Polyregular under string representation -/

/-- **Polyregular under string representation.**  A type-to-type function is *polyregular under
string representation* if some polyregular string-to-string function over the eight-letter alphabet
maps the representation of `a` to the representation of `f a`.  Nothing is required of it on the
strings that represent no element.  This is Definition
`def:regular-functions-on-types-under-string-representation` with "regular" replaced by
"polyregular". -/
def IsPolyregularUnderRepr {A B : Ty} (f : A.Elt → B.Elt) : Prop :=
  ∃ f' : List Sym8 → List Sym8, IsPolyregular f' ∧ ∀ a : A.Elt, f' (A.repr a) = B.repr (f a)

lemma IsPolyregularUnderRepr.congr {A B : Ty} {f g : A.Elt → B.Elt}
    (h : IsPolyregularUnderRepr f) (hfg : ∀ a, f a = g a) : IsPolyregularUnderRepr g := by
  obtain ⟨f', hf', hfe⟩ := h
  exact ⟨f', hf', fun a => by rw [hfe a, hfg a]⟩

/-- A function that is regular under string representation is polyregular under string
representation. -/
lemma IsRegularUnderRepr.isPolyregularUnderRepr {A B : Ty} {f : A.Elt → B.Elt}
    (h : IsRegularUnderRepr f) : IsPolyregularUnderRepr f := by
  obtain ⟨f', hf', hfe⟩ := h
  exact ⟨f', IsPolyregular.of_regular hf', hfe⟩

/-- Polyregularity under string representation is preserved by composition. -/
lemma IsPolyregularUnderRepr.comp {A B C : Ty} {f : A.Elt → B.Elt} {g : B.Elt → C.Elt}
    (hf : IsPolyregularUnderRepr f) (hg : IsPolyregularUnderRepr g) :
    IsPolyregularUnderRepr (fun a => g (f a)) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => g' (f' w), hf'.comp' hg' (fun _ => rfl), fun a => ?_⟩
  show g' (f' (A.repr a)) = C.repr (g (f a))
  rw [hfe a, hge (f a)]

/-! ## Pairing -/

/-- **Pairing preserves polyregularity under string representation.** -/
theorem IsPolyregularUnderRepr.pair {A B C : Ty} {f : A.Elt → B.Elt} {g : A.Elt → C.Elt}
    (hf : IsPolyregularUnderRepr f) (hg : IsPolyregularUnderRepr g) :
    IsPolyregularUnderRepr (A := A) (B := Ty.prod B C) (fun a => (f a, g a)) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => Sym8.lpar :: (f' w ++ Sym8.comma :: (g' w ++ [Sym8.rpar])), ?_, fun a => ?_⟩
  · have hconst : ∀ c : List Sym8, IsPolyregular (fun _ : List Sym8 => c) := fun c =>
      IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_const c))
    have h : IsPolyregular (fun w : List Sym8 =>
        [Sym8.lpar] ++ (f' w ++ ([Sym8.comma] ++ (g' w ++ [Sym8.rpar])))) :=
      isPolyregular_concat (hconst _)
        (isPolyregular_concat hf'
          (isPolyregular_concat (hconst _)
            (isPolyregular_concat hg' (hconst _))))
    exact h.congr (fun w => rfl)
  · dsimp only
    rw [hfe a, hge a, Ty.repr_prod]

/-! ## Co-pairing -/

open scoped Classical in
/-- **Co-pairing preserves polyregularity under string representation.** -/
theorem IsPolyregularUnderRepr.copair {A B C : Ty} {f : A.Elt → C.Elt} {g : B.Elt → C.Elt}
    (hf : IsPolyregularUnderRepr f) (hg : IsPolyregularUnderRepr g) :
    IsPolyregularUnderRepr (A := Ty.sum A B) (B := C) (Sum.elim f g) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => if w ∈ headLang Sym8.left then f' w.tail else g' w.tail, ?_, fun x => ?_⟩
  · exact isPolyregular_cond
      ((IsPolyregular.of_regular isRegularFun_tail).comp' hf' (fun _ => rfl))
      ((IsPolyregular.of_regular isRegularFun_tail).comp' hg' (fun _ => rfl))
      (headLang_isRegular _)
  · cases x with
    | inl a =>
        dsimp only
        have hmem : (Ty.sum A B).repr (Sum.inl a) ∈ headLang Sym8.left := by
          show ((Ty.sum A B).repr (Sum.inl a)).head? = some Sym8.left
          rw [Ty.repr_inl]
          rfl
        rw [if_pos hmem, Ty.repr_inl]
        exact hfe a
    | inr b =>
        dsimp only
        have hmem : (Ty.sum A B).repr (Sum.inr b) ∉ headLang Sym8.left := by
          show ¬ (((Ty.sum A B).repr (Sum.inr b)).head? = some Sym8.left)
          rw [Ty.repr_inr]
          simp
        rw [if_neg hmem, Ty.repr_inr]
        exact hge b

/-! ## Map -/

open scoped Classical in
/-- **Map preserves polyregularity under string representation.** -/
theorem IsPolyregularUnderRepr.mapList {A B : Ty} {f : A.Elt → B.Elt}
    (hf : IsPolyregularUnderRepr f) :
    IsPolyregularUnderRepr (A := Ty.list A) (B := Ty.list B) (fun l => l.map f) := by
  obtain ⟨f', hf', hfe⟩ := hf
  set f'' : List Sym8 → List Sym8 :=
    fun w => if w ∈ emptyLang Sym8 then [] else f' w with hf''def
  have hf''reg : IsPolyregular f'' :=
    isPolyregular_cond
      (IsPolyregular.of_regular (IsRegularFun.of_rational (isRationalFun_const []))) hf'
      (emptyLang_isRegular Sym8)
  have hf''nil : f'' [] = [] := by
    rw [hf''def]
    exact if_pos rfl
  have hf''repr : ∀ a : A.Elt, f'' (A.repr a) = B.repr (f a) := by
    intro a
    obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A a
    have hne : A.repr a ∉ emptyLang Sym8 := by
      show ¬ (A.repr a = [])
      rw [hcw]
      simp
    rw [hf''def]
    dsimp only
    rw [if_neg hne]
    exact hfe a
  refine ⟨fun w => unmark (mapLift f'' (listMarkMach.run (listMarkN A) .start w)), ?_, fun l => ?_⟩
  · exact ((IsPolyregular.of_regular (isRegularFun_listMarkRun A)).comp'
      (isPolyregular_mapLift hf''reg) (fun _ => rfl)).comp'
      (IsPolyregular.of_regular isRegularFun_unmark) (fun _ => rfl)
  · dsimp only
    rw [listMarkMach_run, mapLift_optBlocks hf''nil, List.map_map]
    rw [show ((f'' ∘ A.repr) : A.Elt → List Sym8) = (B.repr ∘ f) from funext hf''repr,
      ← List.map_map]
    exact unmark_optBlocks B (l.map f)

/-! ## The two functoriality combinators -/

/-- **The functoriality combinator `f₁ × f₂` preserves polyregularity under string
representation.** -/
theorem IsPolyregularUnderRepr.prodMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt}
    {g : A₂.Elt → B₂.Elt} (hf : IsPolyregularUnderRepr f) (hg : IsPolyregularUnderRepr g) :
    IsPolyregularUnderRepr (A := Ty.prod A₁ A₂) (B := Ty.prod B₁ B₂) (fun p => (f p.1, g p.2)) :=
  IsPolyregularUnderRepr.pair
    ((isRegularUnderRepr_fst A₁ A₂).isPolyregularUnderRepr.comp hf)
    ((isRegularUnderRepr_snd A₁ A₂).isPolyregularUnderRepr.comp hg)

/-- **The functoriality combinator `f₁ + f₂` preserves polyregularity under string
representation.** -/
theorem IsPolyregularUnderRepr.sumMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt}
    {g : A₂.Elt → B₂.Elt} (hf : IsPolyregularUnderRepr f) (hg : IsPolyregularUnderRepr g) :
    IsPolyregularUnderRepr (A := Ty.sum A₁ A₂) (B := Ty.sum B₁ B₂) (fun x => Sum.map f g x) :=
  (IsPolyregularUnderRepr.copair (hf.comp (isRegularUnderRepr_inl B₁ B₂).isPolyregularUnderRepr)
    (hg.comp (isRegularUnderRepr_inr B₁ B₂).isPolyregularUnderRepr)).congr
    (fun x => by cases x <;> rfl)

end Transducers
