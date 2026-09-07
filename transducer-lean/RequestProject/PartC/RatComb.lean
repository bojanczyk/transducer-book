/-
The combinators of Theorem `thm:rational-terms` preserve rationality under string representation.
Part of the easy direction of that theorem, from Section *Combinators* of *Transducers*
(M. Bojańczyk).

Composition is `Transducers.IsRationalUnderRepr.comp`, in `RatTerms.lean`.  This file has the three
functoriality combinators.

* *Map* is the map lifting of Part A applied to the marking of `CombMark.lean`, exactly as in the
  regular case (`Transducers.Comb.IsRegularUnderRepr.mapList`); the map lifting of a rational
  function is rational.

* *`f₁ + f₂`* looks at the first letter of the input, which says which summand the input comes
  from, and runs the corresponding function on the rest; both the test and the removal of the
  first letter are rational.

* *`f₁ × f₂`* is the one that has to be done differently.  In the regular case it is a pairing --
  the first component of the output is a function of the whole input, and so is the second -- and
  pairing is not available for rational terms.  Instead the input `(a,b)` is cut into the two
  *blocks* `L a` and `R b` by a machine of `CombMach.lean`, which is a one-pass left-to-right
  transformation, and the map lifting then applies to each block the function that runs `f₁` or
  `f₂` according to the tag `L` or `R` that the block carries.  Putting the brackets and the comma
  back is a homomorphism between two constants.  The same machine, `Transducers.RatComb.pairMarkMach`,
  is used again in `RatRepr.lean` to invert the representation of a product.
-/
import RequestProject.PartC.RatAtomA
import RequestProject.PartC.CombMark

namespace Transducers
namespace RatComb

open Comb

/-! ## Unmarking into a pair -/

/-- Unmarking into a pair: the brackets of a product are put back and the separator becomes the
comma. -/
def unmarkPair (v : List (Option Sym8)) : List Sym8 :=
  Sym8.lpar :: (v.map unopt ++ [Sym8.rpar])

lemma isRationalFun_unmarkPair : IsRationalFun unmarkPair :=
  isRationalFun_comp' (isRationalFun_map unopt)
    (isRationalFun_comp' (isRationalFun_appendConst [Sym8.rpar]) (isRationalFun_cons Sym8.lpar)
      (fun _ => rfl)) (fun _ => rfl)

lemma isRationalFun_unmark : IsRationalFun unmark :=
  isRationalFun_comp' (isRationalFun_map unopt)
    (isRationalFun_comp' (isRationalFun_appendConst [Sym8.rbrack]) (isRationalFun_cons Sym8.lbrack)
      (fun _ => rfl)) (fun _ => rfl)

/-! ## The machine that cuts a pair into its two tagged components -/

/-- The machine that turns the representation of a pair into the two blocks `L a` and `R b`,
separated by the marker. -/
def pairMarkMach : Mach PMode (Option Sym8) where
  step := fun m e c => match m with
    | .start => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .inB else .inA
    | .inB => if e = 1 ∧ c = Sym8.rpar then .stop else .inB
    | .stop => .stop
  out := fun m e c => match m with
    | .start => [some Sym8.left]
    | .inA => if e = 1 ∧ c = Sym8.comma then [none, some Sym8.right] else [some c]
    | .inB => if e = 1 ∧ c = Sym8.rpar then [] else [some c]
    | .stop => []
  fin := fun _ _ => []

@[simp] lemma pairMarkMach_step_start (e : ℕ) (c : Sym8) : pairMarkMach.step .start e c = .inA :=
  rfl
@[simp] lemma pairMarkMach_out_start (e : ℕ) (c : Sym8) :
    pairMarkMach.out .start e c = [some Sym8.left] := rfl
@[simp] lemma pairMarkMach_step_inA_comma : pairMarkMach.step .inA 1 Sym8.comma = .inB := rfl
@[simp] lemma pairMarkMach_out_inA_comma :
    pairMarkMach.out .inA 1 Sym8.comma = [none, some Sym8.right] := rfl
@[simp] lemma pairMarkMach_step_inB_rpar : pairMarkMach.step .inB 1 Sym8.rpar = .stop := rfl
@[simp] lemma pairMarkMach_out_inB_rpar : pairMarkMach.out .inB 1 Sym8.rpar = [] := rfl
@[simp] lemma pairMarkMach_fin (m : PMode) (e : ℕ) : pairMarkMach.fin m e = [] := rfl

private lemma flatten_map_some' (w : List Sym8) :
    (w.map (fun c => [(some c : Option Sym8)])).flatten = w.map some := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]

section PairMark

variable (A B : Ty)

private lemma pairMark_copies_inA : pairMarkMach.Copies .inA (d1 A B).1 (fun c => [some c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [pairMarkMach, hne, if_false], by simp only [pairMarkMach, hne, if_false]⟩

private lemma pairMark_copies_inB : pairMarkMach.Copies .inB (d1 A B).1 (fun c => [some c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [pairMarkMach, hne, if_false], by simp only [pairMarkMach, hne, if_false]⟩

/-- **The machine cuts the representation of a pair into its two tagged components.** -/
theorem pairMarkMach_run (a : A.Elt) (b : B.Elt) :
    pairMarkMach.run ((Ty.prod A B).height) .start ((Ty.prod A B).repr (a, b))
      = optBlocks [Sym8.left :: A.repr a, Sym8.right :: B.repr b] := by
  show pairMarkMach.runFrom ((Ty.prod A B).height) (PMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: (B.repr b ++ [Sym8.rpar]))) = _
  rw [Mach.runFrom_cons]
  simp only [pairMarkMach_out_start, pairMarkMach_step_start, dstep_zero_lpar]
  rw [Mach.runFrom_repr _ _ _ (fun c => [some c]) A a (d1 A B) _ (capA A B)
      (pairMark_copies_inA A B), flatten_map_some', Mach.runFrom_cons]
  simp only [d1_val, pairMarkMach_out_inA_comma, pairMarkMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0)]
  rw [Mach.runFrom_repr _ _ _ (fun c => [some c]) B b (d1 A B) _ (capB A B)
      (pairMark_copies_inB A B), flatten_map_some', Mach.runFrom_cons]
  simp only [d1_val, pairMarkMach_out_inB_rpar, pairMarkMach_step_inB_rpar, List.nil_append]
  rw [Mach.runFrom_nil]
  simp [optBlocks]

end PairMark

/-! ## The functoriality combinator for products -/

open scoped Classical in
/-- **The functoriality combinator `f₁ × f₂` preserves rationality under string
representation.** -/
theorem IsRationalUnderRepr.prodMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsRationalUnderRepr f) (hg : IsRationalUnderRepr g) :
    IsRationalUnderRepr (A := Ty.prod A₁ A₂) (B := Ty.prod B₁ B₂) (fun p => (f p.1, g p.2)) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  set h : List Sym8 → List Sym8 := fun w =>
    if w ∈ emptyLang Sym8 then []
    else if w ∈ headLang Sym8.left then f' w.tail else g' w.tail with hhdef
  have hhrat : IsRationalFun h :=
    isRationalFun_ite_lang (emptyLang_isRegular Sym8) (isRationalFun_const [])
      (isRationalFun_ite_lang (headLang_isRegular Sym8.left)
        (isRationalFun_comp isRationalFun_tail hf')
        (isRationalFun_comp isRationalFun_tail hg'))
  have hhnil : h [] = [] := by rw [hhdef]; exact if_pos rfl
  have hhleft : ∀ a : A₁.Elt, h (Sym8.left :: A₁.repr a) = B₁.repr (f a) := by
    intro a
    have h1 : (Sym8.left :: A₁.repr a) ∉ emptyLang Sym8 := by
      show ¬ (Sym8.left :: A₁.repr a = []); simp
    have h2 : (Sym8.left :: A₁.repr a) ∈ headLang Sym8.left := rfl
    rw [hhdef]
    dsimp only
    rw [if_neg h1, if_pos h2]
    exact hfe a
  have hhright : ∀ b : A₂.Elt, h (Sym8.right :: A₂.repr b) = B₂.repr (g b) := by
    intro b
    have h1 : (Sym8.right :: A₂.repr b) ∉ emptyLang Sym8 := by
      show ¬ (Sym8.right :: A₂.repr b = []); simp
    have h2 : (Sym8.right :: A₂.repr b) ∉ headLang Sym8.left := by
      show ¬ ((Sym8.right :: A₂.repr b).head? = some Sym8.left); simp
    rw [hhdef]
    dsimp only
    rw [if_neg h1, if_neg h2]
    exact hge b
  refine ⟨fun w => unmarkPair (mapLift h
      (pairMarkMach.run ((Ty.prod A₁ A₂).height) .start w)), ?_, ?_⟩
  · exact isRationalFun_comp' (pairMarkMach.isRationalFun_run _ _)
      (isRationalFun_comp' (isRationalFun_mapLift hhrat) isRationalFun_unmarkPair
        (fun _ => rfl)) (fun _ => rfl)
  · rintro ⟨a, b⟩
    dsimp only
    rw [pairMarkMach_run, mapLift_optBlocks hhnil]
    simp only [List.map_cons, List.map_nil]
    rw [hhleft a, hhright b, unmarkPair, map_unopt_optBlocks]
    show _ = Sym8.lpar :: (B₁.repr (f a) ++ Sym8.comma :: (B₂.repr (g b) ++ [Sym8.rpar]))
    rw [show joinSep [B₁.repr (f a), B₂.repr (g b)]
        = B₁.repr (f a) ++ Sym8.comma :: joinSep [B₂.repr (g b)] from rfl, joinSep_singleton]
    simp

/-! ## The functoriality combinator for co-products -/

open scoped Classical in
/-- **The functoriality combinator `f₁ + f₂` preserves rationality under string
representation.** -/
theorem IsRationalUnderRepr.sumMap {A₁ A₂ B₁ B₂ : Ty} {f : A₁.Elt → B₁.Elt} {g : A₂.Elt → B₂.Elt}
    (hf : IsRationalUnderRepr f) (hg : IsRationalUnderRepr g) :
    IsRationalUnderRepr (A := Ty.sum A₁ A₂) (B := Ty.sum B₁ B₂) (fun x => Sum.map f g x) := by
  obtain ⟨f', hf', hfe⟩ := hf
  obtain ⟨g', hg', hge⟩ := hg
  refine ⟨fun w => if w ∈ headLang Sym8.left then Sym8.left :: f' w.tail
      else Sym8.right :: g' w.tail, ?_, ?_⟩
  · exact isRationalFun_ite_lang (headLang_isRegular Sym8.left)
      (isRationalFun_comp (isRationalFun_comp isRationalFun_tail hf')
        (isRationalFun_cons Sym8.left))
      (isRationalFun_comp (isRationalFun_comp isRationalFun_tail hg')
        (isRationalFun_cons Sym8.right))
  · rintro (a | b)
    · have hmem : (Ty.sum A₁ A₂).repr (Sum.inl a) ∈ headLang Sym8.left := rfl
      show (if _ ∈ headLang Sym8.left then _ else _) = _
      rw [if_pos hmem, Ty.repr_inl]
      show Sym8.left :: f' (A₁.repr a) = _
      rw [hfe a]
      rfl
    · have hmem : (Ty.sum A₁ A₂).repr (Sum.inr b) ∉ headLang Sym8.left := by
        show ¬ (((Ty.sum A₁ A₂).repr (Sum.inr b)).head? = some Sym8.left)
        rw [Ty.repr_inr]
        simp
      show (if _ ∈ headLang Sym8.left then _ else _) = _
      rw [if_neg hmem, Ty.repr_inr]
      show Sym8.right :: g' (A₂.repr b) = _
      rw [hge b]
      rfl

/-! ## The functoriality combinator for lists -/

open scoped Classical in
/-- **The functoriality combinator `f*` preserves rationality under string representation.** -/
theorem IsRationalUnderRepr.mapList {A B : Ty} {f : A.Elt → B.Elt} (hf : IsRationalUnderRepr f) :
    IsRationalUnderRepr (A := Ty.list A) (B := Ty.list B) (fun l => l.map f) := by
  obtain ⟨f', hf', hfe⟩ := hf
  set f'' : List Sym8 → List Sym8 :=
    fun w => if w ∈ emptyLang Sym8 then [] else f' w with hf''def
  have hf''rat : IsRationalFun f'' :=
    isRationalFun_ite_lang (emptyLang_isRegular Sym8) (isRationalFun_const []) hf'
  have hf''nil : f'' [] = [] := by rw [hf''def]; exact if_pos rfl
  have hf''repr : ∀ a : A.Elt, f'' (A.repr a) = B.repr (f a) := by
    intro a
    obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A a
    have hne : A.repr a ∉ emptyLang Sym8 := by
      show ¬ (A.repr a = [])
      rw [hcw]; simp
    rw [hf''def]
    dsimp only
    rw [if_neg hne]
    exact hfe a
  refine ⟨fun w => unmark (mapLift f'' (listMarkMach.run (listMarkN A) .start w)), ?_, fun l => ?_⟩
  · exact isRationalFun_comp' (listMarkMach.isRationalFun_run _ _)
      (isRationalFun_comp' (isRationalFun_mapLift hf''rat) isRationalFun_unmark
        (fun _ => rfl)) (fun _ => rfl)
  · dsimp only
    rw [listMarkMach_run, mapLift_optBlocks hf''nil, List.map_map]
    rw [show ((f'' ∘ A.repr) : A.Elt → List Sym8) = (B.repr ∘ f) from funext hf''repr,
      ← List.map_map]
    exact unmark_optBlocks B (l.map f)

end RatComb
end Transducers
