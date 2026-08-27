/-
An exercise of the chapter on rational functions (`rational-functions.tex`) of
*Transducers* (M. Bojańczyk): injectivity of a rational function.
-/
import RequestProject.Exercises.PartBC

/-!
# A rational function is injective exactly when it has a rational left inverse

Exercise `exer:rational-injectivity-decidable` asks for a procedure deciding whether a given
rational function is injective.  The solution proceeds in two steps.  The first one is a
mathematical statement, and it is what is proved here
(`exists_rationalFun_inverse_of_injective`, `rationalFun_injective_iff_exists_inverse`): the
inverse relation of `f` is rational, it becomes total once it is extended with a default output
on the complement of the range of `f` — a regular language — so the Uniformisation Lemma
`lem:uniformisation` gives a rational function `g` inside it, and `f` is injective exactly when
that `g` inverts `f` on the left.  The second step is the decision procedure itself: apply
Theorem `thm:equivalence-rational-functions` to `g ∘ f` and the identity.  That step is *not*
formalised.  In this project a decision procedure for rational functions is a statement about
*codes* of automata (`Transducers.RelCode`), and the `g` above is produced by the Uniformisation
Lemma in the form `Transducers.exists_rationalFun_of_total_rel`, which asserts the existence of
a rational function and not of a code for one; so no code for `g` can be computed from a code
for `f` with what the project has.  This is recorded in `EXERCISES.md`, where the exercise
remains listed as not formalised.

The auxiliary fact that the first step needs and that the project did not have is that rational
relations are closed under union (`isRationalRel_union`), which is proved here by the disjoint
union of two nfas with output (`sumAut`).
-/

namespace Transducers.Exercises

open LabAut NFAO

/-! ### Rational relations are closed under union -/

section Union

variable {A B Q₁ Q₂ : Type}

/-- The disjoint union of two nfas with output: it runs one of the two automata, chosen by the
initial state. -/
def sumAut (M₁ : NFAO A B Q₁) (M₂ : NFAO A B Q₂) : NFAO A B (Q₁ ⊕ Q₂) where
  init := Sum.inl '' M₁.init ∪ Sum.inr '' M₂.init
  final := Sum.inl '' M₁.final ∪ Sum.inr '' M₂.final
  δ := (fun t : Q₁ × List A × List B × Q₁ => (Sum.inl t.1, t.2.1, t.2.2.1, Sum.inl t.2.2.2)) '' M₁.δ
     ∪ (fun t : Q₂ × List A × List B × Q₂ => (Sum.inr t.1, t.2.1, t.2.2.1, Sum.inr t.2.2.2)) '' M₂.δ
  δ_finite := (M₁.δ_finite.image _).union (M₂.δ_finite.image _)

variable {M₁ : NFAO A B Q₁} {M₂ : NFAO A B Q₂}

lemma sumAut_relFrom_left {q p : Q₁} {w : List A} {v : List B} (h : M₁.relFrom q w v p) :
    (sumAut M₁ M₂).relFrom (Sum.inl q) w v (Sum.inl p) := by
  refine NFAO.relFrom_induction (M := M₁)
    (motive := fun q w v => (sumAut M₁ M₂).relFrom (Sum.inl q) w v (Sum.inl p))
    (NFAO.relFrom_nil _ _) (fun q q' u x w v ht _ ih => ?_) h
  exact NFAO.relFrom_step (Or.inl ⟨(q, u, x, q'), ht, rfl⟩) ih

lemma sumAut_relFrom_right {q p : Q₂} {w : List A} {v : List B} (h : M₂.relFrom q w v p) :
    (sumAut M₁ M₂).relFrom (Sum.inr q) w v (Sum.inr p) := by
  refine NFAO.relFrom_induction (M := M₂)
    (motive := fun q w v => (sumAut M₁ M₂).relFrom (Sum.inr q) w v (Sum.inr p))
    (NFAO.relFrom_nil _ _) (fun q q' u x w v ht _ ih => ?_) h
  exact NFAO.relFrom_step (Or.inr ⟨(q, u, x, q'), ht, rfl⟩) ih

/-- A path of the disjoint union that ends in the first copy runs inside the first copy. -/
lemma sumAut_relFrom_left_source {x : Q₁ ⊕ Q₂} {p : Q₁} {w : List A} {v : List B}
    (h : (sumAut M₁ M₂).relFrom x w v (Sum.inl p)) :
    ∃ q, x = Sum.inl q ∧ M₁.relFrom q w v p := by
  refine NFAO.relFrom_induction (M := sumAut M₁ M₂)
    (motive := fun x w v => ∃ q, x = Sum.inl q ∧ M₁.relFrom q w v p)
    ⟨p, rfl, NFAO.relFrom_nil _ _⟩ (fun x x' u o w v ht _ ih => ?_) h
  obtain ⟨q', hq', hrel⟩ := ih
  rcases ht with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ :
        x = Sum.inl t.1 ∧ u = t.2.1 ∧ o = t.2.2.1 ∧ x' = Sum.inl t.2.2.2 := by
      simp_all [Prod.ext_iff]
    refine ⟨t.1, rfl, ?_⟩
    have hq : q' = t.2.2.2 := by simpa using hq'.symm
    subst hq
    exact NFAO.relFrom_step ht hrel
  · exfalso
    have hx' : x' = Sum.inr t.2.2.2 := by
      have := congrArg (fun z => z.2.2.2) heq
      simpa using this.symm
    rw [hx'] at hq'
    simp at hq'

/-- A path of the disjoint union that ends in the second copy runs inside the second copy. -/
lemma sumAut_relFrom_right_source {x : Q₁ ⊕ Q₂} {p : Q₂} {w : List A} {v : List B}
    (h : (sumAut M₁ M₂).relFrom x w v (Sum.inr p)) :
    ∃ q, x = Sum.inr q ∧ M₂.relFrom q w v p := by
  refine NFAO.relFrom_induction (M := sumAut M₁ M₂)
    (motive := fun x w v => ∃ q, x = Sum.inr q ∧ M₂.relFrom q w v p)
    ⟨p, rfl, NFAO.relFrom_nil _ _⟩ (fun x x' u o w v ht _ ih => ?_) h
  obtain ⟨q', hq', hrel⟩ := ih
  rcases ht with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
  · exfalso
    have hx' : x' = Sum.inl t.2.2.2 := by
      have := congrArg (fun z => z.2.2.2) heq
      simpa using this.symm
    rw [hx'] at hq'
    simp at hq'
  · obtain ⟨rfl, rfl, rfl, rfl⟩ :
        x = Sum.inr t.1 ∧ u = t.2.1 ∧ o = t.2.2.1 ∧ x' = Sum.inr t.2.2.2 := by
      simp_all [Prod.ext_iff]
    refine ⟨t.1, rfl, ?_⟩
    have hq : q' = t.2.2.2 := by simpa using hq'.symm
    subst hq
    exact NFAO.relFrom_step ht hrel

/-- The disjoint union computes the union of the two relations. -/
lemma sumAut_rel_iff (w : List A) (v : List B) :
    (sumAut M₁ M₂).rel w v ↔ M₁.rel w v ∨ M₂.rel w v := by
  rw [NFAO.rel_iff_relFrom, NFAO.rel_iff_relFrom, NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨x, hx, y, hy, hrel⟩
    rcases hy with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨q, rfl, hq⟩ := sumAut_relFrom_left_source hrel
      rcases hx with ⟨q', hq', hq'eq⟩ | ⟨q', hq', hq'eq⟩
      · exact Or.inl ⟨q, by rwa [(by simpa using hq'eq : q' = q)] at hq', p, hp, hq⟩
      · exact absurd hq'eq (by simp)
    · obtain ⟨q, rfl, hq⟩ := sumAut_relFrom_right_source hrel
      rcases hx with ⟨q', hq', hq'eq⟩ | ⟨q', hq', hq'eq⟩
      · exact absurd hq'eq (by simp)
      · exact Or.inr ⟨q, by rwa [(by simpa using hq'eq : q' = q)] at hq', p, hp, hq⟩
  · rintro (⟨q, hq, p, hp, hrel⟩ | ⟨q, hq, p, hp, hrel⟩)
    · exact ⟨Sum.inl q, Or.inl ⟨q, hq, rfl⟩, Sum.inl p, Or.inl ⟨p, hp, rfl⟩,
        sumAut_relFrom_left hrel⟩
    · exact ⟨Sum.inr q, Or.inr ⟨q, hq, rfl⟩, Sum.inr p, Or.inr ⟨p, hp, rfl⟩,
        sumAut_relFrom_right hrel⟩

/-- Rational relations are closed under union. -/
theorem isRationalRel_union {R S : List A → List B → Prop}
    (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => R w v ∨ S w v) := by
  obtain ⟨Q₁, h₁, M₁, hM₁⟩ := hR
  obtain ⟨Q₂, h₂, M₂, hM₂⟩ := hS
  haveI := h₁; haveI := h₂
  refine ⟨Q₁ ⊕ Q₂, inferInstance, sumAut M₁ M₂, fun w v => ?_⟩
  rw [sumAut_rel_iff]
  exact or_congr (hM₁ w v) (hM₂ w v)

end Union

/-! ### The relation that empties a regular language -/

lemma homOf_singleton {B : Type} (u : List B) : homOf (fun b : B => [b]) u = u := by
  induction u with
  | nil => rfl
  | cons c u ih => rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih, List.singleton_append]

lemma homOf_nil_const {A B : Type} (u : List B) : homOf (fun _ : B => ([] : List A)) u = [] := by
  induction u with
  | nil => rfl
  | cons c u ih => rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih]; rfl

/-- The relation that maps every string of a regular language to the empty string is rational:
this is the default output that the solution adds outside the range of the function. -/
lemma isRationalRel_regular_to_nil {A B : Type} [Finite B] {L : Language B} (hL : L.IsRegular) :
    IsRationalRel (fun (v : List B) (u : List A) => v ∈ L ∧ u = []) := by
  have h := isRationalRel_of_regular_nivat (fun b : B => [b]) (fun _ : B => ([] : List A)) hL
  refine isRationalRel_congr h ?_
  intro v u
  constructor
  · rintro ⟨hv, rfl⟩
    exact ⟨v, hv, homOf_singleton v, homOf_nil_const v⟩
  · rintro ⟨x, hx, hxv, hxu⟩
    rw [homOf_singleton] at hxv
    rw [homOf_nil_const] at hxu
    exact ⟨hxv ▸ hx, hxu.symm⟩

/-! ### Injectivity -/

/-- **Exercise `exer:rational-injectivity-decidable`**, the first step of the solution: an
injective rational function `f : A* → B*` has a rational left inverse, a rational function
`g : B* → A*` with `g (f w) = w` for every `w`.

This is the author's construction: the inverse relation of `f` is rational, it is made total by
sending every string outside the range of `f` — a regular language — to the empty string, and
the Uniformisation Lemma `lem:uniformisation`, in the form
`Transducers.exists_rationalFun_of_total_rel`, provides a rational function inside it. -/
theorem exists_rationalFun_inverse_of_injective {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) (hinj : Function.Injective f) :
    ∃ g : List B → List A, IsRationalFun g ∧ ∀ w, g (f w) = w := by
  set L : Language B := {v | ∃ w, v = f w} with hL
  have hLreg : L.IsRegular := rationalRel_range_isRegular hf
  have hrat : IsRationalRel (fun (v : List B) (u : List A) => v = f u ∨ (v ∈ Lᶜ ∧ u = [])) :=
    isRationalRel_union (isRationalRel_inv hf) (isRationalRel_regular_to_nil hLreg.compl)
  have htot : ∀ v : List B, ∃ u : List A, v = f u ∨ (v ∈ Lᶜ ∧ u = []) := by
    intro v
    by_cases hv : v ∈ L
    · obtain ⟨w, hw⟩ := hv
      exact ⟨w, Or.inl hw⟩
    · exact ⟨[], Or.inr ⟨hv, rfl⟩⟩
  obtain ⟨g, hg, hgspec⟩ := exists_rationalFun_of_total_rel hrat htot
  refine ⟨g, hg, fun w => ?_⟩
  rcases hgspec (f w) with h | ⟨hmem, _⟩
  · exact hinj h.symm
  · exact absurd ⟨w, rfl⟩ hmem

/-- **Exercise `exer:rational-injectivity-decidable`**, the criterion of the solution: a
rational function is injective exactly when it has a rational left inverse.  The decision
procedure that the exercise asks for would apply Theorem `thm:equivalence-rational-functions`
to that left inverse composed with the function; see the header of this file for why that step
is not formalised. -/
theorem rationalFun_injective_iff_exists_inverse {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) :
    Function.Injective f ↔ ∃ g : List B → List A, IsRationalFun g ∧ ∀ w, g (f w) = w := by
  constructor
  · exact exists_rationalFun_inverse_of_injective hf
  · rintro ⟨g, _, hg⟩ w w' hww'
    rw [← hg w, ← hg w', hww']

end Transducers.Exercises
