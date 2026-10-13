/-
Part D, Section *Evaluation*, subsection *Simon trees*: Theorem `thm:monoids-equal-automata`
(finite monoids recognise exactly the regular languages) and Lemma `lem:semigroup-is-group`.

## Recognition by a monoid homomorphism

A language `L ⊆ A*` is *recognised* by a monoid homomorphism `h : A* → M` if membership `w ∈ L`
depends only on `h(w)`.  The free monoid `A*` is Mathlib's `FreeMonoid A`, whose elements are the
lists over `A` (`FreeMonoid.ofList`).  Regularity is Mathlib's `Language.IsRegular` (recognition by
a deterministic finite automaton), as everywhere in the project.

The two directions are the two constructions of the book: the automaton whose states are the
elements of the monoid, and the homomorphism into the monoid of state transformations.  Since
`Function.End Q` composes as `f * g = f ∘ g`, that is, it applies `g` first, the transformations are
taken in the opposite monoid `(Function.End Q)ᵐᵒᵖ`, so that the transformation of `u v` is that of
`u` followed by that of `v`.

## Semigroups whose translations are permutations

Lemma `lem:semigroup-is-group` says that a semigroup in which every left and every right
translation is a permutation is a group.  As literally stated it needs the semigroup to be
*nonempty*: the empty semigroup satisfies the hypothesis vacuously and is not a group (it has no
neutral element), and the book's proof starts from an idempotent, which an empty semigroup does not
have.  So `Transducers.semigroup_is_group` assumes `Nonempty S`, and
`Transducers.semigroup_is_group_false_without_nonempty` records that the hypothesis cannot be
dropped.  The book's semigroup is finite, but the proof below does not use finiteness: in any
nonempty semigroup with bijective translations, the element `e` with `e·a = a` for one fixed `a`
is a left identity, and so on.  (Mathlib's `IsOfFinOrder` and idempotent API are therefore not
needed.)
-/
import Mathlib

namespace Transducers

open Function

/-! ## Theorem `thm:monoids-equal-automata` -/

/-- The homomorphism from the free monoid into the monoid of state transformations of a dfa. -/
def dfaTransHom {A Q : Type} (D : DFA A Q) : FreeMonoid A →* (Function.End Q)ᵐᵒᵖ :=
  FreeMonoid.lift fun a => MulOpposite.op (fun q => D.step q a)

lemma dfaTransHom_apply {A Q : Type} (D : DFA A Q) :
    ∀ (w : List A) (q : Q), (dfaTransHom D (FreeMonoid.ofList w)).unop q = D.evalFrom q w
  | [], q => by simp [dfaTransHom]; rfl
  | a :: w, q => by
    rw [FreeMonoid.ofList_cons, map_mul, MulOpposite.unop_mul, DFA.evalFrom_cons,
      ← dfaTransHom_apply D w (D.step q a)]
    simp [dfaTransHom, Function.End.mul_def]

/-- **Theorem `thm:monoids-equal-automata`** (finite monoids and finite automata have the same
expressive power).  A language `L ⊆ A*` is regular if and only if it is recognised by a homomorphism
into a finite monoid: there is a monoid homomorphism `h : A* → M` with `M` finite such that
membership `w ∈ L` depends only on `h(w)`. -/
theorem regular_iff_recognised_by_monoid {A : Type} (L : Language A) :
    L.IsRegular ↔ ∃ (M : Type) (_ : Monoid M) (_ : Finite M) (h : FreeMonoid A →* M),
      ∀ w w' : List A, h (FreeMonoid.ofList w) = h (FreeMonoid.ofList w') → (w ∈ L ↔ w' ∈ L) := by
  constructor
  · rintro ⟨Q, hQ, D, rfl⟩
    haveI : Finite (Function.End Q) := inferInstanceAs (Finite (Q → Q))
    haveI : Finite (Function.End Q)ᵐᵒᵖ := Finite.of_equiv _ MulOpposite.opEquiv
    refine ⟨(Function.End Q)ᵐᵒᵖ, inferInstance, inferInstance, dfaTransHom D, fun w w' hww' => ?_⟩
    have hev : D.eval w = D.eval w' := by
      unfold DFA.eval
      rw [← dfaTransHom_apply, ← dfaTransHom_apply, hww']
    rw [DFA.mem_accepts, DFA.mem_accepts, hev]
  · rintro ⟨M, hM, hfin, h, hrec⟩
    haveI : Fintype M := Fintype.ofFinite M
    let D : DFA A M :=
      { step := fun m a => m * h (FreeMonoid.of a)
        start := 1
        accept := {m | ∃ w ∈ L, h (FreeMonoid.ofList w) = m} }
    have hev : ∀ (w : List A) (m : M), D.evalFrom m w = m * h (FreeMonoid.ofList w) := by
      intro w
      induction w with
      | nil => intro m; simp
      | cons a w ih =>
        intro m
        rw [DFA.evalFrom_cons, ih, FreeMonoid.ofList_cons, map_mul, mul_assoc]
    refine ⟨M, inferInstance, D, ?_⟩
    ext w
    rw [DFA.mem_accepts, DFA.eval, hev, one_mul]
    constructor
    · rintro ⟨w', hw', hww'⟩
      exact (hrec w' w hww').mp hw'
    · intro hw
      exact ⟨w, hw, rfl⟩

/-! ## Lemma `lem:semigroup-is-group` -/

/-- **Lemma `lem:semigroup-is-group`.**  If every right translation `t ↦ t·s` and every left
translation `t ↦ s·t` of a semigroup is a permutation, then the semigroup is a group: it has a
two-sided identity `e`, and every element has a two-sided inverse.  The semigroup has to be
nonempty -- see `Transducers.semigroup_is_group_false_without_nonempty`; finiteness, which the book
has in its context, is not needed. -/
theorem semigroup_is_group {S : Type*} [Semigroup S] [Nonempty S]
    (hright : ∀ s : S, Bijective (· * s)) (hleft : ∀ s : S, Bijective (s * ·)) :
    ∃ e : S, (∀ x, e * x = x ∧ x * e = x) ∧ ∀ x, ∃ y, x * y = e ∧ y * x = e := by
  obtain ⟨a⟩ := ‹Nonempty S›
  obtain ⟨e, he⟩ := (hright a).2 a
  obtain ⟨e', he'⟩ := (hleft a).2 a
  simp only at he he'
  have hl : ∀ x, e * x = x := by
    intro x
    obtain ⟨y, rfl⟩ := (hleft a).2 x
    simp only
    rw [← mul_assoc, he]
  have hr : ∀ x, x * e' = x := by
    intro x
    obtain ⟨y, rfl⟩ := (hright a).2 x
    simp only
    rw [mul_assoc, he']
  have hee : e = e' := by rw [← hr e, hl e']
  subst hee
  refine ⟨e, fun x => ⟨hl x, hr x⟩, fun x => ?_⟩
  obtain ⟨y, hy⟩ := (hleft x).2 e
  obtain ⟨z, hz⟩ := (hright x).2 e
  simp only at hy hz
  have hzy : z = y := by rw [← hr z, ← hy, ← mul_assoc, hz, hl]
  subst hzy
  exact ⟨_, hy, hz⟩

/-- The hypothesis `Nonempty S` of `Transducers.semigroup_is_group` cannot be dropped: the empty
semigroup has bijective translations (vacuously), but no identity element.  So Lemma
`lem:semigroup-is-group`, read literally for an arbitrary semigroup, is false; the book's proof
assumes that an idempotent exists, which holds exactly when the (finite) semigroup is nonempty. -/
theorem semigroup_is_group_false_without_nonempty :
    ¬ ∀ (S : Type) (_ : Semigroup S), (∀ s : S, Bijective (· * s)) →
      (∀ s : S, Bijective (s * ·)) →
      ∃ e : S, (∀ x, e * x = x ∧ x * e = x) ∧ ∀ x, ∃ y, x * y = e ∧ y * x = e := by
  intro h
  let inst : Semigroup Empty :=
    { mul := fun a _ => a
      mul_assoc := fun a => a.elim }
  obtain ⟨e, -⟩ := h Empty inst (fun s => s.elim) (fun s => s.elim)
  exact e.elim

end Transducers
