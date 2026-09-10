/-
Part D, Section *A functional programming language*: Definition `def:resource-bound`.

A resource bound is a finite set of types together with a height bound, and a closed term is
consistent with it when its height is at most the bound and every type that appears in it belongs
to the set.  The book introduces resource bounds in order to parse terms with a finite automaton,
and then uses them to control the reduction of terms; the proof of Theorem `thm:higher-order-terms`
formalised here goes by the logical relation of `RequestProject/PartD/HORel.lean` instead.  The
definition itself is formalised, together with the observation that it is not vacuous -- every
closed term is consistent with some resource bound -- and so are the reduction rules
(`RequestProject/PartD/HORed.lean`), Lemma `lem:normal-forms-of-arrow-free-terms`
(`RequestProject/PartD/HONormal.lean`) and Definition `def:majorants`
(`RequestProject/PartD/HOMaj.lean`) and Lemma `claim:parsing-is-regular-with-resource-bounds`
(`RequestProject/PartD/HOStr.lean` and `RequestProject/PartD/HOParse.lean`).  The four remaining
results of the book's normalisation proof -- Lemma `lem:reduction-strategy-lemma`, Corollary
`cor:normalisation-of-terms-with-resource-bounds`, Claim `claim:atomic-functions-majorised` and
Claim `claim:every-term-majorised` -- are not formalised; `THEOREMS.md` says what stands in the way
of each.

Two remarks on the rendering.

* **Height of a list term.**  The book's list constructor takes `n` terms at once, and the height
  of `[a₁,…,aₙ]` is one plus the maximum of the heights of the entries.  Here a list term is a
  cons-chain (see `RequestProject/PartD/HOSyntax.lean`), so `Transducers.HTerm.height` gives a
  cons-chain the height its list term has in the book -- `1 + max` over the entries -- rather than
  counting the conses.

* **Types that appear in a term.**  In the intrinsically typed presentation used here, the types
  used by the subterms of a term are exactly the types of its subterms, and the type annotating an
  abstraction is recorded in the arrow type of the abstraction itself.  So
  `Transducers.HTerm.types` collects the type of every subterm.
-/
import RequestProject.PartD.HOSyntax

namespace Transducers

namespace HTerm

/-- The height of the syntax tree of a term.  A cons-chain is the book's list term
`[a₁,…,aₙ]`, whose height is one plus the maximum of the heights of its entries, so `cons` takes a
maximum rather than adding one for each entry. -/
def height : {Γ : List HTy} → {H : HTy} → HTerm Γ H → ℕ
  | _, _, .var _ => 1
  | _, _, .atom _ => 1
  | _, _, .app f a => 1 + max f.height a.height
  | _, _, .lam b => 1 + b.height
  | _, _, .unit => 1
  | _, _, .pair a b => 1 + max a.height b.height
  | _, _, .nil => 1
  | _, _, .cons a l => max (1 + a.height) l.height

lemma one_le_height {Γ : List HTy} {H : HTy} (t : HTerm Γ H) : 1 ≤ t.height := by
  cases t with
  | cons a _ => exact le_trans (Nat.le_add_right 1 a.height) (le_max_left _ _)
  | app _ _ => exact Nat.le_add_right 1 _
  | lam _ => exact Nat.le_add_right 1 _
  | pair _ _ => exact Nat.le_add_right 1 _
  | _ => exact le_refl 1

/-- The types that appear in a term: the type of every subterm. -/
def types : {Γ : List HTy} → {H : HTy} → HTerm Γ H → Finset HTy
  | _, _, .var (A := A) _ => {A}
  | _, _, .atom (H := H) _ => {H}
  | _, _, .app (B := B) f a => insert B (f.types ∪ a.types)
  | _, _, .lam (A := A) (B := B) b => insert (.arrow A B) b.types
  | _, _, .unit => {.one}
  | _, _, .pair (A := A) (B := B) a b => insert (.prod A B) (a.types ∪ b.types)
  | _, _, .nil (A := A) => {.list A}
  | _, _, .cons (A := A) a l => insert (.list A) (a.types ∪ l.types)

/-- The type of a term is one of the types that appear in it. -/
lemma mem_types {Γ : List HTy} {H : HTy} (t : HTerm Γ H) : H ∈ t.types := by
  cases t <;> simp [types]

end HTerm

/-- **Definition `def:resource-bound` (Resource bound).**  A finite set of types together with a
height bound, which is at least one. -/
structure ResourceBound where
  /-- The finite set of types that a consistent term may use. -/
  types : Finset HTy
  /-- The height bound. -/
  height : ℕ
  /-- The height bound is at least one, as in the book, where it ranges over `{1,2,…}`. -/
  height_pos : 1 ≤ height

/-- **Definition `def:resource-bound`, consistency.**  A closed term is consistent with a resource
bound when its height is at most the height bound and every type that appears in it belongs to the
set of types.  The book states this for closed terms; the definition below reads the same for a
term in any context, and is applied to closed terms. -/
def ResourceBound.Consistent (R : ResourceBound) {Γ : List HTy} {H : HTy} (t : HTerm Γ H) : Prop :=
  t.height ≤ R.height ∧ t.types ⊆ R.types

/-- The definition is not vacuous: every term is consistent with some resource bound. -/
theorem exists_resourceBound_consistent {Γ : List HTy} {H : HTy} (t : HTerm Γ H) :
    ∃ R : ResourceBound, R.Consistent t :=
  ⟨⟨t.types, t.height, HTerm.one_le_height t⟩, le_refl _, subset_refl _⟩

/-- Consistency is monotone in the resource bound. -/
theorem ResourceBound.Consistent.mono {R R' : ResourceBound} {Γ : List HTy} {H : HTy}
    {t : HTerm Γ H} (h : R.Consistent t) (hh : R.height ≤ R'.height)
    (ht : R.types ⊆ R'.types) : R'.Consistent t :=
  ⟨le_trans h.1 hh, subset_trans h.2 ht⟩

end Transducers
