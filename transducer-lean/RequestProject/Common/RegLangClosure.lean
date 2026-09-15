/-
Closure properties of regular languages: a general-purpose library, with nothing in it about
transducers.

Mathlib knows that the regular languages are closed under complement, union and intersection
(`Language.IsRegular.compl`, `Language.IsRegular.add`, `Language.IsRegular.inf`), and it proves the
Myhill-Nerode theorem (`Language.isRegular_iff_finite_range_leftQuotient`), but it does not have the
two closure properties that a regular *expression* needs: concatenation and the Kleene star.  They
are proved here, together with the regularity of a finite language, by the Myhill-Nerode criterion:
in each case the left quotient `L.leftQuotient x = {y | x ++ y ∈ L}` is computed from a bounded
amount of information about `x`, and the criterion then bounds the number of left quotients.

* `Transducers.isRegular_mul`   -- `L * M` is regular when `L` and `M` are;
* `Transducers.isRegular_kstar` -- `L∗` is regular when `L` is;
* `Transducers.isRegular_singleton`, `Transducers.isRegular_zero`,
  `Transducers.isRegular_biUnion_finset` -- singletons, the empty language, and a finite union.

Nothing in the project uses them at present: they were written for the parsing step of the
normalisation proof of Theorem `thm:higher-order-terms`, which the book has since replaced by the
good-functions argument, so the file that used them is gone.  They are kept because they are a
self-contained addition to what Mathlib has about regular languages, and are stated for arbitrary
languages over a finite alphabet.

Unions are written as set-builders rather than with `∪` and `⋃`, because `Language α` carries its
own algebraic structure and the `Set` operations do not apply to it directly.
-/
import Mathlib

namespace Transducers

open Language Computability

variable {α : Type}

/-! ## The Myhill-Nerode criterion in the form used below -/

/-- If all the left quotients of `L` lie in a fixed finite set of languages, then `L` is
regular. -/
theorem isRegular_of_leftQuotient_mem {L : Language α} {S : Set (Language α)} (hS : S.Finite)
    (h : ∀ x, L.leftQuotient x ∈ S) : L.IsRegular :=
  Language.isRegular_iff_finite_range_leftQuotient.mpr
    (hS.subset (by rintro _ ⟨x, rfl⟩; exact h x))

/-- Transport regularity along an equality of languages. -/
theorem isRegular_of_eq {L M : Language α} (h : L = M) (hL : L.IsRegular) : M.IsRegular := h ▸ hL

/-! ## Finite languages -/

/-- The empty language is regular. -/
theorem isRegular_zero : (0 : Language α).IsRegular := by
  refine isRegular_of_leftQuotient_mem (S := {0}) (Set.finite_singleton _) fun x => ?_
  ext y
  simp [Language.mem_leftQuotient]

/-- A language with one word is regular. -/
theorem isRegular_singleton (w : List α) : ({w} : Language α).IsRegular := by
  classical
  refine isRegular_of_leftQuotient_mem
    (S := insert (0 : Language α) ((fun v => ({v} : Language α)) '' {v | v ∈ w.tails}))
    (Set.Finite.insert _ (Set.Finite.image _ (List.finite_toSet _))) fun x => ?_
  by_cases h : ∃ v, w = x ++ v
  · obtain ⟨v, rfl⟩ := h
    refine Set.mem_insert_of_mem _ ⟨v, (List.mem_tails v (x ++ v)).mpr ⟨x, rfl⟩, ?_⟩
    ext y
    show y = v ↔ x ++ y = x ++ v
    exact ⟨fun hy => by rw [hy], fun hy => List.append_cancel_left hy⟩
  · refine Set.mem_insert_iff.mpr (Or.inl ?_)
    ext y
    show (x ++ y = w) ↔ False
    exact ⟨fun hy => absurd ⟨y, hy.symm⟩ h, fun hy => hy.elim⟩

/-- The union of two regular languages, in set-builder form. -/
theorem isRegular_union {L M : Language α} (hL : L.IsRegular) (hM : M.IsRegular) :
    Language.IsRegular {y | y ∈ L ∨ y ∈ M} := by
  have he : L + M = {y | y ∈ L ∨ y ∈ M} := by
    ext y
    exact Language.mem_add L M y
  exact he ▸ hL.add hM

/-- A finite union of regular languages, indexed by a `Finset`. -/
theorem isRegular_biUnion_finset {ι : Type*} (s : Finset ι) (L : ι → Language α)
    (h : ∀ i ∈ s, (L i).IsRegular) :
    Language.IsRegular {y | ∃ i ∈ s, y ∈ L i} := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : {y : List α | ∃ i ∈ (∅ : Finset ι), y ∈ L i} = (0 : Language α) := by
        ext y
        exact ⟨fun hy => absurd hy.choose_spec.1 (Finset.notMem_empty _), fun hy => hy.elim⟩
      rw [h0]
      exact isRegular_zero
  | insert a s ha ih =>
      have h1 : (L a).IsRegular := h a (Finset.mem_insert_self a s)
      have h2 : Language.IsRegular {y | ∃ i ∈ s, y ∈ L i} :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      have he : {y : List α | y ∈ L a ∨ y ∈ {y : List α | ∃ i ∈ s, y ∈ L i}}
          = {y : List α | ∃ i ∈ insert a s, y ∈ L i} := by
        ext y
        simp only [Finset.mem_insert, Set.mem_setOf_eq]
        constructor
        · rintro (hy | ⟨i, hi, hy⟩)
          · exact ⟨a, Or.inl rfl, hy⟩
          · exact ⟨i, Or.inr hi, hy⟩
        · rintro ⟨i, hi | hi, hy⟩
          · exact Or.inl (hi ▸ hy)
          · exact Or.inr ⟨i, hi, hy⟩
      exact he ▸ isRegular_union h1 h2

/-- A language contained in a finite set of words is regular. -/
theorem isRegular_of_subset_finite {L : Language α} {F : Finset (List α)}
    (h : ∀ w ∈ L, w ∈ F) : L.IsRegular := by
  classical
  have hb := isRegular_biUnion_finset (F.filter (fun w => w ∈ L)) (fun w => ({w} : Language α))
    (fun w _ => isRegular_singleton w)
  have he : {y : List α | ∃ w ∈ F.filter (fun w => w ∈ L), y ∈ ({w} : Language α)} = L := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (Finset.mem_filter.mp hw).2
    · intro hy
      exact ⟨y, Finset.mem_filter.mpr ⟨h y hy, hy⟩, rfl⟩
  exact he ▸ hb

/-- A regular language guarded by a proposition. -/
theorem isRegular_prop_and (p : Prop) {L : Language α} (hL : L.IsRegular) :
    Language.IsRegular {w | p ∧ w ∈ L} := by
  by_cases hp : p
  · have he : L = {w | p ∧ w ∈ L} := by
      ext w
      exact ⟨fun hw => ⟨hp, hw⟩, fun hw => hw.2⟩
    exact he ▸ hL
  · have he : (0 : Language α) = {w | p ∧ w ∈ L} := by
      ext w
      exact ⟨fun hw => hw.elim, fun hw => absurd hw.1 hp⟩
    exact he ▸ isRegular_zero

/-! ## Concatenation -/

/-- The left quotient of a concatenation: either the whole of the first factor is still to come,
or the prefix `x` has already crossed into the second factor. -/
theorem leftQuotient_mul (L M : Language α) (x : List α) :
    (L * M).leftQuotient x
      = {y | y ∈ (L.leftQuotient x) * M
              ∨ ∃ v, (∃ u ∈ L, x = u ++ v) ∧ y ∈ M.leftQuotient v} := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.mp hy
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · refine Or.inr ⟨c, ⟨a, ha, hc1⟩, ?_⟩
      show c ++ y ∈ M
      exact hc2 ▸ hb
    · refine Or.inl (Language.mem_mul.mpr ⟨c, ?_, b, hb, hc2.symm⟩)
      show x ++ c ∈ L
      exact hc1 ▸ ha
  · rintro (hy | ⟨v, ⟨u, hu, hx⟩, hy⟩)
    · obtain ⟨c, hc, b, hb, hcb⟩ := Language.mem_mul.mp hy
      refine Language.mem_mul.mpr ⟨x ++ c, hc, b, hb, ?_⟩
      rw [List.append_assoc, hcb]
    · refine Language.mem_mul.mpr ⟨u, hu, v ++ y, hy, ?_⟩
      rw [← List.append_assoc, ← hx]

/-- **The regular languages are closed under concatenation.** -/
theorem isRegular_mul {L M : Language α} (hL : L.IsRegular) (hM : M.IsRegular) :
    (L * M).IsRegular := by
  have h1 := hL.finite_range_leftQuotient
  have h2 := hM.finite_range_leftQuotient
  refine isRegular_of_leftQuotient_mem
    (S := (fun p : Language α × Set (Language α) =>
        ({y | y ∈ p.1 * M ∨ ∃ P ∈ p.2, y ∈ P} : Language α)) ''
      (Set.range L.leftQuotient ×ˢ {s | s ⊆ Set.range M.leftQuotient}))
    (Set.Finite.image _ (h1.prod h2.finite_subsets)) fun x => ?_
  refine ⟨(L.leftQuotient x, M.leftQuotient '' {v : List α | ∃ u ∈ L, x = u ++ v}),
    ⟨⟨x, rfl⟩, ?_⟩, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · rw [leftQuotient_mul]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro (hy | ⟨P, ⟨v, hv, rfl⟩, hy⟩)
      · exact Or.inl hy
      · exact Or.inr ⟨v, hv, hy⟩
    · rintro (hy | ⟨v, hv, hy⟩)
      · exact Or.inl hy
      · exact Or.inr ⟨M.leftQuotient v, ⟨v, hv, rfl⟩, hy⟩

/-- The concatenation of two regular languages, in set-builder form. -/
theorem isRegular_concat {L M : Language α} (hL : L.IsRegular) (hM : M.IsRegular) :
    Language.IsRegular {w | ∃ u ∈ L, ∃ v ∈ M, w = u ++ v} := by
  have he : L * M = {w | ∃ u ∈ L, ∃ v ∈ M, w = u ++ v} := by
    ext w
    constructor
    · intro hw
      obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp hw
      exact ⟨u, hu, v, hv, huv.symm⟩
    · rintro ⟨u, hu, v, hv, rfl⟩
      exact Language.mem_mul.mpr ⟨u, hu, v, hv, rfl⟩
  exact he ▸ isRegular_mul hL hM

/-! ## The Kleene star -/

theorem mem_kstar_of_mem {L : Language α} {a : List α} (ha : a ∈ L) : a ∈ L∗ :=
  Language.mem_kstar.mpr ⟨[a], by simp, by simpa using ha⟩

theorem append_mem_kstar {L : Language α} {a b : List α} (ha : a ∈ L∗) (hb : b ∈ L∗) :
    a ++ b ∈ L∗ := by
  obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.mp ha
  obtain ⟨T, rfl, hT⟩ := Language.mem_kstar.mp hb
  refine Language.mem_kstar.mpr ⟨S ++ T, by simp, fun y hy => ?_⟩
  rcases List.mem_append.mp hy with h | h
  exacts [hS y h, hT y h]

/-- The splitting of a word of `L∗` at a prefix: either the prefix is itself in `L∗` and so is the
rest, or the prefix ends inside one of the factors. -/
private theorem kstar_split (L : Language α) :
    ∀ (S : List (List α)) (x y : List α), (∀ w ∈ S, w ∈ L) → S.flatten = x ++ y →
      (x ∈ L∗ ∧ y ∈ L∗) ∨ ∃ v, (∃ u ∈ L∗, x = u ++ v) ∧ y ∈ (L.leftQuotient v) * L∗ := by
  intro S
  induction S with
  | nil =>
      intro x y _ h
      obtain ⟨hx, hy⟩ := List.append_eq_nil_iff.mp h.symm
      exact Or.inl ⟨hx ▸ Language.nil_mem_kstar L, hy ▸ Language.nil_mem_kstar L⟩
  | cons w S ih =>
      intro x y hmem h
      have hw : w ∈ L := hmem w (List.mem_cons_self ..)
      have hS : ∀ u ∈ S, u ∈ L := fun u hu => hmem u (List.mem_cons_of_mem _ hu)
      have h' : w ++ S.flatten = x ++ y := by simpa using h
      rcases List.append_eq_append_iff.mp h' with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
      · rcases ih c y hS hc2 with ⟨hc, hy⟩ | ⟨v, ⟨u, hu, hcv⟩, hy⟩
        · exact Or.inl ⟨hc1 ▸ append_mem_kstar (mem_kstar_of_mem hw) hc, hy⟩
        · refine Or.inr ⟨v, ⟨w ++ u, append_mem_kstar (mem_kstar_of_mem hw) hu, ?_⟩, hy⟩
          rw [List.append_assoc, ← hcv, hc1]
      · refine Or.inr ⟨x, ⟨[], Language.nil_mem_kstar L, by simp⟩, ?_⟩
        refine Language.mem_mul.mpr ⟨c, ?_, S.flatten, Language.join_mem_kstar hS, hc2.symm⟩
        show x ++ c ∈ L
        exact hc1 ▸ hw

/-- The left quotient of a Kleene star. -/
theorem leftQuotient_kstar (L : Language α) (x : List α) :
    (L∗).leftQuotient x
      = {y | (∃ v, (∃ u ∈ L∗, x = u ++ v) ∧ y ∈ (L.leftQuotient v) * L∗)
            ∨ (x ∈ L∗ ∧ y ∈ L∗)} := by
  ext y
  constructor
  · intro hy
    obtain ⟨S, hS, hSmem⟩ := Language.mem_kstar.mp hy
    rcases kstar_split L S x y hSmem hS.symm with h | ⟨v, hv, hyv⟩
    · exact Or.inr h
    · exact Or.inl ⟨v, hv, hyv⟩
  · rintro (⟨v, ⟨u, hu, hx⟩, hyv⟩ | ⟨hx, hy⟩)
    · obtain ⟨c, hc, z, hz, hcz⟩ := Language.mem_mul.mp hyv
      show x ++ y ∈ L∗
      have hxy : x ++ y = (u ++ (v ++ c)) ++ z := by
        rw [← hcz, hx]; simp
      rw [hxy]
      exact append_mem_kstar (append_mem_kstar hu (mem_kstar_of_mem hc)) hz
    · exact append_mem_kstar hx hy

/-- **The regular languages are closed under the Kleene star.** -/
theorem isRegular_kstar {L : Language α} (hL : L.IsRegular) : (L∗).IsRegular := by
  have h1 := hL.finite_range_leftQuotient
  refine isRegular_of_leftQuotient_mem
    (S := (fun p : Set (Language α) × Prop =>
        ({y | (∃ P ∈ p.1, y ∈ P * L∗) ∨ (p.2 ∧ y ∈ L∗)} : Language α)) ''
      ({s | s ⊆ Set.range L.leftQuotient} ×ˢ (Set.univ : Set Prop)))
    (Set.Finite.image _ (h1.finite_subsets.prod Set.finite_univ)) fun x => ?_
  refine ⟨(L.leftQuotient '' {v : List α | ∃ u ∈ L∗, x = u ++ v}, x ∈ L∗),
    ⟨?_, Set.mem_univ _⟩, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · rw [leftQuotient_kstar]
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro (⟨P, ⟨v, hv, rfl⟩, hy⟩ | hy)
      · exact Or.inl ⟨v, hv, hy⟩
      · exact Or.inr hy
    · rintro (⟨v, hv, hy⟩ | hy)
      · exact Or.inl ⟨L.leftQuotient v, ⟨v, hv, rfl⟩, hy⟩
      · exact Or.inr hy

end Transducers
