/-
Part C, Section C.4: Logic
  from *Transducers* (M. Bojańczyk, June 25, 2026).

The numbered results of Section C.4 that are proved: Theorem C.4.1,
Lemma C.4.2, Claim C.4.6 and Lemma C.4.15.  Every proof in this file is
complete.

The definitions they speak about (monadic second-order logic, mso relabellings,
mso transductions and the first-order fragment) are in
`RequestProject/PartC/MSODef.lean`, the constructions used in their proofs in
`RequestProject/PartC/MSOSyntax.lean`, `RequestProject/PartC/RegAut.lean`,
`RequestProject/PartC/MSOAnnot.lean`, `RequestProject/PartC/MSOBuchi.lean`,
`RequestProject/PartC/MSORelab.lean` and `RequestProject/PartC/KTypes.lean`.

The numbered results of Section C.4 that are still open (Theorem C.4.4,
Lemma C.4.10, Theorem C.4.8, Theorem C.4.11, Lemma C.4.13, Theorem C.4.16 and
Theorem C.4.17) are stated in `RequestProject/PartC/MSOOpen.lean`, which this
file imports; so importing `RequestProject.PartC.MSO` gives, as before, all the
statements of Section C.4.

Not formalised: Claim C.4.5, Lemma C.4.9 and Claim C.4.14, which are internal
steps of the proofs of Theorems C.4.4, C.4.8 and C.4.11.
-/
import RequestProject.PartC.MSOBuchi
import RequestProject.PartC.MSORelab
import RequestProject.PartC.MSOOpen

namespace Transducers

/-! ## C.4.1 Monadic second-order logic -/

/-- **Theorem C.4.1.**  A language is regular if and only if it is definable in
monadic second-order logic. -/
theorem regular_iff_msoDefinable {A : Type} [Finite A] (L : Language A) :
    L.IsRegular ↔ MSODefinable L :=
  regular_iff_msoDefinable_aux L

/-- **Lemma C.4.2.**  For an mso formula whose free variables are among
`x₁, …, x_k, X₁, …, X_l`, the set of annotated strings that satisfy it is a
regular language over the alphabet `A × 2^{k+l}`. -/
theorem mso_annotated_regular {A : Type} [Finite A] (φ : MSO A) (k l : ℕ)
    (hfo : φ.freeFO ⊆ {i | i < k}) (hso : φ.freeSO ⊆ {j | j < l}) :
    Language.IsRegular
      {u : List (A × (Fin k → Bool) × (Fin l → Bool)) |
        ∃ (w : List A) (fo : Fin k → ℕ) (so : Fin l → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate k l w fo so ∧ MSO.Sat w (extFO k fo) (extSO l so) φ} :=
  mso_annotated_regular_aux φ k l hfo hso

/-! ## C.4.2 Rational functions in terms of logic

Theorem C.4.4 (`rational_iff_msoRelabelling`) and Lemma C.4.10
(`mso_formulas_via_rational`) are still open; they are stated in
`RequestProject/PartC/MSOOpen.lean`. -/

/-- **Claim C.4.6.**  For an mso relabelling, the language of strings over the
alphabet `A × Φ` in which every position is labelled by a formula that holds in
that position is regular. -/
theorem msoRelabelling_annotation_regular {A B : Type} [Finite A] (R : MSORelabelling A B) :
    Language.IsRegular
      {u : List (A × R.Idx) | ∀ (p : ℕ) (hp : p < u.length),
        MSO.Sat (u.map Prod.fst) (fun _ => p) (fun _ => ∅) (R.form (u.get ⟨p, hp⟩).2)} :=
  msoRelabelling_annotation_regular_aux R

/-! ## C.4.4 The first-order fragment

**Definition C.4.12 (k-types)** (`TpType` and `tp`) is in
`RequestProject/PartC/KTypes.lean`, together with the proof of Lemma C.4.15
below. -/

/-- **Lemma C.4.15.**  Refinement, congruence and aperiodicity of `k`-types. -/
theorem tp_properties {A : Type} (k : ℕ) :
    (∀ w v : List A, tp (k + 1) w = tp (k + 1) v → tp k w = tp k v) ∧
    (∀ w w' v v' : List A, tp k w = tp k w' → tp k v = tp k v' →
      tp k (w ++ v) = tp k (w' ++ v')) ∧
    (∀ w : List A, ∃ N : ℕ, ∀ n ≥ N, tp k (npow w n) = tp k (npow w N)) :=
  tp_properties_aux k

end Transducers
