/-
Part D, Section *Evaluation*, subsection *The evaluation algorithm*: Claim
`claim:mso-formula-recognised-by-homomorphism` (every mso formula is recognised by a monoid
homomorphism).

## Profiles

The book defines the *profile* of distinguished positions `x₁, …, x_k, y` of a string `w` under a
monoid homomorphism `h` by a picture: the distinguished positions, with their labels, and the
values of `h` on the factors of `w` between them.  `Transducers.mso_profile h w fo` formalises it
for an arbitrary valuation `fo : Fin n → ℕ` of `n` first-order variables (the book's variables
`x₁, …, x_k, y`, with `n = k + 1`).  It is read off the string `w ⊗ {fo 0} ⊗ ⋯ ⊗ {fo (n-1)}` in which
every position carries its letter and the set of variables that point to it: it is the value of
`h` on the factor before the first distinguished position, followed by the list, from left to right,
of the distinguished positions, each with its letter, the set of variables pointing to it, and the
value of `h` on the factor up to the next distinguished position (or to the end of the string).  The
book's positions are distinct and ordered, `x₁ < ⋯ < x_k`; the definition does not need that, as
the set of variables at each distinguished position records which variables coincide and in which
order they come.

A formula `ψ` is *recognised* by `h` if the profile determines whether `ψ` holds.

## The proof

It is the book's: the formula defines a regular language of annotated strings over `A × 2ⁿ`
(Lemma `lem:mso-free-variables`, `Transducers.mso_annotated_regular`), which is recognised by a
homomorphism `g` into a finite monoid (Theorem `thm:monoids-equal-automata`); the homomorphism `h`
simulates `g` on strings without distinguished positions, and the value of `g` on the annotated
string is computed from the profile under `h` (`Transducers.MSOProfile.g_eq_eval`).
-/
import RequestProject.PartC.MSO
import RequestProject.PartD.MonoidAut

namespace Transducers

variable {A M : Type} [Monoid M] {n : ℕ}

/-- The string `w ⊗ {fo 0} ⊗ ⋯ ⊗ {fo (n-1)}`: every position carries its letter and the set of the
first-order variables that point to it. -/
def markFO (n : ℕ) (w : List A) (fo : Fin n → ℕ) : List (A × (Fin n → Bool)) :=
  w.zipIdx.map (fun z => (z.1, fun i => decide (fo i = z.2)))

/-- The profile of a marked string: the value of `h` on the factor before the first marked
position, and, for every marked position from left to right, its letter and set of variables
together with the value of `h` on the factor that follows it, up to the next marked position. -/
def profileOf (h : FreeMonoid A →* M) :
    List (A × (Fin n → Bool)) → M × List ((A × (Fin n → Bool)) × M)
  | [] => (1, [])
  | (a, b) :: rest =>
    if b = (fun _ => false) then
      (h (FreeMonoid.of a) * (profileOf h rest).1, (profileOf h rest).2)
    else (1, ((a, b), (profileOf h rest).1) :: (profileOf h rest).2)

/-- **The profile** of the distinguished positions `fo 0, …, fo (n-1)` of the string `w` under the
monoid homomorphism `h`: the distinguished positions, with their letters and the variables pointing
to them, and the values of `h` on the factors between them. -/
def mso_profile (h : FreeMonoid A →* M) (w : List A) (fo : Fin n → ℕ) :
    M × List ((A × (Fin n → Bool)) × M) :=
  profileOf h (markFO n w fo)

namespace MSOProfile

/-- The letter of the annotated alphabet with no second-order components. -/
def ext (d : A × (Fin n → Bool)) : A × (Fin n → Bool) × (Fin 0 → Bool) := (d.1, d.2, Fin.elim0)

/-- The value of a profile, given the homomorphism `g` on annotated letters. -/
def evalProf (g : FreeMonoid (A × (Fin n → Bool) × (Fin 0 → Bool)) →* M)
    (p : M × List ((A × (Fin n → Bool)) × M)) : M :=
  p.1 * (p.2.map (fun dm => g (FreeMonoid.of (ext dm.1)) * dm.2)).prod

lemma g_eq_eval (g : FreeMonoid (A × (Fin n → Bool) × (Fin 0 → Bool)) →* M) :
    ∀ u : List (A × (Fin n → Bool)),
      g (FreeMonoid.ofList (u.map ext)) =
        evalProf g (profileOf (FreeMonoid.lift fun a => g (FreeMonoid.of (a, fun _ => false,
          Fin.elim0))) u)
  | [] => by simp [evalProf, profileOf]
  | (a, b) :: rest => by
    have ih := g_eq_eval g rest
    rw [List.map_cons, FreeMonoid.ofList_cons, map_mul, ih]
    by_cases hb : b = (fun _ => false)
    · subst hb
      simp only [profileOf, if_pos, evalProf, ext, FreeMonoid.lift_eval_of, mul_assoc]
    · simp only [profileOf, if_neg hb, evalProf, List.map_cons, List.prod_cons, one_mul, ext]
      rw [mul_assoc]

lemma annotate_eq (w : List A) (fo : Fin n → ℕ) (so : Fin 0 → Set ℕ) :
    annotate n 0 w fo so = (markFO n w fo).map ext := by
  simp only [annotate, markFO, List.map_map]
  congr 1
  funext z
  simp only [Function.comp, ext]
  congr 2
  funext j
  exact j.elim0

lemma markFO_getElem? (w : List A) (fo : Fin n → ℕ) (p : ℕ) :
    (markFO n w fo)[p]? = w[p]?.map (fun a => (a, fun i => decide (fo i = p))) := by
  simp only [markFO, List.getElem?_map, List.getElem?_zipIdx, Option.map_map, zero_add]
  rfl

lemma markFO_inj {w w' : List A} {fo fo' : Fin n → ℕ} (hfo : ∀ i, fo i < w.length)
    (h : markFO n w fo = markFO n w' fo') : w = w' ∧ fo = fo' := by
  have hw : w = w' := by
    have := congrArg (List.map Prod.fst) h
    simpa [markFO, List.map_map, Function.comp_def, List.zipIdx_map_fst] using this
  subst hw
  refine ⟨rfl, funext fun i => ?_⟩
  have h1 := markFO_getElem? w fo (fo i)
  have h2 := markFO_getElem? w fo' (fo i)
  rw [h] at h1
  rw [h1, List.getElem?_eq_getElem (hfo i)] at h2
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h2
  have := congrFun h2 i
  simp at this
  exact this.symm

end MSOProfile

open MSOProfile in
/-- **Claim `claim:mso-formula-recognised-by-homomorphism`.**  Every mso formula `ψ` whose free
variables are first-order variables among `0, …, n-1` is recognised by some monoid homomorphism
`h : A* → M` into a finite monoid: whether `ψ` holds of distinguished positions `fo 0, …, fo (n-1)`
of a string is determined by their profile under `h` (`Transducers.mso_profile`). -/
theorem mso_formula_recognised_by_homomorphism {A : Type} [Finite A] (ψ : MSO A) (n : ℕ)
    (hfo : ψ.freeFO ⊆ {i | i < n}) (hso : ψ.freeSO = ∅) :
    ∃ (M : Type) (_ : Monoid M) (_ : Finite M) (h : FreeMonoid A →* M),
      ∀ (w w' : List A) (fo fo' : Fin n → ℕ), (∀ i, fo i < w.length) →
        (∀ i, fo' i < w'.length) → mso_profile h w fo = mso_profile h w' fo' →
          (MSO.Sat w (extFO n fo) (fun _ => ∅) ψ ↔ MSO.Sat w' (extFO n fo') (fun _ => ∅) ψ) := by
  have hreg := mso_annotated_regular ψ n 0 hfo (by rw [hso]; exact Set.empty_subset _)
  obtain ⟨M, hM, hfin, g, hg⟩ := (regular_iff_recognised_by_monoid _).mp hreg
  refine ⟨M, hM, hfin, FreeMonoid.lift fun a => g (FreeMonoid.of (a, fun _ => false, Fin.elim0)),
    ?_⟩
  -- membership of the annotated string in the language is satisfaction of the formula
  have hso0 : ∀ so : Fin 0 → Set ℕ, extSO 0 so = fun _ => ∅ := fun so => by
    funext j; simp [extSO]
  have hmem : ∀ (w : List A) (fo : Fin n → ℕ), (∀ i, fo i < w.length) →
      ((annotate n 0 w fo Fin.elim0 ∈ {u : List (A × (Fin n → Bool) × (Fin 0 → Bool)) |
        ∃ (w : List A) (fo : Fin n → ℕ) (so : Fin 0 → Set ℕ),
          (∀ i, fo i < w.length) ∧ (∀ j, so j ⊆ {p | p < w.length}) ∧
          u = annotate n 0 w fo so ∧ MSO.Sat w (extFO n fo) (extSO 0 so) ψ}) ↔
        MSO.Sat w (extFO n fo) (fun _ => ∅) ψ) := by
    intro w fo hw
    constructor
    · rintro ⟨w', fo', so', hw', -, heq, hsat⟩
      rw [annotate_eq, annotate_eq] at heq
      have hinj := markFO_inj hw (List.map_injective_iff.mpr (fun d d' hdd' => by
        obtain ⟨a, b⟩ := d
        obtain ⟨a', b'⟩ := d'
        simp only [ext, Prod.mk.injEq] at hdd'
        rw [hdd'.1, hdd'.2.1]) heq)
      obtain ⟨rfl, rfl⟩ := hinj
      rwa [hso0] at hsat
    · intro hsat
      exact ⟨w, fo, Fin.elim0, hw, fun j => j.elim0, rfl, by rwa [hso0]⟩
  intro w w' fo fo' hw hw' hprof
  rw [← hmem w fo hw, ← hmem w' fo' hw']
  apply hg
  rw [annotate_eq, annotate_eq, g_eq_eval, g_eq_eval]
  exact congrArg (evalProf g) hprof

end Transducers
