/-
Exercise `exer:fo-suc` of the chapter on logic (`logic.tex`) of *Transducers*
(M. Bojańczyk).
-/
import RequestProject.PartC.MSODef

/-!
# First-order logic with successor only is weaker than with order

Exercise `exer:fo-suc` asks to show that first-order logic on strings in which
the only available predicate is the successor relation is strictly weaker than
first-order logic with the order.

The separating language of the book is

  `{w ∈ {a,b,c}* : w has exactly one b, exactly one c, and the b comes first}`,

which is `Transducers.Exercises.sepLang` below.  The solution has two halves.

* The language is definable with the order.  This is proved here in full: the
  formula is `Transducers.Exercises.sepForm`, a first-order formula of the
  logic `Transducers.MSO` of the project, and
  `Transducers.Exercises.sat_sepForm` is its correctness.
* The language is not definable with the successor only.  The book proves this
  with an Ehrenfeucht–Fraïssé argument on the two strings `aᵐ b aᵐ c aᵐ` and
  `aᵐ c aᵐ b aᵐ` for `m` much larger than `2ᵏ`.  Ehrenfeucht–Fraïssé games are
  not developed in this project, and the argument is taken as the explicit
  hypothesis `Transducers.Exercises.EFSuccSeparation`, which is exactly what the
  duplicator's strategy gives: for every `k` there are two strings, one in the
  language and one outside it, that satisfy the same formulas of quantifier
  rank at most `k` with successor only.  Non-definability follows from it in one
  step (`Transducers.Exercises.sepLang_not_foSuccDefinable`).

The logic with successor only is given its own syntax
`Transducers.Exercises.FOSucc`, with the successor and equality predicates in
place of the order.
-/

namespace Transducers.Exercises

open Transducers

/-! ## The alphabet and the language -/

/-- The three-letter alphabet of the separating language. -/
inductive L3 : Type
  | a : L3
  | b : L3
  | c : L3
  deriving DecidableEq

/-- The separating language: exactly one `b`, exactly one `c`, and the `b` before the `c`. -/
def sepLang : Set (List L3) :=
  {w | ∃ i j : ℕ, i < j ∧ w[i]? = some L3.b ∧ w[j]? = some L3.c ∧
        (∀ k, w[k]? = some L3.b → k = i) ∧ (∀ k, w[k]? = some L3.c → k = j)}

/-! ## The language is first-order definable with the order -/

/-- `∀ z (x (z) → z = x_i)`, written with the connectives of `MSO`. -/
def uniqF (x : L3) (i : ℕ) : MSO L3 :=
  MSO.not (MSO.exFO 2 (MSO.and (MSO.lab x 2) (MSO.not (MSO.and (MSO.le 2 i) (MSO.le i 2)))))

/-- The first-order formula, with the order, that defines `sepLang`. -/
def sepForm : MSO L3 :=
  MSO.exFO 0 (MSO.exFO 1 (MSO.and (MSO.lab L3.b 0) (MSO.and (MSO.lab L3.c 1)
    (MSO.and (MSO.le 0 1) (MSO.and (uniqF L3.b 0) (uniqF L3.c 1))))))

lemma isFO_sepForm : sepForm.IsFO := by
  simp [sepForm, uniqF, MSO.IsFO]

private lemma lt_length_of_getElem? {w : List L3} {k : ℕ} {x : L3} (h : w[k]? = some x) :
    k < w.length := by
  by_contra hk
  rw [List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

lemma sat_uniqF (w : List L3) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) (x : L3) {i : ℕ} (hi : i ≠ 2) :
    MSO.Sat w fo so (uniqF x i) ↔ ∀ k, w[k]? = some x → k = fo i := by
  constructor
  · intro h k hk
    by_contra hne
    refine h ⟨k, lt_length_of_getElem? hk, ?_, ?_⟩
    · show w[(Function.update fo 2 k) 2]? = some x
      rwa [Function.update_self]
    · show ¬ ((Function.update fo 2 k) 2 ≤ (Function.update fo 2 k) i ∧
        (Function.update fo 2 k) i ≤ (Function.update fo 2 k) 2)
      rw [Function.update_self, Function.update_of_ne hi]
      omega
  · rintro h ⟨p, hp, hlab, hne⟩
    have hlab' : w[p]? = some x := by
      have : w[(Function.update fo 2 p) 2]? = some x := hlab
      rwa [Function.update_self] at this
    have hp' : p = fo i := h p hlab'
    refine hne ?_
    show (Function.update fo 2 p) 2 ≤ (Function.update fo 2 p) i ∧
      (Function.update fo 2 p) i ≤ (Function.update fo 2 p) 2
    rw [Function.update_self, Function.update_of_ne hi, hp']
    exact ⟨le_rfl, le_rfl⟩

/-- **The separating language is first-order definable with the order.** -/
theorem sat_sepForm (w : List L3) (fo : ℕ → ℕ) (so : ℕ → Set ℕ) :
    MSO.Sat w fo so sepForm ↔ w ∈ sepLang := by
  constructor
  · rintro ⟨p, hp, q, hq, hb, hc, hle, hub, huc⟩
    set fo' := Function.update (Function.update fo 0 p) 1 q with hfo'
    have hp0 : fo' 0 = p := by
      rw [hfo', Function.update_of_ne (by norm_num), Function.update_self]
    have hq1 : fo' 1 = q := by rw [hfo', Function.update_self]
    have hb' : w[p]? = some L3.b := by
      have : w[fo' 0]? = some L3.b := hb
      rwa [hp0] at this
    have hc' : w[q]? = some L3.c := by
      have : w[fo' 1]? = some L3.c := hc
      rwa [hq1] at this
    have hle' : p ≤ q := by
      have : fo' 0 ≤ fo' 1 := hle
      rwa [hp0, hq1] at this
    have hub' : ∀ k, w[k]? = some L3.b → k = p := by
      have := (sat_uniqF w fo' so L3.b (i := 0) (by norm_num)).1 hub
      rwa [hp0] at this
    have huc' : ∀ k, w[k]? = some L3.c → k = q := by
      have := (sat_uniqF w fo' so L3.c (i := 1) (by norm_num)).1 huc
      rwa [hq1] at this
    have hne : p ≠ q := by
      rintro rfl
      rw [hb'] at hc'
      exact absurd hc' (by simp)
    exact ⟨p, q, lt_of_le_of_ne hle' hne, hb', hc', hub', huc'⟩
  · rintro ⟨i, j, hij, hb, hc, hub, huc⟩
    refine ⟨i, lt_length_of_getElem? hb, j, lt_length_of_getElem? hc, ?_⟩
    set fo' := Function.update (Function.update fo 0 i) 1 j with hfo'
    have hp0 : fo' 0 = i := by
      rw [hfo', Function.update_of_ne (by norm_num), Function.update_self]
    have hq1 : fo' 1 = j := by rw [hfo', Function.update_self]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show w[fo' 0]? = some L3.b
      rwa [hp0]
    · show w[fo' 1]? = some L3.c
      rwa [hq1]
    · show fo' 0 ≤ fo' 1
      rw [hp0, hq1]
      omega
    · refine (sat_uniqF w fo' so L3.b (i := 0) (by norm_num)).2 ?_
      rw [hp0]
      exact hub
    · refine (sat_uniqF w fo' so L3.c (i := 1) (by norm_num)).2 ?_
      rw [hq1]
      exact huc

theorem sepLang_foDefinable :
    ∃ φ : MSO L3, φ.IsFO ∧ ∀ (w : List L3) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat w fo so φ ↔ w ∈ sepLang :=
  ⟨sepForm, isFO_sepForm, sat_sepForm⟩

/-! ## First-order logic with the successor only -/

/-- Formulas of first-order logic on strings in which the only available predicates are the
successor relation and equality. -/
inductive FOSucc (A : Type) : Type
  /-- The successor test `x_i + 1 = x_j`. -/
  | succ : ℕ → ℕ → FOSucc A
  /-- The equality test `x_i = x_j`. -/
  | eq : ℕ → ℕ → FOSucc A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → FOSucc A
  /-- Negation. -/
  | not : FOSucc A → FOSucc A
  /-- Conjunction. -/
  | and : FOSucc A → FOSucc A → FOSucc A
  /-- Disjunction. -/
  | or : FOSucc A → FOSucc A → FOSucc A
  /-- Existential quantification. -/
  | ex : ℕ → FOSucc A → FOSucc A

namespace FOSucc

variable {A : Type}

/-- Satisfaction of a formula with successor only, under a valuation of the variables by
positions. -/
def Sat (w : List A) : (ℕ → ℕ) → FOSucc A → Prop
  | fo, succ i j => fo i + 1 = fo j
  | fo, eq i j => fo i = fo j
  | fo, lab a i => w[fo i]? = some a
  | fo, not φ => ¬ Sat w fo φ
  | fo, and φ ψ => Sat w fo φ ∧ Sat w fo ψ
  | fo, or φ ψ => Sat w fo φ ∨ Sat w fo ψ
  | fo, ex i φ => ∃ p < w.length, Sat w (Function.update fo i p) φ

/-- The quantifier rank of a formula with successor only. -/
def qrank : FOSucc A → ℕ
  | succ _ _ => 0
  | eq _ _ => 0
  | lab _ _ => 0
  | not φ => qrank φ
  | and φ ψ => max (qrank φ) (qrank ψ)
  | or φ ψ => max (qrank φ) (qrank ψ)
  | ex _ φ => qrank φ + 1

end FOSucc

/-- A language is definable in first-order logic with the successor only. -/
def FOSuccDefinable {A : Type} (L : Set (List A)) : Prop :=
  ∃ φ : FOSucc A, ∀ (w : List A) (fo : ℕ → ℕ), φ.Sat w fo ↔ w ∈ L

/-- **Assumed: the Ehrenfeucht–Fraïssé argument of the solution.**

For every number `k` of rounds there are two strings, one in `sepLang` and one outside it, which
satisfy the same formulas with successor only of quantifier rank at most `k`.

*Why this is true.*  This is the second half of the solution of `exer:fo-suc`.  Take
`w₁ = aᵐ b aᵐ c aᵐ` and `w₂ = aᵐ c aᵐ b aᵐ` with `m` much bigger than `2ᵏ`; the first is in the
language and the second is not.  In the `k`-round Ehrenfeucht–Fraïssé game for the signature with
the successor only, the duplicator wins: the invariant is that after `i` rounds the chosen
positions are matched so that two of them are at the same distance in both strings whenever that
distance is at most `2^{k-i}`, and are far apart in both strings otherwise.  The invariant can be
maintained because the two strings differ only in the order of `b` and `c`, which are at distance
more than `2ᵏ` from each other.  A duplicator win in `k` rounds means that the two strings satisfy
the same formulas of quantifier rank `k`.

*Why it is not available here.*  The equivalence between winning the `k`-round
Ehrenfeucht–Fraïssé game and satisfying the same formulas of quantifier rank `k` is the standard
Ehrenfeucht–Fraïssé theorem, and neither the games nor that theorem are developed in this
project.  Only this consequence of the argument is assumed; the other half of the exercise, that
the language *is* definable with the order, is proved. -/
def EFSuccSeparation : Prop :=
  ∀ k : ℕ, ∃ w₁ w₂ : List L3, w₁ ∈ sepLang ∧ w₂ ∉ sepLang ∧
    ∀ (φ : FOSucc L3) (fo : ℕ → ℕ), φ.qrank ≤ k → (φ.Sat w₁ fo ↔ φ.Sat w₂ fo)

/-- **The separating language is not definable with the successor only**, given the
Ehrenfeucht–Fraïssé argument of the book. -/
theorem sepLang_not_foSuccDefinable (h : EFSuccSeparation) : ¬ FOSuccDefinable sepLang := by
  rintro ⟨φ, hφ⟩
  obtain ⟨w₁, w₂, h₁, h₂, hEF⟩ := h φ.qrank
  exact h₂ ((hφ w₂ (fun _ => 0)).1 ((hEF φ (fun _ => 0) le_rfl).1 ((hφ w₁ (fun _ => 0)).2 h₁)))

/-- **Exercise `exer:fo-suc`.**  First-order logic with the successor only is strictly weaker
than first-order logic with the order: the language of the strings over `{a,b,c}` with exactly
one `b`, exactly one `c` and the `b` before the `c` is definable with the order and not with the
successor only.

The second half rests on the hypothesis `EFSuccSeparation`, the Ehrenfeucht–Fraïssé argument of
the book; see its docstring. -/
theorem fo_succ_strictly_weaker (h : EFSuccSeparation) :
    (∃ φ : MSO L3, φ.IsFO ∧ ∀ (w : List L3) (fo : ℕ → ℕ) (so : ℕ → Set ℕ),
      MSO.Sat w fo so φ ↔ w ∈ sepLang) ∧ ¬ FOSuccDefinable sepLang :=
  ⟨sepLang_foDefinable, sepLang_not_foSuccDefinable h⟩

end Transducers.Exercises
