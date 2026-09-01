/-
The exercises of the chapter *Logic* (`logic.tex`) of *Transducers*
(M. Bojańczyk) that were not part of the earlier passes.

The exercise `exer:mealy-as-restricted-mso-relabelling` of that chapter is
formalised in `RequestProject/Exercises/PartBC.lean`; this file adds
`exer:so-logic`.  Exercises are not numbered results of the book, so they are
recorded in `EXERCISES.md`, and they are referred to by their LaTeX label.

Full second-order logic over strings is not part of the main development, which
only has monadic second-order logic (`Transducers.MSO`), so the fragment that
the solution to `exer:so-logic` needs is defined here: monadic second-order
logic without set variables, extended with variables for *binary relations* on
positions, which is all that the solution quantifies over.
-/
import RequestProject.Exercises.PartBCAux

namespace Transducers
namespace Exercises

/-! ## Second-order logic -/

/-- Formulas of second-order logic over strings with letters in `A`, in the
fragment used by the solution to Exercise `exer:so-logic`: first-order
variables range over positions and second-order variables range over *binary
relations* on positions; both kinds of variables are named by natural numbers.
Monadic set variables are not included, since the exercise does not need them:
this fragment already contains first-order logic and already defines a
non-regular language. -/
inductive SO (A : Type) : Type
  /-- The order test `x_i ≤ x_j`. -/
  | le : ℕ → ℕ → SO A
  /-- The label test `a (x_i)`. -/
  | lab : A → ℕ → SO A
  /-- The membership test `(x_i, x_j) ∈ R_k`. -/
  | pair : ℕ → ℕ → ℕ → SO A
  /-- Negation. -/
  | neg : SO A → SO A
  /-- Conjunction. -/
  | conj : SO A → SO A → SO A
  /-- First-order existential quantification `∃ x_i`. -/
  | exFO : ℕ → SO A → SO A
  /-- Second-order existential quantification `∃ R_k` over binary relations. -/
  | exBin : ℕ → SO A → SO A

namespace SO

variable {A : Type}

/-- Satisfaction of a second-order formula in a string, under a valuation of
the first-order variables (by positions) and of the second-order variables (by
binary relations on positions). -/
def Sat (w : List A) : (ℕ → ℕ) → (ℕ → Set (ℕ × ℕ)) → SO A → Prop
  | fo, _, le i j => fo i ≤ fo j
  | fo, _, lab a i => w[fo i]? = some a
  | fo, bin, pair i j k => (fo i, fo j) ∈ bin k
  | fo, bin, neg φ => ¬ Sat w fo bin φ
  | fo, bin, conj φ ψ => Sat w fo bin φ ∧ Sat w fo bin ψ
  | fo, bin, exFO i φ => ∃ p < w.length, Sat w (Function.update fo i p) bin φ
  | fo, bin, exBin k φ =>
      ∃ R ⊆ {q : ℕ × ℕ | q.1 < w.length ∧ q.2 < w.length},
        Sat w fo (Function.update bin k R) φ

@[simp] lemma sat_le (w : List A) (fo bin) (i j) :
    Sat w fo bin (le i j : SO A) ↔ fo i ≤ fo j := Iff.rfl

@[simp] lemma sat_lab (w : List A) (fo bin) (a : A) (i) :
    Sat w fo bin (lab a i) ↔ w[fo i]? = some a := Iff.rfl

@[simp] lemma sat_pair (w : List A) (fo bin) (i j k) :
    Sat w fo bin (pair i j k : SO A) ↔ (fo i, fo j) ∈ bin k := Iff.rfl

@[simp] lemma sat_neg (w : List A) (fo bin) (φ : SO A) :
    Sat w fo bin φ.neg ↔ ¬ Sat w fo bin φ := Iff.rfl

@[simp] lemma sat_conj (w : List A) (fo bin) (φ ψ : SO A) :
    Sat w fo bin (φ.conj ψ) ↔ Sat w fo bin φ ∧ Sat w fo bin ψ := Iff.rfl

@[simp] lemma sat_exFO (w : List A) (fo bin) (i) (φ : SO A) :
    Sat w fo bin (exFO i φ) ↔ ∃ p < w.length, Sat w (Function.update fo i p) bin φ := Iff.rfl

@[simp] lemma sat_exBin (w : List A) (fo bin) (k) (φ : SO A) :
    Sat w fo bin (exBin k φ) ↔
      ∃ R ⊆ {q : ℕ × ℕ | q.1 < w.length ∧ q.2 < w.length},
        Sat w fo (Function.update bin k R) φ := Iff.rfl

/-- Disjunction, as usual. -/
def disj (φ ψ : SO A) : SO A := neg (conj (neg φ) (neg ψ))

/-- Implication, as usual. -/
def imp (φ ψ : SO A) : SO A := disj (neg φ) ψ

/-- First-order universal quantification, as usual. -/
def allFO (i : ℕ) (φ : SO A) : SO A := neg (exFO i (neg φ))

/-- Equality of two first-order variables. -/
def eqFO (i j : ℕ) : SO A := conj (le i j) (le j i)

@[simp] lemma sat_disj (w : List A) (fo bin) (φ ψ : SO A) :
    Sat w fo bin (disj φ ψ) ↔ Sat w fo bin φ ∨ Sat w fo bin ψ := by
  simp [disj, or_iff_not_and_not]

@[simp] lemma sat_imp (w : List A) (fo bin) (φ ψ : SO A) :
    Sat w fo bin (imp φ ψ) ↔ (Sat w fo bin φ → Sat w fo bin ψ) := by
  simp [imp, imp_iff_not_or]

@[simp] lemma sat_allFO (w : List A) (fo bin) (i) (φ : SO A) :
    Sat w fo bin (allFO i φ) ↔ ∀ p < w.length, Sat w (Function.update fo i p) bin φ := by
  simp [allFO]

@[simp] lemma sat_eqFO (w : List A) (fo bin) (i j) :
    Sat w fo bin (eqFO i j : SO A) ↔ fo i = fo j := by
  simp [eqFO]
  omega

/-- The language defined by a formula, evaluated under the trivial valuation.
For a sentence this is the language of the sentence. -/
def lang (φ : SO A) : Language A := {w | Sat w (fun _ => 0) (fun _ => ∅) φ}

end SO

/-! ### Exercise `exer:so-logic` -/

open SO

/-- Every position labelled `true` comes strictly after every position labelled
`false`; the letter `false` plays the role of the book's `a`, and `true` the
role of its `b`. -/
def sortedForm : SO Bool :=
  allFO 0 (allFO 1 (imp (conj (lab true 0) (lab false 1)) (neg (le 0 1))))

/-- There is a binary relation on positions which is the graph of a bijection
between the `false`-positions and the `true`-positions. -/
def bijForm : SO Bool :=
  exBin 0 (conj (conj (conj (conj
    (allFO 0 (allFO 1 (imp (pair 0 1 0) (conj (lab false 0) (lab true 1)))))
    (allFO 0 (imp (lab false 0) (exFO 1 (pair 0 1 0)))))
    (allFO 1 (imp (lab true 1) (exFO 0 (pair 0 1 0)))))
    (allFO 0 (allFO 1 (allFO 2 (imp (conj (pair 0 1 0) (pair 0 2 0)) (eqFO 1 2))))))
    (allFO 0 (allFO 1 (allFO 2 (imp (conj (pair 0 2 0) (pair 1 2 0)) (eqFO 0 1))))))

/-- The second-order sentence of the solution to Exercise `exer:so-logic`. -/
def eqReplicateForm : SO Bool := conj sortedForm bijForm

lemma sat_sortedForm (w : List Bool) (fo : ℕ → ℕ) (bin : ℕ → Set (ℕ × ℕ)) :
    Sat w fo bin sortedForm ↔
      ∀ x < w.length, ∀ y < w.length, w[x]? = some true → w[y]? = some false → y < x := by
  simp only [sortedForm, sat_allFO, sat_imp, sat_conj, sat_neg, sat_lab, sat_le,
    Function.update_apply]
  norm_num

lemma sat_bijForm (w : List Bool) (fo : ℕ → ℕ) (bin : ℕ → Set (ℕ × ℕ)) :
    Sat w fo bin bijForm ↔ ∃ R : Set (ℕ × ℕ),
      (∀ a b, (a, b) ∈ R → a < w.length ∧ b < w.length) ∧
      (∀ p q, (p, q) ∈ R → w[p]? = some false ∧ w[q]? = some true) ∧
      (∀ p < w.length, w[p]? = some false → ∃ q, (p, q) ∈ R) ∧
      (∀ q < w.length, w[q]? = some true → ∃ p, (p, q) ∈ R) ∧
      (∀ p q r, (p, q) ∈ R → (p, r) ∈ R → q = r) ∧
      (∀ p q r, (p, r) ∈ R → (q, r) ∈ R → p = q) := by
  simp only [bijForm, sat_exBin, sat_conj, sat_allFO, sat_imp, sat_pair, sat_exFO, sat_lab,
    sat_eqFO, Function.update_apply]
  norm_num
  constructor
  · rintro ⟨R, hRsub, ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    have hb : ∀ a b, (a, b) ∈ R → a < w.length ∧ b < w.length := by
      intro a b hab; exact hRsub hab
    refine ⟨R, hb, ?_, ?_, ?_, ?_, ?_⟩
    · intro p q hpq
      obtain ⟨hp, hq⟩ := hb p q hpq
      exact h1 p hp q hq hpq
    · intro p hp hpf
      obtain ⟨q, _, hq⟩ := h2 p hp hpf
      exact ⟨q, hq⟩
    · intro q hq hqt
      obtain ⟨p, _, hp⟩ := h3 q hq hqt
      exact ⟨p, hp⟩
    · intro p q r hpq hpr
      obtain ⟨hp, hqq⟩ := hb p q hpq
      obtain ⟨_, hrr⟩ := hb p r hpr
      exact h4 p hp q hqq r hrr hpq hpr
    · intro p q r hpr hqr
      obtain ⟨hp, hrr⟩ := hb p r hpr
      obtain ⟨hq, _⟩ := hb q r hqr
      exact h5 p hp q hq r hrr hpr hqr
  · rintro ⟨R, hb, h1, h2, h3, h4, h5⟩
    refine ⟨R, fun z hz => hb z.1 z.2 hz, ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro p _ q _ hpq; exact h1 p q hpq
    · intro p hp hpf
      obtain ⟨q, hq⟩ := h2 p hp hpf
      exact ⟨q, (hb p q hq).2, hq⟩
    · intro q hq hqt
      obtain ⟨p, hp⟩ := h3 q hq hqt
      exact ⟨p, (hb p q hp).1, hp⟩
    · intro p _ q _ r _ hpq hpr; exact h4 p q r hpq hpr
    · intro p _ q _ r _ hpr hqr; exact h5 p q r hpr hqr

/-- The letters of `falseⁿ trueᵐ`. -/
lemma getElem?_replicate_append (n m i : ℕ) :
    (List.replicate n false ++ List.replicate m true)[i]? =
      if i < n then some false else if i < n + m then some true else none := by
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simpa using h)]
    simp [h]
  · rw [List.getElem?_append_right (by simpa using h)]
    simp only [List.length_replicate, List.getElem?_replicate]
    rcases lt_or_ge i (n + m) with h' | h'
    · simp [h', Nat.not_lt.2 h, show i - n < m by omega]
    · simp [Nat.not_lt.2 h, Nat.not_lt.2 h', show ¬ i - n < m by omega]

/-- A string over `{false, true}` in which every `true` comes after every
`false` is of the form `falseᵖ trueᵍ`. -/
lemma sorted_bool_eq_replicate : ∀ w : List Bool,
    (∀ x < w.length, ∀ y < w.length, w[x]? = some true → w[y]? = some false → y < x) →
      w = List.replicate (w.count false) false ++ List.replicate (w.count true) true := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons a w ih =>
    intro h
    have hw : ∀ x < w.length, ∀ y < w.length,
        w[x]? = some true → w[y]? = some false → y < x := by
      intro x hx y hy hxt hyf
      have := h (x + 1) (by simpa using hx) (y + 1) (by simpa using hy) (by simpa using hxt)
        (by simpa using hyf)
      omega
    have hrec := ih hw
    cases a with
    | false =>
      rw [List.count_cons_self, List.count_cons_of_ne (by simp)]
      rw [List.replicate_succ, List.cons_append, ← hrec]
    | true =>
      have hnf : w.count false = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        obtain ⟨y, hy, hyf⟩ := List.getElem_of_mem hmem
        have := h 0 (by simp) (y + 1) (by simpa using hy) (by simp)
          (by simp [List.getElem?_eq_getElem hy, hyf])
        omega
      rw [List.count_cons_of_ne (by simp), List.count_cons_self, hnf]
      rw [List.replicate_succ]
      rw [hnf] at hrec
      simpa using congrArg (fun l => true :: l) hrec

theorem lang_eqReplicateForm :
    SO.lang eqReplicateForm =
      {w : List Bool | ∃ n, w = List.replicate n false ++ List.replicate n true} := by
  classical
  ext w
  simp only [SO.lang, eqReplicateForm, sat_conj, sat_sortedForm, sat_bijForm]
  constructor
  · rintro ⟨hsort, R, hb, h1, h2, h3, h4, h5⟩
    set p := w.count false with hp
    set q := w.count true with hq
    have hform : w = List.replicate p false ++ List.replicate q true :=
      sorted_bool_eq_replicate w hsort
    have hlen : w.length = p + q := by rw [hform]; simp
    have hget : ∀ i, w[i]? = if i < p then some false else if i < p + q then some true else none := by
      intro i; rw [hform]; exact getElem?_replicate_append p q i
    -- the chosen partner of a position
    set g : ℕ → ℕ := fun a => if h : ∃ b, (a, b) ∈ R then h.choose else 0 with hgdef
    have hgmem : ∀ a, (∃ b, (a, b) ∈ R) → (a, g a) ∈ R := by
      intro a ha
      simp only [hgdef, dif_pos ha]
      exact ha.choose_spec
    have hcard : (Finset.range p).card = (Finset.Ico p (p + q)).card := by
      refine Finset.card_bij (fun a _ => g a) ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_range] at ha
        have haf : w[a]? = some false := by rw [hget]; simp [ha]
        have hex : ∃ b, (a, b) ∈ R := h2 a (by omega) haf
        have hmem := hgmem a hex
        have hbound := hb a (g a) hmem
        have hgt : w[g a]? = some true := (h1 a (g a) hmem).2
        rw [hget] at hgt
        by_cases hlt : g a < p
        · simp [hlt] at hgt
        · simp only [Finset.mem_Ico]
          have : g a < w.length := hbound.2
          omega
      · intro a ha b hb' hab
        simp only [Finset.mem_range] at ha hb'
        have haf : w[a]? = some false := by rw [hget]; simp [ha]
        have hbf : w[b]? = some false := by rw [hget]; simp [hb']
        have hga := hgmem a (h2 a (by omega) haf)
        have hgb := hgmem b (h2 b (by omega) hbf)
        have hab' : g a = g b := hab
        rw [hab'] at hga
        exact h5 a b (g b) hga hgb
      · intro b hbm
        simp only [Finset.mem_Ico] at hbm
        have hbt : w[b]? = some true := by
          rw [hget]; simp [Nat.not_lt.2 hbm.1, hbm.2]
        obtain ⟨a, hab⟩ := h3 b (by omega) hbt
        have haf : w[a]? = some false := (h1 a b hab).1
        have hap : a < p := by
          rw [hget] at haf
          by_cases hlt : a < p
          · exact hlt
          · simp [hlt] at haf
        refine ⟨a, by simp [hap], ?_⟩
        have hga := hgmem a ⟨b, hab⟩
        exact h4 a (g a) b hga hab
    simp only [Nat.card_Ico, Finset.card_range] at hcard
    have : p = q := by omega
    exact ⟨p, by rw [hform, this]⟩
  · rintro ⟨n, rfl⟩
    have hget : ∀ i, (List.replicate n false ++ List.replicate n true)[i]? =
        if i < n then some false else if i < n + n then some true else none :=
      getElem?_replicate_append n n
    have hlen : (List.replicate n false ++ List.replicate n true).length = n + n := by simp
    refine ⟨?_, {z | z.1 < n ∧ z.2 = n + z.1}, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy hxt hyf
      rw [hlen] at hx hy
      rw [hget] at hxt hyf
      by_cases h : x < n
      · simp [h] at hxt
      · simp only [h, if_false] at hxt
        by_cases h' : y < n
        · omega
        · simp [h'] at hyf
    · rintro x y ⟨hx, hy⟩
      simp only [hlen]
      exact ⟨by omega, by omega⟩
    · rintro x y ⟨hx, hy⟩
      simp only [hget]
      constructor
      · simp [hx]
      · simp [Nat.not_lt.2 (by omega : n ≤ y), show y < n + n by omega]
    · intro x hx hxf
      rw [hlen] at hx
      rw [hget] at hxf
      by_cases h : x < n
      · exact ⟨n + x, h, rfl⟩
      · simp [h] at hxf
    · intro y hy hyt
      rw [hlen] at hy
      rw [hget] at hyt
      by_cases h : y < n
      · simp [h] at hyt
      · exact ⟨y - n, by omega, by omega⟩
    · rintro x y z ⟨hx, hy⟩ ⟨_, hz⟩
      omega
    · rintro x y z ⟨hx, hz⟩ ⟨hy, hz'⟩
      omega

/-- **Exercise `exer:so-logic`.**  Second-order logic can define non-regular
languages. -/
theorem exists_SO_lang_not_isRegular : ∃ φ : SO Bool, ¬ (SO.lang φ).IsRegular := by
  refine ⟨eqReplicateForm, ?_⟩
  rw [lang_eqReplicateForm]
  exact not_isRegular_eqReplicate

end Exercises
end Transducers
