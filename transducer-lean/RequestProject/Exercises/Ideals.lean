/-
The four remaining exercises of `rational-functions.tex` of *Transducers* (M. Bojańczyk) on the
ideals of rational functions: `exer:full-ideal`, `exer:polynomial-ideals`, `exer:all-ideals` and
`exer:decide-same-ideal`.  They continue the series that begins with `exer:some-ideals` and
`exer:finite-range-ideals`, which are formalised in `RequestProject/Exercises/PartBC.lean`.
-/
import RequestProject.Exercises.PartBC
import RequestProject.Exercises.IdealsOmega
import RequestProject.Exercises.IdealsPoly

/-!
# The ideals of rational functions

An *ideal* is a class `I` of rational functions with `I = Rational · I · Rational`
(`Transducers.Exercises.IsIdeal`, Exercise `exer:some-ideals`).  Two families of ideals are already
known to the project: the functions whose range has at most `k` elements
(`Transducers.Exercises.RangeAtMost`) and the functions with `O(n^k)` outputs
(`Transducers.Exercises.OutputsPoly`), and an ideal all of whose functions have a finite range is
one of them (`Transducers.Exercises.finite_range_ideal_classification`, Exercise
`exer:finite-range-ideals`).  This file finishes the series:

* `full_ideal_iff` — Exercise `exer:full-ideal`: an ideal contains all rational functions exactly
  when it contains a function with super-polynomially many outputs, whose range is then a regular
  language of super-polynomial growth, as the exercise says;
* `polynomial_ideals` — Exercise `exer:polynomial-ideals`: an ideal that contains a function with
  `Ω(n^k)` outputs contains every rational function with `O(n^k)` outputs;
* `all_ideals` — Exercise `exer:all-ideals`: every ideal is one of `RangeAtMost k`,
  `OutputsPoly k`, the functions with polynomially many outputs, or all rational functions;
* `sameIdeal_iff` — Exercise `exer:decide-same-ideal`: two rational functions belong to the same
  ideals exactly when their ranges are both finite and of the same size, or both infinite and of
  the same polynomial degree.  This is the reduction of the decision problem to the computation of
  that invariant, which is what the author's solution consists of.

## How growth is measured

The book measures the growth of a rational function by the growth rate of its *range*: the number
of strings of length at most `n` that the function outputs.  This project measures it, since
Exercise `exer:some-ideals`, by the number of *outputs on inputs of length at most `n`*
(`Transducers.Exercises.outCount`), and that is the reading used here as well.  The reason is that
it is in this reading that the classes are ideals — that is what
`Transducers.Exercises.isIdeal_outputsPoly` proves — and the statements below quantify over
ideals, so the two readings must not be mixed.  The divergence is recorded in `EXERCISES.md`.

## What is proved

The solutions of these four exercises rest on an analysis of the loops of an automaton — the
patterns of Exercise `exer:polynomial-image-growth-decidable` — combined with the Uniformisation
Lemma, and the book itself carries it out only in outline ("using a similar analysis", "this can be
proved by analysing the structure of strongly connected components").  That analysis is carried out
for an arbitrary deterministic automaton in `RequestProject/Exercises/RegularGrowth.lean` and
`RequestProject/Exercises/PatternCover.lean`, and transported to rational functions in
`RequestProject/Exercises/RationalGrowth.lean`, `RequestProject/Exercises/IdealsOmega.lean` and
`RequestProject/Exercises/IdealsPoly.lean`.  Nothing in this file is assumed; the four consequences
of the loop analysis that the solutions use are all theorems:

* `IdentityFromSuperPolyOutputs` — a rational function with super-polynomially many outputs has the
  identity of `{0,1}*` among its rational pre- and post-compositions; **proved**, from
  `Transducers.Exercises.exists_rational_bool_identity_of_superPoly`;
* `OutputsGrowthDichotomy` — the number of outputs of a rational function is either
  super-polynomial or `Θ(n^k)` for some `k`; this is the gap in the growth rates of regular
  languages, which the author's solution to `exer:all-ideals` uses silently; **proved**, from
  `Transducers.Exercises.rationalFun_growth_dichotomy`.

* `SortedFromOmegaOutputs` — a rational function with `Ω(n^k)` outputs has the sorted-identity
  function `sortedFun k` among them; **proved**, from
  `Transducers.Exercises.exists_rational_sorted_of_omega`;
* `FactorThroughSortedOfOutputsPolyPos` — a rational function with `O(n^k)` outputs, `k ≥ 1`, is a
  rational pre- and post-composition of `sortedFun k`; **proved**, from
  `Transducers.Exercises.exists_rational_factor_through_sorted`.

## Where the formalisation diverges from the book

The last statement is **false at `k = 0`**, in the form in which the author states it: over the
empty alphabet there is only the empty word, so a factorisation through `sortedFun 0` makes the
function constant, whereas `O(n^0)` outputs only means a finite range.  The faithful rendering is
kept, as the `def FactorThroughSortedOfOutputsPoly`, and refuted in
`not_factorThroughSortedOfOutputsPoly`.

Exercise `exer:polynomial-ideals` inherits the same failure at `k = 0`, where `Ω(n^0)` outputs is
no condition at all and `O(n^0)` outputs is a finite range: `polynomial_ideals_false_at_zero`
refutes it, and `polynomial_ideals` is stated with the extra hypothesis `1 ≤ k`.  The two other
exercises are unaffected: in the cases of `all_ideals` in which `polynomial_ideals` is used, the
ideal has a member of infinite range, whose level is therefore at least `1`
(`one_le_of_not_finite_range`).  Both divergences are recorded in `EXERCISES.md`.

Everything else is proved here: `exer:full-ideal` needs the encoding of an arbitrary alphabet by
blocks over `{0,1}` for its interesting direction and a function with super-polynomially many
outputs for the other one, `exer:all-ideals` is the case analysis of the book over the ideals, and
`exer:decide-same-ideal` is proved from that classification in one direction and from the two
families of ideals in the other.
-/

namespace Transducers.Exercises

/-! ### Counting the outputs -/

/-- The number of outputs of `f` on inputs of length at most `n`.  This is the growth rate that
`Transducers.Exercises.OutputsPoly` — the second family of ideals of Exercise `exer:some-ideals` —
is stated with; see the header of this file. -/
noncomputable def outCount {A B : Type} (f : List A → List B) (n : ℕ) : ℕ :=
  (f '' {w : List A | w.length ≤ n}).ncard

lemma outputsPoly_iff {A B : Type} (k : ℕ) (f : List A → List B) :
    OutputsPoly k A B f ↔ IsRationalFun f ∧ ∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k :=
  Iff.rfl

/-- `f` has super-polynomially many outputs: for no `k` is the number of outputs on inputs of
length at most `n` bounded by a constant times `(n+1)^k`. -/
def SuperPolyOutputs {A B : Type} (f : List A → List B) : Prop :=
  ∀ k C : ℕ, ∃ n, C * (n + 1) ^ k < outCount f n

/-- `f` has `Ω(n^k)` outputs. -/
def OmegaOutputs {A B : Type} (f : List A → List B) (k : ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → (n + 1) ^ k ≤ c * outCount f n

/-- The rational functions with polynomially many outputs: the union of the ideals
`OutputsPoly k`. -/
def OutputsPolySome : ∀ (A B : Type), (List A → List B) → Prop := fun _ _ f =>
  IsRationalFun f ∧ ∃ k C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k

/-- The class of all rational functions, the largest ideal. -/
def AllRationalFuns : ∀ (A B : Type), (List A → List B) → Prop := fun _ _ f => IsRationalFun f

lemma superPolyOutputs_iff {A B : Type} (f : List A → List B) :
    SuperPolyOutputs f ↔ ∀ k : ℕ, ¬ ∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k := by
  constructor
  · rintro h k ⟨C, hC⟩
    obtain ⟨n, hn⟩ := h k C
    exact absurd (hC n) (by omega)
  · intro h k C
    have hk := h k
    push_neg at hk
    obtain ⟨n, hn⟩ := hk C
    exact ⟨n, by omega⟩

lemma outCount_mono_pow {A B : Type} {f : List A → List B} {j k C : ℕ} (hjk : j ≤ k)
    (h : ∀ n, outCount f n ≤ C * (n + 1) ^ j) : ∀ n, outCount f n ≤ C * (n + 1) ^ k := fun n =>
  le_trans (h n) (Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) hjk))

/-- A function with a finite range has boundedly many outputs, so it lies in every
`OutputsPoly k`. -/
lemma outputsPoly_of_finite_range {A B : Type} [Finite A] {f : List A → List B}
    (hf : IsRationalFun f) (hfin : (Set.range f).Finite) (k : ℕ) : OutputsPoly k A B f := by
  refine ⟨hf, (Set.range f).ncard, fun n => ?_⟩
  have hsub : f '' {w : List A | w.length ≤ n} ⊆ Set.range f := by
    rintro y ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  calc outCount f n ≤ (Set.range f).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ (Set.range f).ncard * (n + 1) ^ k := Nat.le_mul_of_pos_right _ (by positivity)

/-- Every polynomial is eventually beaten by `2^n`. -/
lemma exists_lt_two_pow (k C : ℕ) : ∃ n : ℕ, C * (n + 1) ^ k < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt k (r := 2) (by norm_num)
  have h2 : Filter.Tendsto
      (fun n : ℕ => ((C : ℝ) * 2 ^ k) * ((n : ℝ) ^ k / 2 ^ n)) Filter.atTop (nhds 0) := by
    simpa using h.const_mul ((C : ℝ) * 2 ^ k)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ((C : ℝ) * 2 ^ k) * ((n : ℝ) ^ k / 2 ^ n) < 1 :=
    h2.eventually_lt_const (by norm_num)
  obtain ⟨n, hn, hn1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hpos : (0 : ℝ) < 2 ^ (n : ℕ) := by positivity
  have hB : ((C : ℝ) * 2 ^ k) * (n : ℝ) ^ k < 2 ^ (n : ℕ) := by
    rw [← mul_div_assoc] at hn
    exact (div_lt_one hpos).1 hn
  have h1 : ((n : ℝ) + 1) ^ k ≤ (2 * (n : ℝ)) ^ k := by
    have hle : (n : ℝ) + 1 ≤ 2 * n := by linarith
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    gcongr
  have hA : (C : ℝ) * ((n : ℝ) + 1) ^ k ≤ ((C : ℝ) * 2 ^ k) * (n : ℝ) ^ k := by
    calc (C : ℝ) * ((n : ℝ) + 1) ^ k ≤ (C : ℝ) * (2 * (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((C : ℝ) * 2 ^ k) * (n : ℝ) ^ k := by rw [mul_pow]; ring
  have hlt : (C : ℝ) * ((n : ℝ) + 1) ^ k < 2 ^ (n : ℕ) := lt_of_le_of_lt hA hB
  refine ⟨n, ?_⟩
  have hcast : ((C * (n + 1) ^ k : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by push_cast; exact hlt
  exact_mod_cast hcast

/-! ### The sorted-identity functions

The function `f_k` of the author's solution — `Transducers.Exercises.sortedFun`, the identity on
the sorted strings of `a_1^* a_2^* ⋯ a_k^*` and the empty string elsewhere — is defined in
`RequestProject/Exercises/SortedPattern.lean`, together with the proof that it is rational. -/

/-! ### The consequences of the loop analysis, and the two remaining hypotheses -/

/-- **From super-polynomially many outputs to the identity.**  If a rational function `f` has
super-polynomially many outputs, then the identity of `{0,1}*` is a rational pre-composition and
post-composition of `f`.

This is the second paragraph of the author's solution to Exercise `exer:full-ideal`: the range of
`f` is a regular language of super-polynomial growth, so by the loop analysis of Exercise
`exer:polynomial-image-growth-decidable` an automaton for it has two loops with different output
strings of the same length, which gives an injective encoding of `{0,1}*` inside the range; the
Uniformisation Lemma turns the inverse of `f` into a rational function that produces, for a string
of the range, an input of `f` mapped to it, and a rational function reads the encoded bits back.
The loop analysis is carried out in `RequestProject/Exercises/RegularGrowth.lean` and transported
to rational functions in `RequestProject/Exercises/RationalGrowth.lean`; this statement is
`Transducers.Exercises.exists_rational_bool_identity_of_superPoly`. -/
theorem IdentityFromSuperPolyOutputs :
    ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B), IsRationalFun f →
      SuperPolyOutputs f →
        ∃ (g : List Bool → List A) (h : List B → List Bool),
          IsRationalFun g ∧ IsRationalFun h ∧ ∀ u : List Bool, h (f (g u)) = u :=
  fun _ _ _ _ _ hf hsuper => exists_rational_bool_identity_of_superPoly hf hsuper

/-- **From `Ω(n^k)` outputs to the sorted identity.**  If a rational function `f` has `Ω(n^k)`
outputs, then `sortedFun k` is a rational pre-composition and post-composition of `f`.

This is the second step of the author's solution to Exercise `exer:polynomial-ideals`: the range of
`f` contains a `k`-pattern, and the same argument as in `exer:full-ideal` — the Uniformisation
Lemma and a rational decoding of the pattern — turns that pattern into the function `f_k`.  The
`k`-pattern is extracted from the loop analysis in
`RequestProject/Exercises/ChainWords.lean`, and the two rational functions are built in
`RequestProject/Exercises/IdealsOmega.lean`; this statement is
`Transducers.Exercises.exists_rational_sorted_of_omega`. -/
theorem SortedFromOmegaOutputs :
    ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B) (k : ℕ), IsRationalFun f →
      OmegaOutputs f k →
        ∃ (g : List (Fin k) → List A) (h : List B → List (Fin k)),
          IsRationalFun g ∧ IsRationalFun h ∧ ∀ u : List (Fin k), h (f (g u)) = sortedFun k u :=
  fun _ _ _ _ _ k hf ⟨_, hc, _, hΩ⟩ => exists_rational_sorted_of_omega hf k hc hΩ

/-- **`O(n^k)` outputs factor through the sorted identity**, as the author's solution to Exercise
`exer:polynomial-ideals` states it: a rational function with `O(n^k)` outputs is a rational
pre-composition and post-composition of `sortedFun k`.

This statement is **false at `k = 0`** — see `not_factorThroughSortedOfOutputsPoly` — because the
only word over the empty alphabet is the empty one, so a factorisation through `sortedFun 0` forces
the function to be constant, while a rational function with `O(1)` outputs need only have a finite
range.  It is kept here as the faithful rendering of what the author writes; the corrected version,
with `k ≥ 1`, is `FactorThroughSortedOfOutputsPolyPos` below and is a theorem of the project. -/
def FactorThroughSortedOfOutputsPoly : Prop :=
  ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B) (k : ℕ), IsRationalFun f →
    (∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k) →
      ∃ (g : List A → List (Fin k)) (h : List (Fin k) → List B),
        IsRationalFun g ∧ IsRationalFun h ∧ ∀ w : List A, h (sortedFun k (g w)) = f w

/-- Every word over the empty alphabet is empty. -/
lemma list_fin_zero_eq_nil (l : List (Fin 0)) : l = [] := by
  cases l with
  | nil => rfl
  | cons a _ => exact a.elim0

/-- **The factorisation statement is false at `k = 0`.**  `Transducers.Exercises.firstLetterFun`
is rational and has two outputs in all, hence `O(n^0)` of them, but it is not constant, while
every function of the form `w ↦ h (sortedFun 0 (g w))` is. -/
theorem not_factorThroughSortedOfOutputsPoly : ¬ FactorThroughSortedOfOutputsPoly := by
  intro hpoly
  obtain ⟨g, h, -, -, hgh⟩ := hpoly Bool Bool firstLetterFun 0 isRationalFun_firstLetterFun
    ⟨2, fun n => outCount_firstLetterFun n⟩
  refine firstLetterFun_not_const ?_
  rw [← hgh [], ← hgh [true], list_fin_zero_eq_nil (g []), list_fin_zero_eq_nil (g [true])]

/-- **`O(n^k)` outputs factor through the sorted identity, for `k ≥ 1`.**  This is the corrected
form of `FactorThroughSortedOfOutputsPoly`, and it is proved: it is the last step of the author's
solution to Exercise `exer:polynomial-ideals`, the one he describes as "analysing the structure of
strongly connected components in the automaton that computes a rational function whose range has
growth `O(n^k)`".

The analysis is carried out in `RequestProject/Exercises/PatternCover.lean` (every word accepted by
an automaton with no ambiguous cycle and no chain of `k+1` loops is a word of one of finitely many
`k`-patterns), realised rationally in `RequestProject/Exercises/PatternCoverRat.lean` and assembled
in `RequestProject/Exercises/IdealsPoly.lean`; this statement is
`Transducers.Exercises.exists_rational_factor_through_sorted`. -/
theorem FactorThroughSortedOfOutputsPolyPos :
    ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B) (k : ℕ), 1 ≤ k → IsRationalFun f →
      (∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k) →
        ∃ (g : List A → List (Fin k)) (h : List (Fin k) → List B),
          IsRationalFun g ∧ IsRationalFun h ∧ ∀ w : List A, h (sortedFun k (g w)) = f w :=
  fun _ _ _ _ _ _ hk hf hC => exists_rational_factor_through_sorted hf hk hC

/-- **The growth of a rational function has no gaps.**  The number of outputs of a rational
function on inputs of length at most `n` is either super-polynomial, or `Θ(n^k)` for some `k`.

This is the gap theorem for the growth rates of regular languages, which the author's solution to
Exercise `exer:all-ideals` uses when it speaks of "the largest `k` such that some function in the
ideal has range of growth `Ω(n^k)`".  It comes from the same loop analysis as the statement
above; it is `Transducers.Exercises.rationalFun_growth_dichotomy`. -/
theorem OutputsGrowthDichotomy :
    ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B), IsRationalFun f →
      SuperPolyOutputs f ∨
        ∃ k : ℕ, (∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k) ∧ OmegaOutputs f k :=
  fun _ _ _ _ _ hf => rationalFun_growth_dichotomy hf

/-! ### Exercise `exer:full-ideal` -/

/-- The identity of `{0,1}*` is a rational function. -/
lemma isRationalFun_id {A : Type} [Finite A] : IsRationalFun (id : List A → List A) :=
  isRationalRel_congr (isRationalFun_map (id : A → A)) (fun w v => by simp)

/-- The identity of `{0,1}*` has super-polynomially many outputs: on the inputs of length at most
`n` it already takes at least `2^n` values, and `2^n` outgrows every polynomial. -/
lemma superPolyOutputs_id_bool : SuperPolyOutputs (id : List Bool → List Bool) := by
  have hpow : ∀ n : ℕ, 2 ^ n ≤ outCount (id : List Bool → List Bool) n := by
    intro n
    have hinj : Function.Injective (fun v : Fin n → Bool => List.ofFn v) :=
      fun _ _ h => List.ofFn_injective h
    have hsub : Set.range (fun v : Fin n → Bool => List.ofFn v)
        ⊆ id '' {w : List Bool | w.length ≤ n} := by
      rintro w ⟨v, rfl⟩
      exact ⟨List.ofFn v, by simp, rfl⟩
    have hfin : (id '' {w : List Bool | w.length ≤ n}).Finite :=
      (finite_lists_length_le n).image _
    have hcard : (Set.range (fun v : Fin n → Bool => List.ofFn v)).ncard = 2 ^ n := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
      simp [Nat.card_eq_fintype_card]
    calc 2 ^ n = (Set.range (fun v : Fin n → Bool => List.ofFn v)).ncard := hcard.symm
      _ ≤ outCount (id : List Bool → List Bool) n := Set.ncard_le_ncard hsub hfin
  intro k C
  obtain ⟨n, hn⟩ := exists_lt_two_pow k C
  exact ⟨n, lt_of_lt_of_le hn (hpow n)⟩

/-- **Exercise `exer:full-ideal`.**  An ideal contains all rational functions if and only if it
contains some function whose range is a regular language of super-polynomial growth.

The growth is measured as everywhere in this file; see the header.  The direction from left to
right is witnessed by the identity of `{0,1}*`, whose range is the regular language of all strings
and has `2^n` elements of length at most `n`.  The other direction is the author's argument: the
theorem `IdentityFromSuperPolyOutputs` produces the identity of `{0,1}*` inside the ideal, and
every rational function `u` factors through it, because an arbitrary finite alphabet is encoded by
blocks over `{0,1}` (`Transducers.Exercises.code` and `Transducers.Exercises.decBlock`). -/
theorem full_ideal_iff
    {I : ∀ (A B : Type), (List A → List B) → Prop} (hI : IsIdeal I) :
    (∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B), IsRationalFun f → I A B f) ↔
      ∃ (A B : Type) (_ : Finite A) (_ : Finite B) (f : List A → List B),
        I A B f ∧ Language.IsRegular ({v | ∃ w, v = f w} : Language B) ∧ SuperPolyOutputs f := by
  constructor
  · intro hall
    exact ⟨Bool, Bool, inferInstance, inferInstance, id, hall Bool Bool id isRationalFun_id,
      rationalRel_range_isRegular isRationalFun_id, superPolyOutputs_id_bool⟩
  · rintro ⟨A, B, iA, iB, f, hfI, -, hsuper⟩ C D _ _ u hu
    haveI := iA; haveI := iB
    obtain ⟨g, h, hg, hh, hgh⟩ :=
      IdentityFromSuperPolyOutputs A B f (hI.1 A B f hfI) hsuper
    have hpre : IsRationalFun (fun w : List C => g (homOf TwoLetter.code w)) :=
      isRationalFun_comp (isRationalFun_homOf TwoLetter.code) hg
    have hdec : IsRationalFun (fun b : List Bool => u (TwoLetter.decBlock C b)) :=
      isRationalFun_comp TwoLetter.isRationalFun_decBlock hu
    have hpost : IsRationalFun (fun v : List B => u (TwoLetter.decBlock C (h v))) :=
      isRationalFun_comp (f := h) (g := fun b : List Bool => u (TwoLetter.decBlock C b)) hh hdec
    have hmem := hI.2 C A B D (fun w : List C => g (homOf TwoLetter.code w)) f
      (fun v : List B => u (TwoLetter.decBlock C (h v))) hpre hfI hpost
    have heq : ((fun v : List B => u (TwoLetter.decBlock C (h v))) ∘ f ∘
        fun w : List C => g (homOf TwoLetter.code w)) = u := by
      funext w
      simp only [Function.comp_apply]
      rw [hgh (homOf TwoLetter.code w), TwoLetter.decBlock_homOf_code]
    exact heq ▸ hmem

/-! ### Exercise `exer:polynomial-ideals` -/

/-
The faithful rendering of Exercise `exer:polynomial-ideals`, which is **false**: at `k = 0` the
hypothesis `OmegaOutputs f 0` holds of every function, while `O(n^0)` outputs is exactly a finite
range, so the statement would say that every ideal with a member at all contains every rational
function of finite range.  `polynomial_ideals_false_at_zero` below refutes it, with the ideal
`RangeAtMost 1` and the function `Transducers.Exercises.firstLetterFun`.  The corrected statement,
with `k ≥ 1`, is `polynomial_ideals`; the divergence is recorded in `EXERCISES.md`.

theorem polynomial_ideals_faithful (hPoly : FactorThroughSortedOfOutputsPoly)
    {I : ∀ (A B : Type), (List A → List B) → Prop} (hI : IsIdeal I)
    {A B : Type} [Finite A] [Finite B] {f : List A → List B} {k : ℕ}
    (hfI : I A B f) (hf : OmegaOutputs f k) :
    ∀ (C D : Type) [Finite C] [Finite D] (u : List C → List D), IsRationalFun u →
      (∃ K : ℕ, ∀ n, outCount u n ≤ K * (n + 1) ^ k) → I C D u
-/

/-- **The `k = 0` case of Exercise `exer:polynomial-ideals` is false.**  The ideal `RangeAtMost 1`
contains the constant function, which has `Ω(n^0)` outputs since every function does, and
`Transducers.Exercises.firstLetterFun` is rational with `O(n^0)` outputs and does not belong to
it. -/
theorem polynomial_ideals_false_at_zero :
    ∃ I : ∀ (A B : Type), (List A → List B) → Prop, IsIdeal I ∧
      ∃ f : List Bool → List Bool, I Bool Bool f ∧ OmegaOutputs f 0 ∧
        ∃ u : List Bool → List Bool, IsRationalFun u ∧
          (∃ K : ℕ, ∀ n, outCount u n ≤ K * (n + 1) ^ 0) ∧ ¬ I Bool Bool u := by
  classical
  refine ⟨RangeAtMost 1, isIdeal_rangeAtMost 1, (fun _ => []), ?_, ?_,
    firstLetterFun, isRationalFun_firstLetterFun, ⟨2, outCount_firstLetterFun⟩, ?_⟩
  · refine ⟨isRationalFun_const _, ?_, ?_⟩
    · exact Set.Finite.subset (Set.finite_singleton ([] : List Bool))
        (by rintro v ⟨w, rfl⟩; rfl)
    · exact le_trans (Set.ncard_le_ncard (by rintro v ⟨w, rfl⟩; rfl)
        (Set.finite_singleton ([] : List Bool))) (by simp)
  · refine ⟨1, Nat.one_pos, 0, fun n _ => ?_⟩
    have hmem : ([] : List Bool) ∈
        (fun _ : List Bool => ([] : List Bool)) '' {w : List Bool | w.length ≤ n} :=
      ⟨[], by simp, rfl⟩
    have hpos : 0 < outCount (fun _ : List Bool => ([] : List Bool)) n := by
      refine Set.ncard_pos (Set.Finite.subset (Set.finite_singleton ([] : List Bool))
        (by rintro v ⟨w, -, rfl⟩; rfl)) |>.2 ⟨[], hmem⟩
    simpa using hpos
  · rintro ⟨-, hfin, hcard⟩
    have hsub : ({[], [true]} : Set (List Bool)) ⊆ Set.range firstLetterFun := by
      rintro v (rfl | rfl)
      · exact ⟨[], rfl⟩
      · exact ⟨[true], by rw [firstLetterFun, if_neg (by simp)]⟩
    have h2 : ({[], [true]} : Set (List Bool)).ncard = 2 := Set.ncard_pair (by simp)
    have := Set.ncard_le_ncard hsub hfin
    omega

/-- **Exercise `exer:polynomial-ideals`.**  If an ideal contains a function with `Ω(n^k)` outputs,
`k ≥ 1`, then it contains every rational function with `O(n^k)` outputs.

This is the author's argument in two steps: the member with `Ω(n^k)` outputs produces the sorted
identity `sortedFun k` inside the ideal (`SortedFromOmegaOutputs`), and every rational function
with `O(n^k)` outputs factors through `sortedFun k` (`FactorThroughSortedOfOutputsPolyPos`).

The hypothesis `1 ≤ k` is not in the book, and cannot be dropped: see
`polynomial_ideals_false_at_zero`. -/
theorem polynomial_ideals
    {I : ∀ (A B : Type), (List A → List B) → Prop} (hI : IsIdeal I)
    {A B : Type} [Finite A] [Finite B] {f : List A → List B} {k : ℕ} (hk : 1 ≤ k)
    (hfI : I A B f) (hf : OmegaOutputs f k) :
    ∀ (C D : Type) [Finite C] [Finite D] (u : List C → List D), IsRationalFun u →
      (∃ K : ℕ, ∀ n, outCount u n ≤ K * (n + 1) ^ k) → I C D u := by
  obtain ⟨g, h, hg, hh, hgh⟩ := SortedFromOmegaOutputs A B f k (hI.1 A B f hfI) hf
  have hsorted : I (Fin k) (Fin k) (sortedFun k) := by
    have hmem := hI.2 (Fin k) A B (Fin k) g f h hg hfI hh
    have heq : (h ∘ f ∘ g) = sortedFun k := funext hgh
    exact heq ▸ hmem
  intro C D _ _ u hu hupoly
  obtain ⟨g', h', hg', hh', hgh'⟩ := FactorThroughSortedOfOutputsPolyPos C D u k hk hu hupoly
  have hmem := hI.2 C (Fin k) (Fin k) D g' (sortedFun k) h' hg' hsorted hh'
  have heq : (h' ∘ sortedFun k ∘ g') = u := funext hgh'
  exact heq ▸ hmem

/-! ### Exercise `exer:all-ideals` -/

/-- A rational function with an infinite range has no polynomial bound of degree `0` on its
outputs, so every degree that bounds it is at least `1`.  This is what makes the hypothesis
`1 ≤ k` of `polynomial_ideals` available in the proof of `all_ideals`: an ideal that is not
classified by Exercise `exer:finite-range-ideals` has a member with an infinite range. -/
lemma one_le_of_not_finite_range {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hrat : IsRationalFun f) (hnf : ¬ (Set.range f).Finite) {j : ℕ}
    (hj : ∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ j) : 1 ≤ j := by
  rcases Nat.eq_zero_or_pos j with rfl | h
  · exact absurd ((outputsPoly_zero_iff_finite_range f).1 ⟨hrat, hj⟩).2 hnf
  · exact h

/-- The levels at which an ideal has a member of `Ω(n^k)` outputs. -/
def IdealOmegaLevels (I : ∀ (A B : Type), (List A → List B) → Prop) : Set ℕ :=
  {k | ∃ (A B : Type) (_ : Finite A) (_ : Finite B) (f : List A → List B),
        I A B f ∧ OmegaOutputs f k}

/-- **Exercise `exer:all-ideals`.**  Every ideal is one of the ideals of the previous exercises:
the functions whose range has at most `k` elements, the functions with `O(n^k)` outputs, the
functions with polynomially many outputs, or all rational functions.

This is the author's case analysis.  If every member has a finite range, the classification of
Exercise `exer:finite-range-ideals` applies.  Otherwise, if some member has super-polynomially many
outputs, the ideal is everything by Exercise `exer:full-ideal`.  Otherwise every member is `Θ(n^k)`
for some `k` by the dichotomy, and the ideal is `OutputsPoly k` for the largest level `k` that
occurs, or the union of all of them if there is no largest one; both by Exercise
`exer:polynomial-ideals`. -/
theorem all_ideals
    {I : ∀ (A B : Type), (List A → List B) → Prop} (hI : IsIdeal I) :
    (∃ k : ℕ, ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
        I A B f ↔ RangeAtMost k A B f) ∨
    (∃ k : ℕ, ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
        I A B f ↔ OutputsPoly k A B f) ∨
    (∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
        I A B f ↔ OutputsPolySome A B f) ∨
    (∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
        I A B f ↔ AllRationalFuns A B f) := by
  classical
  by_cases hfin : ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B),
      I A B f → (Set.range f).Finite
  · rcases finite_range_ideal_classification hI hfin with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨0, h⟩)
  · -- there is a member, and none of them has a finite range in the vacuous sense
    have hinf : ∃ (A B : Type) (_ : Finite A) (_ : Finite B) (f : List A → List B),
        I A B f ∧ ¬ (Set.range f).Finite := by
      by_contra hno
      exact hfin (fun A B _ _ f hf => not_not.1 (fun hnf =>
        hno ⟨A, B, ‹Finite A›, ‹Finite B›, f, hf, hnf⟩))
    have hmem : ∃ (A B : Type) (_ : Finite A) (_ : Finite B) (f : List A → List B), I A B f := by
      by_contra hno
      exact hfin (fun A B _ _ f hf => absurd ⟨A, B, ‹Finite A›, ‹Finite B›, f, hf⟩ hno)
    by_cases hsuper : ∃ (A B : Type) (_ : Finite A) (_ : Finite B) (f : List A → List B),
        I A B f ∧ SuperPolyOutputs f
    · refine Or.inr (Or.inr (Or.inr ?_))
      intro A B _ _ f
      refine ⟨fun hf => hI.1 A B f hf, fun hf => ?_⟩
      obtain ⟨A₁, B₁, i₁, i₂, f₁, hf₁I, hs₁⟩ := hsuper
      haveI := i₁; haveI := i₂
      exact (full_ideal_iff hI).2
        ⟨A₁, B₁, i₁, i₂, f₁, hf₁I, rationalRel_range_isRegular (hI.1 A₁ B₁ f₁ hf₁I), hs₁⟩
        A B f hf
    · push_neg at hsuper
      -- every member is `Θ(n^j)` for some `j`
      have hlevel : ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B), I A B f →
          ∃ j : ℕ, (∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ j) ∧ OmegaOutputs f j := by
        intro A B _ _ f hf
        rcases OutputsGrowthDichotomy A B f (hI.1 A B f hf) with hs | hj
        · exact absurd hs (hsuper A B ‹Finite A› ‹Finite B› f hf)
        · exact hj
      have hne : (IdealOmegaLevels I).Nonempty := by
        obtain ⟨A₁, B₁, i₁, i₂, f₁, hf₁⟩ := hmem
        haveI := i₁; haveI := i₂
        obtain ⟨j, -, hj⟩ := hlevel A₁ B₁ f₁ hf₁
        exact ⟨j, A₁, B₁, i₁, i₂, f₁, hf₁, hj⟩
      by_cases hbdd : BddAbove (IdealOmegaLevels I)
      · obtain ⟨A₁, B₁, i₁, i₂, f₁, hf₁I, hf₁Ω⟩ := Nat.sSup_mem hne hbdd
        haveI := i₁; haveI := i₂
        -- the level of a member with an infinite range is at least `1`, so the supremum is too
        have hsup1 : 1 ≤ sSup (IdealOmegaLevels I) := by
          obtain ⟨A₂, B₂, i₃, i₄, f₂, hf₂I, hf₂inf⟩ := hinf
          haveI := i₃; haveI := i₄
          obtain ⟨j₂, hj₂C, hj₂Ω⟩ := hlevel A₂ B₂ f₂ hf₂I
          exact le_trans (one_le_of_not_finite_range (hI.1 _ _ _ hf₂I) hf₂inf hj₂C)
            (le_csSup hbdd ⟨A₂, B₂, i₃, i₄, f₂, hf₂I, hj₂Ω⟩)
        refine Or.inr (Or.inl ⟨sSup (IdealOmegaLevels I), fun A B _ _ f => ⟨fun hf => ?_, ?_⟩⟩)
        · obtain ⟨j, ⟨C, hC⟩, hjΩ⟩ := hlevel A B f hf
          have hjle : j ≤ sSup (IdealOmegaLevels I) :=
            le_csSup hbdd ⟨A, B, ‹Finite A›, ‹Finite B›, f, hf, hjΩ⟩
          exact ⟨hI.1 A B f hf, C, outCount_mono_pow hjle hC⟩
        · rintro ⟨hu, C, hC⟩
          exact polynomial_ideals hI hsup1 hf₁I hf₁Ω A B f hu ⟨C, hC⟩
      · refine Or.inr (Or.inr (Or.inl fun A B _ _ f => ⟨fun hf => ?_, ?_⟩))
        · obtain ⟨j, ⟨C, hC⟩, -⟩ := hlevel A B f hf
          exact ⟨hI.1 A B f hf, j, C, hC⟩
        · rintro ⟨hu, k, C, hC⟩
          obtain ⟨j, ⟨A₁, B₁, i₁, i₂, f₁, hf₁I, hf₁Ω⟩, hkj⟩ := not_bddAbove_iff.1 hbdd k
          haveI := i₁; haveI := i₂
          exact polynomial_ideals hI (by omega) hf₁I hf₁Ω A B f hu
            ⟨C, outCount_mono_pow hkj.le hC⟩

/-! ### Exercise `exer:decide-same-ideal` -/

/-- Two functions *generate the same ideal* if they belong to exactly the same ideals.  The ideals
being linearly ordered (Exercise `exer:all-ideals`), this is the same as the book's "the last ideal
that contains it" being the same for the two functions. -/
def SameIdeal {A B C D : Type} (f : List A → List B) (g : List C → List D) : Prop :=
  ∀ I : ∀ (A B : Type), (List A → List B) → Prop, IsIdeal I → (I A B f ↔ I C D g)

/-- The invariant that the solution to Exercise `exer:decide-same-ideal` computes: the size of the
range if it is finite, and the polynomial degree of the number of outputs otherwise. -/
def SameOutputInvariant {A B C D : Type} (f : List A → List B) (g : List C → List D) : Prop :=
  ((Set.range f).Finite ∧ (Set.range g).Finite ∧ (Set.range f).ncard = (Set.range g).ncard) ∨
    (¬ (Set.range f).Finite ∧ ¬ (Set.range g).Finite ∧
      ∀ k : ℕ, (∃ C : ℕ, ∀ n, outCount f n ≤ C * (n + 1) ^ k) ↔
        (∃ C : ℕ, ∀ n, outCount g n ≤ C * (n + 1) ^ k))

/-- **Exercise `exer:decide-same-ideal`.**  Two rational functions generate the same ideal exactly
when their ranges are both finite of the same size, or both infinite with the same polynomial
degree.  This is the reduction of the decision problem to the computation of that invariant, which
is what the author's solution consists of; the computation itself — looking for the patterns of
the previous exercises in an automaton for the range — is what this project does not have, and
`sameIdeal_decidable` below turns any way of deciding the invariant into a decision procedure for
the exercise.

The direction from left to right uses only the two families of ideals of Exercise
`exer:some-ideals`, which are known to be ideals; the other direction is the classification of
Exercise `exer:all-ideals`. -/
theorem sameIdeal_iff
    {A B C D : Type} [Finite A] [Finite B] [Finite C] [Finite D]
    {f : List A → List B} {g : List C → List D}
    (hf : IsRationalFun f) (hg : IsRationalFun g) :
    SameIdeal f g ↔ SameOutputInvariant f g := by
  classical
  constructor
  · intro hsame
    by_cases hffin : (Set.range f).Finite
    · have hgmem := (hsame (RangeAtMost (Set.range f).ncard) (isIdeal_rangeAtMost _)).1
        ⟨hf, hffin, le_refl _⟩
      have hgfin : (Set.range g).Finite := hgmem.2.1
      have hfmem := (hsame (RangeAtMost (Set.range g).ncard) (isIdeal_rangeAtMost _)).2
        ⟨hg, hgfin, le_refl _⟩
      exact Or.inl ⟨hffin, hgfin, le_antisymm hfmem.2.2 hgmem.2.2⟩
    · have hgfin : ¬ (Set.range g).Finite := by
        intro hgfin
        exact hffin ((hsame (RangeAtMost (Set.range g).ncard)
          (isIdeal_rangeAtMost _)).2 ⟨hg, hgfin, le_refl _⟩).2.1
      refine Or.inr ⟨hffin, hgfin, fun k => ⟨fun hfk => ?_, fun hgk => ?_⟩⟩
      · exact ((hsame (OutputsPoly k) (isIdeal_outputsPoly k)).1 ⟨hf, hfk⟩).2
      · exact ((hsame (OutputsPoly k) (isIdeal_outputsPoly k)).2 ⟨hg, hgk⟩).2
  · intro hinv I hI
    rcases all_ideals hI with ⟨k, hk⟩ | ⟨k, hk⟩ | hk | hk
    · rw [hk A B f, hk C D g]
      rcases hinv with ⟨hffin, hgfin, hcard⟩ | ⟨hffin, hgfin, -⟩
      · exact ⟨fun h => ⟨hg, hgfin, hcard ▸ h.2.2⟩, fun h => ⟨hf, hffin, hcard ▸ h.2.2⟩⟩
      · exact ⟨fun h => absurd h.2.1 hffin, fun h => absurd h.2.1 hgfin⟩
    · rw [hk A B f, hk C D g]
      rcases hinv with ⟨hffin, hgfin, -⟩ | ⟨-, -, hiff⟩
      · exact ⟨fun _ => outputsPoly_of_finite_range hg hgfin k,
          fun _ => outputsPoly_of_finite_range hf hffin k⟩
      · exact ⟨fun h => ⟨hg, (hiff k).1 h.2⟩, fun h => ⟨hf, (hiff k).2 h.2⟩⟩
    · rw [hk A B f, hk C D g]
      rcases hinv with ⟨hffin, hgfin, -⟩ | ⟨-, -, hiff⟩
      · exact ⟨fun _ => ⟨hg, 0, (outputsPoly_of_finite_range hg hgfin 0).2⟩,
          fun _ => ⟨hf, 0, (outputsPoly_of_finite_range hf hffin 0).2⟩⟩
      · refine ⟨fun h => ⟨hg, ?_⟩, fun h => ⟨hf, ?_⟩⟩
        · obtain ⟨k, hk'⟩ := h.2
          obtain ⟨C', hC'⟩ := (hiff k).1 hk'
          exact ⟨k, C', hC'⟩
        · obtain ⟨k, hk'⟩ := h.2
          obtain ⟨C', hC'⟩ := (hiff k).2 hk'
          exact ⟨k, C', hC'⟩
    · rw [hk A B f, hk C D g]
      exact ⟨fun _ => hg, fun _ => hf⟩

/-- **Exercise `exer:decide-same-ideal`**, the decision procedure: once the invariant of
`sameIdeal_iff` can be decided, so can the property that two rational functions generate the same
ideal. -/
def sameIdeal_decidable
    {A B C D : Type} [Finite A] [Finite B] [Finite C] [Finite D]
    {f : List A → List B} {g : List C → List D}
    (hf : IsRationalFun f) (hg : IsRationalFun g)
    (hdec : Decidable (SameOutputInvariant f g)) : Decidable (SameIdeal f g) :=
  decidable_of_iff _ (sameIdeal_iff hf hg).symm

end Transducers.Exercises
