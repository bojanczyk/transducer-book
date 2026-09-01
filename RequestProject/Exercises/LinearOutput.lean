/-
The three exercises of *Transducers* (M. Bojańczyk) on functions of exactly linear output size:
`exer:rational-outpus-of-exactly-linear-size` and
`exer:rational-outpus-of-exactly-linear-size-rational-number` of `rational-functions.tex`, and
`exer:regular-outpus-of-exactly-linear-size` of `2dfa.tex`.
-/
import RequestProject.Exercises.TwoDFAUnary
import RequestProject.Exercises.PartBCAux
import RequestProject.Exercises.CycleMean

/-!
# Exactly linear output size

Let `f` be a rational (or regular) function whose output size is *unbounded*.  The exercises ask
for the limit

  `lim_{n → ∞} (maximal output length on inputs of length at most n) / n`

to exist, to be nonzero, and (the second and the third exercise) to be a rational number.

The numerator is `Transducers.Exercises.maxOutLen f n`, the supremum of `|f w|` over the inputs
`w` of length at most `n`; the alphabet is finite, so that supremum is a maximum.

## What is proved

The solution of the book computes the limit as the maximum, over the cycles of a trim
nondeterministic transducer for `f`, of the ratio (output length)/(input length) of the cycle —
the *maximum cycle mean* of the weighted graph of the transducer.  That analysis is carried out in
`RequestProject/Exercises/CycleMean.lean`; it gives
`Transducers.Exercises.RationalHasLinearRate`, which used to be a hypothesis of this file and is
now a theorem.

It says that every rational function `f` has a *linear rate*,
`Transducers.Exercises.HasLinearRate f`: there are natural numbers `p`, `q > 0` and `C` with

  `|q · maxOutLen f n − p · n| ≤ C`  for every `n`,

i.e. the maximal output length is `(p/q)·n` up to a bounded error.  Here `p/q` is the maximal ratio
of a cycle through a productive state, the upper bound comes from decomposing a run into cycles and
a short path, and the lower bound from pumping an optimal cycle, the error `C` accounting in both
cases for the bounded parts of the run that lie outside the cycles.

What is proved here is the exercise itself from that statement, and it is not a restatement of it:
that the limit *exists*, that it is *nonzero* — this is where the unboundedness of the output size
is used, and it is the only place where it is used — and that it is a *rational number*, namely
`p/q`.  The third exercise is then reduced to the first two exactly as the book does it: replacing
every output letter by a single letter changes neither the output lengths nor regularity, and over
a one-letter output alphabet the regular functions are the rational ones
(`Transducers.Exercises.isRegularFun_iff_isRationalFun_of_unary_output`, Exercise
`exer:2dfa-unary-output`).
-/

namespace Transducers.Exercises

open Filter Topology

/-! ### The maximal output length -/

section MaxOut

variable {A B : Type}

/-- The maximal length of `f w` over the inputs `w` of length at most `n`: the numerator of the
limit in Exercises `exer:rational-outpus-of-exactly-linear-size` and
`exer:regular-outpus-of-exactly-linear-size`.  The alphabet is finite, so the supremum is over a
finite nonempty set of natural numbers and is therefore attained. -/
noncomputable def maxOutLen (f : List A → List B) (n : ℕ) : ℕ :=
  sSup ((fun w => (f w).length) '' {w : List A | w.length ≤ n})

lemma maxOutLen_finite [Finite A] (f : List A → List B) (n : ℕ) :
    ((fun w => (f w).length) '' {w : List A | w.length ≤ n}).Finite :=
  (finite_lists_length_le n).image _

lemma le_maxOutLen [Finite A] (f : List A → List B) {w : List A} {n : ℕ} (hw : w.length ≤ n) :
    (f w).length ≤ maxOutLen f n :=
  le_csSup (maxOutLen_finite f n).bddAbove ⟨w, hw, rfl⟩

lemma maxOutLen_le (f : List A → List B) {n m : ℕ}
    (h : ∀ w : List A, w.length ≤ n → (f w).length ≤ m) : maxOutLen f n ≤ m := by
  refine csSup_le ⟨(f []).length, ⟨[], by simp, rfl⟩⟩ ?_
  rintro x ⟨w, hw, rfl⟩
  exact h w hw

/-- The maximum is attained: the alphabet is finite, so the supremum is over a finite nonempty set
of natural numbers. -/
lemma exists_maxOutLen_eq [Finite A] (f : List A → List B) (n : ℕ) :
    ∃ w : List A, w.length ≤ n ∧ (f w).length = maxOutLen f n := by
  have hne : ((fun w => (f w).length) '' {w : List A | w.length ≤ n}).Nonempty :=
    ⟨(f []).length, [], by simp, rfl⟩
  obtain ⟨w, hw, hval⟩ := Nat.sSup_mem hne (maxOutLen_finite f n).bddAbove
  exact ⟨w, hw, hval⟩

end MaxOut

/-! ### The maximal output length grows at a fixed rational rate -/

/-- **The maximum cycle mean, for one function.**  The maximal output length of `f` on inputs of
length at most `n` is `(p/q)·n` up to an additive constant.  See the header of this file for why
this is what the analysis of the cycles of a transducer for `f` gives. -/
def HasLinearRate {A B : Type} (f : List A → List B) : Prop :=
  ∃ p q C : ℕ, 0 < q ∧
    ∀ n : ℕ, q * maxOutLen f n ≤ p * n + C ∧ p * n ≤ q * maxOutLen f n + C

/-- **The maximum cycle mean.**  Every rational function has a linear rate in the sense of
`Transducers.Exercises.HasLinearRate`.  This was a hypothesis of the two exercises below; it is
now a theorem, proved in `RequestProject/Exercises/CycleMean.lean` from the analysis of the cycles
of a transducer for `f`. -/
theorem RationalHasLinearRate :
    ∀ (A B : Type) [Finite A] [Finite B] (f : List A → List B), IsRationalFun f →
      HasLinearRate f := by
  intro A B _ _ f hf
  obtain ⟨pn, qd, C, hq, h⟩ := CycleMean.exists_linear_rate hf
  refine ⟨pn, qd, C, hq, fun n => ⟨?_, ?_⟩⟩
  · obtain ⟨w, hw, hval⟩ := exists_maxOutLen_eq f n
    rw [← hval]
    exact (h n).1 w hw
  · obtain ⟨w, hw, hle⟩ := (h n).2
    have hmono : (f w).length ≤ maxOutLen f n := le_maxOutLen f hw
    exact le_trans hle (Nat.add_le_add_right (Nat.mul_le_mul_left _ hmono) C)

/-! ### The limit -/

/-- From a linear rate and an unbounded output size: the limit of the exercise exists, is a
rational number and is nonzero.  This is the analytic half of
Exercises `exer:rational-outpus-of-exactly-linear-size` and
`exer:rational-outpus-of-exactly-linear-size-rational-number`, and it is where the unboundedness
of the output size is used: it is exactly what rules out the rate `0`. -/
theorem exists_pos_rat_tendsto_of_hasLinearRate {A B : Type} [Finite A] {f : List A → List B}
    (hlin : HasLinearRate f) (hunb : ¬ ∃ N : ℕ, ∀ w : List A, (f w).length ≤ N) :
    ∃ r : ℚ, 0 < r ∧
      Tendsto (fun n : ℕ => (maxOutLen f n : ℝ) / n) atTop (𝓝 (r : ℝ)) := by
  obtain ⟨p, q, C, hq, hpq⟩ := hlin
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  -- the rate is nonzero, because the output size is unbounded
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · exact absurd ⟨C, fun w => by
        have h1 := (hpq w.length).1
        have h2 := le_maxOutLen f (le_refl w.length)
        subst hp0
        nlinarith [h1, h2]⟩ hunb
    · exact hp0
  refine ⟨(p : ℚ) / q, by positivity, ?_⟩
  have hkey : ∀ n : ℕ, 1 ≤ n →
      ‖(maxOutLen f n : ℝ) / n - (p : ℝ) / q‖ ≤ (C : ℝ) / q / n := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨h1, h2⟩ := hpq n
    have h1' : (q : ℝ) * maxOutLen f n ≤ (p : ℝ) * n + C := by exact_mod_cast h1
    have h2' : (p : ℝ) * n ≤ (q : ℝ) * maxOutLen f n + C := by exact_mod_cast h2
    have hEq : (maxOutLen f n : ℝ) / n - (p : ℝ) / q
        = ((q : ℝ) * maxOutLen f n - p * n) / (q * n) := by
      field_simp
    have habs : |(q : ℝ) * maxOutLen f n - p * n| ≤ C := abs_le.2 ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs, hEq, abs_div, abs_of_pos (by positivity : (0:ℝ) < (q : ℝ) * n)]
    calc |(q : ℝ) * maxOutLen f n - p * n| / ((q : ℝ) * n)
        ≤ (C : ℝ) / ((q : ℝ) * n) := by gcongr
      _ = (C : ℝ) / q / n := by rw [div_div]
  have hzero : Tendsto (fun n : ℕ => (maxOutLen f n : ℝ) / n - (p : ℝ) / q) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat ((C : ℝ) / q))
    filter_upwards [eventually_ge_atTop 1] with n hn using hkey n hn
  have h := hzero.add (tendsto_const_nhds (x := ((p : ℝ) / q)) (f := (atTop : Filter ℕ)))
  simpa using h

/-- **Exercises `exer:rational-outpus-of-exactly-linear-size` and
`exer:rational-outpus-of-exactly-linear-size-rational-number`.**  A rational function whose output
size is unbounded has exactly linear output size: the limit of the maximal output length on inputs
of length at most `n`, divided by `n`, exists, is nonzero, and is a rational number. -/
theorem rational_exactly_linear_output
    {A B : Type} [Finite A] [Finite B] {f : List A → List B} (hf : IsRationalFun f)
    (hunb : ¬ ∃ N : ℕ, ∀ w : List A, (f w).length ≤ N) :
    ∃ r : ℚ, 0 < r ∧
      Tendsto (fun n : ℕ => (maxOutLen f n : ℝ) / n) atTop (𝓝 (r : ℝ)) :=
  exists_pos_rat_tendsto_of_hasLinearRate (RationalHasLinearRate A B f hf) hunb

/-! ### The regular case -/

/-- Replacing every output letter by a single letter does not change the maximal output length. -/
lemma maxOutLen_map_const {A B : Type} [Finite A] (f : List A → List B) (n : ℕ) :
    maxOutLen (fun w => (f w).map (fun _ => ())) n = maxOutLen f n := by
  simp only [maxOutLen, List.length_map]

/-- **Exercise `exer:regular-outpus-of-exactly-linear-size`.**  A regular function whose output
size is unbounded has exactly linear output size, and the limit is a rational number.

This is the author's reduction: replacing every output letter by a single letter changes neither
the output lengths nor regularity, and over a one-letter output alphabet the regular functions are
exactly the rational functions (Exercise `exer:2dfa-unary-output`), so the statement follows from
the rational case. -/
theorem regular_exactly_linear_output
    {A B : Type} [Finite A] [Finite B] {f : List A → List B} (hf : IsRegularFun f)
    (hunb : ¬ ∃ N : ℕ, ∀ w : List A, (f w).length ≤ N) :
    ∃ r : ℚ, 0 < r ∧
      Tendsto (fun n : ℕ => (maxOutLen f n : ℝ) / n) atTop (𝓝 (r : ℝ)) := by
  have hgreg : IsRegularFun (fun w : List A => (f w).map (fun _ : B => ())) :=
    hf.comp' (isRegularFun_map (fun _ : B => ())) (fun w => rfl)
  have hgrat : IsRationalFun (fun w : List A => (f w).map (fun _ : B => ())) :=
    (isRegularFun_iff_isRationalFun_of_unary_output _).1 hgreg
  have hgunb : ¬ ∃ N : ℕ, ∀ w : List A, ((f w).map (fun _ : B => ())).length ≤ N := by
    rintro ⟨N, hN⟩
    exact hunb ⟨N, fun w => by simpa using hN w⟩
  obtain ⟨r, hr, htend⟩ := rational_exactly_linear_output hgrat hgunb
  refine ⟨r, hr, ?_⟩
  simpa only [maxOutLen_map_const f] using htend

end Transducers.Exercises
