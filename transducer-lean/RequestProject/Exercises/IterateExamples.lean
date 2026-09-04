/-
Instances of the decision problem of Exercise
`exer:rational-composition-finiteness-undecidable` of *Transducers* (M. Bojańczyk): a computable
family of codes that can be iterated, whose set of iterates is finite for some members of the
family and infinite for the others.
-/
import RequestProject.Exercises.IterateFiniteness
import RequestProject.Exercises.PartBCPCP

/-!
# Instances of the problem of the exercise, and a computable family of them

Exercise `exer:rational-composition-finiteness-undecidable` asks whether it is decidable that a
rational function generates finitely many functions under composition.  The problem is stated in
`RequestProject/Exercises/IterateFiniteness.lean` as the pair of a promise
(`Transducers.Exercises.CodeSelfMap`: the code describes a function on the strings over its
alphabet, whose outputs are again such strings) and a predicate
(`Transducers.Exercises.CodeIteratesFinite`).

This file gives instances of that problem, all of them codes of a homomorphism over the
one-letter alphabet `{0}`, built with the automaton `Transducers.Exercises.funCode` of
`RequestProject/Exercises/PartBCPCP.lean`.  For `k : ℕ`, the code `powCode k` describes the
homomorphism `0 ↦ 0ᵏ`, which multiplies the length of every nonempty string by `k`:

* for `k ≤ 1` the set of iterates is finite (`codeIteratesFinite_powCode_of_le_one`) — the map is
  the identity on nonempty strings when `k = 1`, and empties every nonempty string when `k = 0`;
* for `2 ≤ k` the `n`-th iterate sends the one-letter string to `0` repeated `kⁿ` times, so the
  iterates are pairwise distinct and there are infinitely many of them
  (`not_codeIteratesFinite_powCode`).

So both answers occur (`exists_codeSelfMap_iteratesFinite`,
`exists_codeSelfMap_not_iteratesFinite`): the promise problem of the exercise is not constant on
the codes that satisfy the promise, which is what makes the question of the exercise a question
at all.

The family `powCode` is computable (`computable_powCode`), so
`exists_computable_iterates_family` gives everything that
`Transducers.Exercises.IteratesReduction` asks for except the one thing that is missing: the set
`{e | CodeIteratesFinite (powCode e)} = {e | e ≤ 1}` is decidable.  See the docstring of
`IteratesReduction` for what a reduction would have to achieve instead.
-/

namespace Transducers.Exercises

open Transducers PCP

/-! ## The self-map described by a code, evaluated -/

/-- The value of the map that a code describes: any output of the coded relation is *the* value,
because the code describes a function. -/
lemma codeSelfFun_val {c : RelCode} (h : CodeSelfMap c) (w : {w : List ℕ // CodeWord c w})
    {v : List ℕ} (hv : codeRel c w.1 v) : (codeSelfFun h w).1 = v :=
  ((h.1 w.1 w.2).choose_spec.2 v hv).symm

/-! ## Codes of a homomorphism as self-maps -/

/-- A word of `ws` has all its letters among the indices of `ws`. -/
lemma lt_length_of_mem_getD {ws : List (List ℕ)}
    (hws : ∀ u ∈ ws, ∀ i ∈ u, i < ws.length) (j : ℕ) {i : ℕ} (hi : i ∈ ws.getD j []) :
    i < ws.length := by
  by_cases hj : j < ws.length
  · rw [List.getD_eq_getElem _ _ hj] at hi
    exact hws _ (List.getElem_mem hj) i hi
  · rw [List.getD_eq_default _ _ (by omega)] at hi
    exact absurd hi (by simp)

/-- The homomorphic image of a string of indices of `ws` is again a string of indices of `ws`,
as soon as every word of `ws` is one. -/
lemma mem_conc_lt_length {ws : List (List ℕ)}
    (hws : ∀ u ∈ ws, ∀ i ∈ u, i < ws.length) :
    ∀ (w : List ℕ) {i : ℕ}, i ∈ conc ws w → i < ws.length := by
  intro w
  induction w with
  | nil => intro i hi; exact absurd hi (by simp)
  | cons j w ih =>
      intro i hi
      rw [conc_cons, List.mem_append] at hi
      rcases hi with hi | hi
      · exact lt_length_of_mem_getD hws j hi
      · exact ih hi

/-- **The code of a homomorphism can be iterated** when the homomorphism maps the alphabet of the
code into itself: the letters of every word of `ws` are indices of `ws`, and so is the letter `x`
that the code outputs on the empty input. -/
theorem codeSelfMap_funCode {ws : List (List ℕ)} {x : ℕ} (hx : x < ws.length)
    (hws : ∀ u ∈ ws, ∀ i ∈ u, i < ws.length) : CodeSelfMap (funCode ws x) := by
  refine ⟨codeFunctional_funCode ws x, ?_⟩
  intro w v _ hrel
  rcases (codeRel_funCode ws x w v).1 hrel with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · intro i hi
    have : i = x := by simpa using hi
    exact mem_codeAlphabet_funCode.2 (this ▸ hx)
  · intro i hi
    exact mem_codeAlphabet_funCode.2 (mem_conc_lt_length hws w hi)

/-- The value of the self-map described by the code of a homomorphism, on a nonempty string: the
homomorphic image. -/
lemma codeSelfFun_funCode_ne_nil {ws : List (List ℕ)} {x : ℕ} (h : CodeSelfMap (funCode ws x))
    (w : {w : List ℕ // CodeWord (funCode ws x) w}) (hne : w.1 ≠ []) :
    (codeSelfFun h w).1 = conc ws w.1 :=
  codeSelfFun_val h w ((codeRel_funCode ws x w.1 _).2
    (Or.inr ⟨hne, fun i hi => mem_codeAlphabet_funCode.1 (w.2 i hi), rfl⟩))

/-- The value of the self-map described by the code of a homomorphism, on the empty string: the
extra letter `x`. -/
lemma codeSelfFun_funCode_nil {ws : List (List ℕ)} {x : ℕ} (h : CodeSelfMap (funCode ws x))
    (w : {w : List ℕ // CodeWord (funCode ws x) w}) (hnil : w.1 = []) :
    (codeSelfFun h w).1 = [x] :=
  codeSelfFun_val h w ((codeRel_funCode ws x w.1 [x]).2 (Or.inl ⟨hnil, rfl⟩))

/-! ## The homomorphism `0 ↦ 0ᵏ` -/

/-- The code of the homomorphism `0 ↦ 0ᵏ` over the one-letter alphabet `{0}`.  It describes the
self-map that multiplies the length of a nonempty string of zeros by `k`, and sends the empty
string to `0`. -/
def powCode (k : ℕ) : RelCode := funCode [List.replicate k 0] 0

/-- **The code `powCode k` can be iterated.** -/
theorem codeSelfMap_powCode (k : ℕ) : CodeSelfMap (powCode k) := by
  refine codeSelfMap_funCode (by simp) ?_
  intro u hu i hi
  have hu' : u = List.replicate k 0 := by simpa using hu
  subst hu'
  rw [List.eq_of_mem_replicate hi]
  simp

/-- The strings over the alphabet of `powCode k` are the strings of zeros. -/
lemma codeWord_powCode_iff (k : ℕ) (w : List ℕ) :
    CodeWord (powCode k) w ↔ ∀ i ∈ w, i = 0 := by
  constructor
  · intro hw i hi
    have := mem_codeAlphabet_funCode.1 (hw i hi)
    simp only [List.length_cons, List.length_nil] at this
    omega
  · intro hw i hi
    exact mem_codeAlphabet_funCode.2 (by rw [hw i hi]; simp)

lemma conc_powCode (k : ℕ) (w : List ℕ) (hw : ∀ i ∈ w, i = 0) :
    conc [List.replicate k 0] w = List.replicate (k * w.length) 0 := by
  induction w with
  | nil => simp
  | cons i w ih =>
      have hi : i = 0 := hw i (by simp)
      subst hi
      rw [conc_cons, ih fun j hj => hw j (by simp [hj]), List.length_cons,
        show k * (w.length + 1) = k + k * w.length by ring, List.replicate_add]
      rfl

/-- The value of the self-map described by `powCode k` on a nonempty string. -/
lemma codeSelfFun_powCode_ne_nil {k : ℕ} (h : CodeSelfMap (powCode k))
    (w : {w : List ℕ // CodeWord (powCode k) w}) (hne : w.1 ≠ []) :
    (codeSelfFun h w).1 = List.replicate (k * w.1.length) 0 := by
  rw [codeSelfFun_funCode_ne_nil h w hne]
  exact conc_powCode k w.1 ((codeWord_powCode_iff k w.1).1 w.2)

/-- The value of the self-map described by `powCode k` on the empty string. -/
lemma codeSelfFun_powCode_nil {k : ℕ} (h : CodeSelfMap (powCode k))
    (w : {w : List ℕ // CodeWord (powCode k) w}) (hnil : w.1 = []) :
    (codeSelfFun h w).1 = [0] :=
  codeSelfFun_funCode_nil h w hnil

/-! ### `k ≤ 1`: finitely many iterates -/

/-- **An instance of the problem with answer yes.**  For `k ≤ 1` the self-map described by
`powCode k` has finitely many iterates: for `k = 1` it is idempotent, and for `k = 0` its cube is
its first power. -/
theorem codeIteratesFinite_powCode_of_le_one {k : ℕ} (hk : k ≤ 1) :
    CodeIteratesFinite (powCode k) := by
  intro h
  rw [iterates_finite_iff]
  interval_cases k
  · -- `k = 0`: the map alternates between `[]` and `[0]`, so `f³ = f`
    refine ⟨1, 2, by norm_num, funext fun w => ?_⟩
    have hnil : ∀ v : {w : List ℕ // CodeWord (powCode 0) w}, v.1 ≠ [] →
        (codeSelfFun h v).1 = [] := by
      intro v hv
      rw [codeSelfFun_powCode_ne_nil h v hv]
      simp
    have hzero : ∀ v : {w : List ℕ // CodeWord (powCode 0) w}, v.1 = [] →
        (codeSelfFun h v).1 = [0] := fun v hv => codeSelfFun_powCode_nil h v hv
    have key : ∀ v : {w : List ℕ // CodeWord (powCode 0) w},
        codeSelfFun h (codeSelfFun h (codeSelfFun h v)) = codeSelfFun h v := by
      intro v
      refine Subtype.ext ?_
      by_cases hv : v.1 = []
      · have h1 : (codeSelfFun h v).1 = [0] := hzero v hv
        have h2 : (codeSelfFun h (codeSelfFun h v)).1 = [] :=
          hnil _ (by rw [h1]; simp)
        rw [hzero _ h2, h1]
      · have h1 : (codeSelfFun h v).1 = [] := hnil v hv
        have h2 : (codeSelfFun h (codeSelfFun h v)).1 = [0] := hzero _ h1
        rw [hnil _ (by rw [h2]; simp), h1]
    have h3 : (codeSelfFun h)^[1 + 2] w
        = codeSelfFun h (codeSelfFun h (codeSelfFun h w)) := by
      simp [Function.iterate_succ_apply]
    rw [Function.iterate_one, h3, key w]
  · -- `k = 1`: the map is the identity on nonempty strings, so `f² = f`
    refine ⟨1, 1, le_refl 1, funext fun w => ?_⟩
    have hne : ∀ v : {w : List ℕ // CodeWord (powCode 1) w}, (codeSelfFun h v).1 ≠ [] := by
      intro v
      by_cases hv : v.1 = []
      · rw [codeSelfFun_powCode_nil h v hv]; simp
      · rw [codeSelfFun_powCode_ne_nil h v hv]
        simp only [ne_eq, List.replicate_eq_nil_iff, one_mul]
        exact fun hlen => hv (List.eq_nil_of_length_eq_zero hlen)
    have key : codeSelfFun h (codeSelfFun h w) = codeSelfFun h w := by
      refine Subtype.ext ?_
      rw [codeSelfFun_powCode_ne_nil h _ (hne w), one_mul]
      refine ((List.eq_replicate_iff).2 ⟨rfl, fun b hb => ?_⟩).symm
      exact (codeWord_powCode_iff 1 _).1 (codeSelfFun h w).2 b hb
    have h2 : (codeSelfFun h)^[1 + 1] w = codeSelfFun h (codeSelfFun h w) := by
      simp [Function.iterate_succ_apply]
    rw [Function.iterate_one, h2, key]

/-! ### `2 ≤ k`: infinitely many iterates -/

lemma codeWord_replicate_powCode (k m : ℕ) : CodeWord (powCode k) (List.replicate m 0) :=
  (codeWord_powCode_iff k _).2 (fun _ hi => List.eq_of_mem_replicate hi)

/-- The `n`-th iterate of the self-map described by `powCode k`, at the one-letter string, is `0`
repeated `kⁿ` times, as long as `k` is positive. -/
lemma iterate_powCode {k : ℕ} (hk : 1 ≤ k) (h : CodeSelfMap (powCode k)) (n : ℕ) :
    ((codeSelfFun h)^[n] ⟨List.replicate 1 0, codeWord_replicate_powCode k 1⟩).1
      = List.replicate (k ^ n) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < k ^ n := Nat.pow_pos (by omega)
      rw [Function.iterate_succ_apply']
      have hne : ((codeSelfFun h)^[n] ⟨List.replicate 1 0,
          codeWord_replicate_powCode k 1⟩).1 ≠ [] := by
        rw [ih]
        simp only [ne_eq, List.replicate_eq_nil_iff]
        omega
      rw [codeSelfFun_powCode_ne_nil h _ hne, ih, List.length_replicate]
      congr 1
      ring

/-- **An instance of the problem with answer no.**  For `2 ≤ k` the self-map described by
`powCode k` multiplies the length of every nonempty string by `k`, so its iterates are pairwise
distinct. -/
theorem not_codeIteratesFinite_powCode {k : ℕ} (hk : 2 ≤ k) :
    ¬ CodeIteratesFinite (powCode k) := by
  intro hfin
  have h := codeSelfMap_powCode k
  obtain ⟨n, m, hm, heq⟩ := (iterates_finite_iff _).1 (hfin h)
  have h1 := iterate_powCode (by omega) h n
  have h2 := iterate_powCode (by omega) h (n + m)
  rw [heq, h2] at h1
  have hlen : k ^ (n + m) = k ^ n := by simpa using congrArg List.length h1
  have : k ^ n < k ^ (n + m) := Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- The set of iterates of `powCode k` is finite exactly for `k ≤ 1`. -/
theorem codeIteratesFinite_powCode_iff (k : ℕ) : CodeIteratesFinite (powCode k) ↔ k ≤ 1 := by
  constructor
  · intro hfin
    by_contra hk
    exact not_codeIteratesFinite_powCode (by omega) hfin
  · exact codeIteratesFinite_powCode_of_le_one

/-! ## The family is computable -/

lemma powCode_eq (k : ℕ) :
    powCode k = ([(0, [0], List.replicate k 0, 1), (1, [0], List.replicate k 0, 1),
      (0, [], [0], 2)], ([0], [1, 2])) := by
  simp [powCode, funCode, funTrans, homTrans]

theorem computable_powCode : Computable powCode := by
  have hrep : Primrec fun k : ℕ => List.replicate k 0 := by
    refine (Primrec.list_map Primrec.list_range (Primrec.const 0).to₂).of_eq fun k => ?_
    rw [List.map_const', List.length_range]
  have htrans : Primrec fun k : ℕ =>
      [((0 : ℕ), [(0 : ℕ)], List.replicate k 0, (1 : ℕ)),
        ((1 : ℕ), [(0 : ℕ)], List.replicate k 0, (1 : ℕ)),
        ((0 : ℕ), ([] : List ℕ), [(0 : ℕ)], (2 : ℕ))] := by
    have h0 : Primrec fun k : ℕ => ((0 : ℕ), [(0 : ℕ)], List.replicate k 0, (1 : ℕ)) :=
      Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.const [(0 : ℕ)]) (Primrec.pair hrep (Primrec.const 1)))
    have h1 : Primrec fun k : ℕ => ((1 : ℕ), [(0 : ℕ)], List.replicate k 0, (1 : ℕ)) :=
      Primrec.pair (Primrec.const 1)
        (Primrec.pair (Primrec.const [(0 : ℕ)]) (Primrec.pair hrep (Primrec.const 1)))
    exact Primrec.list_cons.comp h0 (Primrec.list_cons.comp h1
      (Primrec.const [((0 : ℕ), ([] : List ℕ), [(0 : ℕ)], (2 : ℕ))]))
  refine ((Primrec.pair htrans (Primrec.const (([0], [1, 2]) : List ℕ × List ℕ))).of_eq
    fun k => ?_).to_comp
  rw [powCode_eq]

/-! ## What the family shows -/

/-- The decision problem of Exercise `exer:rational-composition-finiteness-undecidable` has
instances with answer yes. -/
theorem exists_codeSelfMap_iteratesFinite :
    ∃ c : RelCode, CodeSelfMap c ∧ CodeIteratesFinite c :=
  ⟨powCode 1, codeSelfMap_powCode 1, codeIteratesFinite_powCode_of_le_one (le_refl 1)⟩

/-- The decision problem of Exercise `exer:rational-composition-finiteness-undecidable` has
instances with answer no. -/
theorem exists_codeSelfMap_not_iteratesFinite :
    ∃ c : RelCode, CodeSelfMap c ∧ ¬ CodeIteratesFinite c :=
  ⟨powCode 2, codeSelfMap_powCode 2, not_codeIteratesFinite_powCode (le_refl 2)⟩

/-- Everything that `Transducers.Exercises.IteratesReduction` asks for, except that the set which
comes out is decidable: a computable family of codes, all of them iterable, whose set of iterates
is finite exactly on `{e | e ≤ 1}`.

What a reduction has to do is produce a family whose set is *undecidable*; the docstring of
`IteratesReduction` says what that requires, and `iteratesReduction_of_atm_reduction` says what
would then remain to be done. -/
theorem exists_computable_iterates_family :
    ∃ red : ℕ → RelCode, Computable red ∧
      ∀ e, CodeSelfMap (red e) ∧ (CodeIteratesFinite (red e) ↔ e ≤ 1) :=
  ⟨powCode, computable_powCode, fun e => ⟨codeSelfMap_powCode e, codeIteratesFinite_powCode_iff e⟩⟩

end Transducers.Exercises
