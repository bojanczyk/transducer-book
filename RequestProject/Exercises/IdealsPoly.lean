/-
From `O(n^k)` outputs to a factorisation through the sorted-identity function: the third step of
the author's solution to Exercise `exer:polynomial-ideals` of *Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.PatternCoverRat
import RequestProject.Exercises.IdealsOmega

/-!
# A rational function with `O(n^k)` outputs factors through the sorted identity

This is the step of the author's solution that he describes as "analysing the structure of
strongly connected components in the automaton that computes a rational function whose range has
growth `O(n^k)`".  The analysis is
`Transducers.Exercises.RegGrowth.exists_pattern_cover`: the range of `f` is a regular language, of
polynomial growth, so an automaton for it has no ambiguous cycle and no chain of `k+1` loops, and
then every word of the range is a word of one of finitely many `k`-patterns.

* `Transducers.Exercises.exists_pattern_cover_range` — the cover of the range;
* `Transducers.Exercises.exists_rational_factor_through_sorted` — the factorisation.  The rational
  function `h` writes the word of the pattern that a sorted word describes
  (`Transducers.Exercises.exists_rational_cover_of_patterns`), and `g` is a rational section of it
  composed with `f` (the Uniformisation Lemma `lem:uniformisation`, through
  `Transducers.Exercises.exists_rationalFun_section`).

The factorisation needs `k ≥ 1`: for `k = 0` the sorted words over an empty alphabet are all
empty, so a factorisation through `sortedFun 0` would force `f` to be constant, while a rational
function with `O(1)` outputs need only have a finite range.  This is
`Transducers.Exercises.firstLetterFun`, the counterexample used in
`RequestProject/Exercises/Ideals.lean`.
-/

namespace Transducers.Exercises

open Transducers

/-- **The range of a rational function with `O(n^k)` outputs is covered by finitely many
`k`-patterns.** -/
theorem exists_pattern_cover_range {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) {k C : ℕ}
    (hC : ∀ n, (f '' {w : List A | w.length ≤ n}).ncard ≤ C * (n + 1) ^ k) :
    ∃ F : List ((ℕ → List B) × (ℕ → List B)),
      ∀ w : List A, ∃ P ∈ F, ∃ c : ℕ → ℕ, f w = chainWord P.1 P.2 k c := by
  classical
  haveI : Fintype B := Fintype.ofFinite B
  obtain ⟨σ, hσ, M, hM⟩ := rationalRel_range_isRegular hf
  haveI := hσ
  obtain ⟨D, hD⟩ := exists_short_preimage hf
  have hcount : ∀ n, langCount ({v | ∃ w, v = f w} : Language B) n
      = RegGrowth.accCount M M.start n := by
    intro n
    rw [← hM, langCount, RegGrowth.accCount, ← Set.ncard_coe_finset]
    congr 1
    ext v
    constructor
    · rintro ⟨h1, h2⟩
      exact Finset.mem_coe.mpr (RegGrowth.mem_accFin.mpr ⟨h2, h1⟩)
    · intro h
      have h' := RegGrowth.mem_accFin.mp (Finset.mem_coe.mp h)
      exact ⟨h'.2, h'.1⟩
  have hlang : ∀ m, langCount ({v | ∃ w, v = f w} : Language B) m ≤ C * (D * (m + 1) + 1) ^ k :=
    fun m => le_trans (langCount_le_outSet_ncard hD m) (hC _)
  -- no ambiguous cycle: two loops would give super-polynomially many outputs
  have hamb : ¬ RegGrowth.AmbCycle M := by
    rintro ⟨q, ⟨pw, hp⟩, ⟨sw, hs⟩, x, y, hlen, hxy, hx, hy⟩
    have hxpos : 0 < x.length := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · exfalso
        rw [List.length_eq_zero_iff] at h
        have hy0 : y = [] := by
          rw [← List.length_eq_zero_iff, ← hlen, h]
          rfl
        exact hxy (h.trans hy0.symm)
      · exact h
    have hmem : ∀ u : List Bool, ∃ w : List A, pw ++ cycleWord x y u ++ sw = f w := by
      intro u
      have hcyc : M.evalFrom q (cycleWord x y u) = q := by
        induction u with
        | nil => rfl
        | cons b u ih =>
            cases b
            · rw [cycleWord_cons_false, M.evalFrom_of_append, hy, ih]
            · rw [cycleWord_cons_true, M.evalFrom_of_append, hx, ih]
      have hacc : pw ++ cycleWord x y u ++ sw ∈ M.accepts := by
        show M.evalFrom M.start (pw ++ cycleWord x y u ++ sw) ∈ M.accept
        rw [M.evalFrom_of_append, M.evalFrom_of_append, hp, hcyc]
        exact hs
      rw [hM] at hacc
      exact hacc
    obtain ⟨n, hn⟩ := outSet_superPoly_of_range_loops hD hxpos hlen hxy hmem k C
    exact absurd (hC n) (by omega)
  -- no chain of `k+1` loops: it would give `Ω(n^(k+1))` words
  have hchain : ¬ RegGrowth.Chain M M.start (k + 1) := by
    intro hc
    obtain ⟨c, hcpos, N, hN⟩ := RegGrowth.chain_lower_bound hc
    set K := c * C * (D + 1) ^ k with hK
    have hstep : ∀ n, N ≤ n → (n + 1) * (n + 1) ^ k ≤ K * (n + 1) ^ k := by
      intro n hn
      have h1 : (n + 1) ^ (k + 1) ≤ c * RegGrowth.accCount M M.start n := hN n hn
      have h2 : RegGrowth.accCount M M.start n ≤ C * (D * (n + 1) + 1) ^ k := by
        rw [← hcount n]
        exact hlang n
      have h3 : (D * (n + 1) + 1) ^ k ≤ ((D + 1) * (n + 1)) ^ k :=
        Nat.pow_le_pow_left (by nlinarith) k
      calc (n + 1) * (n + 1) ^ k = (n + 1) ^ (k + 1) := by ring
        _ ≤ c * RegGrowth.accCount M M.start n := h1
        _ ≤ c * (C * (D * (n + 1) + 1) ^ k) := Nat.mul_le_mul_left _ h2
        _ ≤ c * (C * ((D + 1) * (n + 1)) ^ k) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)
        _ = K * (n + 1) ^ k := by rw [hK, mul_pow]; ring
    have hn := hstep (max N K) (le_max_left _ _)
    have hpos : 0 < (max N K + 1) ^ k := Nat.pow_pos (Nat.succ_pos _)
    have hle : max N K + 1 ≤ K := Nat.le_of_mul_le_mul_right hn hpos
    have : K ≤ max N K := le_max_right _ _
    omega
  obtain ⟨F, hFcov⟩ := RegGrowth.exists_pattern_cover hamb (Fintype.card σ) M.start k
    (Finset.card_le_univ _) (RegGrowth.reaches_refl _) hchain
  refine ⟨F, fun w => ?_⟩
  have hmem : M.evalFrom M.start (f w) ∈ M.accept := by
    have hin : f w ∈ M.accepts := by
      rw [hM]
      exact ⟨w, rfl⟩
    exact hin
  exact hFcov (f w) hmem

/-- **A rational function with `O(n^k)` outputs factors through the sorted identity.**  For
`k ≥ 1`, a rational function with `O(n^k)` outputs is a rational pre-composition and
post-composition of `sortedFun k`. -/
theorem exists_rational_factor_through_sorted {A B : Type} [Finite A] [Finite B]
    {f : List A → List B} (hf : IsRationalFun f) {k : ℕ} (hk : 1 ≤ k)
    (hC : ∃ C : ℕ, ∀ n, (f '' {w : List A | w.length ≤ n}).ncard ≤ C * (n + 1) ^ k) :
    ∃ (g : List A → List (Fin k)) (h : List (Fin k) → List B),
      IsRationalFun g ∧ IsRationalFun h ∧ ∀ w : List A, h (sortedFun k (g w)) = f w := by
  classical
  obtain ⟨C, hCbound⟩ := hC
  obtain ⟨F, hF⟩ := exists_pattern_cover_range hf hCbound
  obtain ⟨e, he, hcov⟩ := exists_rational_cover_of_patterns (B := B) hk F
  have hhrat : IsRationalFun (fun v : List (Fin k) => e (sortedFun k v)) :=
    isRationalFun_comp (isRationalFun_sortedFun k) he
  have hrange : ∀ w : List A, ∃ v : List (Fin k), e (sortedFun k v) = f w := by
    intro w
    obtain ⟨P, hPF, c, hPc⟩ := hF w
    obtain ⟨u, hu⟩ := hcov P hPF c
    exact ⟨sortedFun k u, by rw [sortedFun_idem, hu, ← hPc]⟩
  obtain ⟨d, hd, hdspec⟩ := exists_rationalFun_section hhrat
  refine ⟨fun w => d (f w), fun v => e (sortedFun k v), isRationalFun_comp hf hd, hhrat,
    fun w => ?_⟩
  have hsec : e (sortedFun k (d (f w))) = f w :=
    hdspec (f w) ((hrange w).imp fun v hv => hv.symm)
  show e (sortedFun k (sortedFun k (d (f w)))) = f w
  rw [sortedFun_idem]
  exact hsec

/-! ### The counterexample at `k = 0` -/

/-- The rational function that maps the empty word to itself and every other word to `[true]`: it
has two outputs in all, so `O(1)` of them, but it is not constant. -/
noncomputable def firstLetterFun (w : List Bool) : List Bool :=
  if w = [] then [] else [true]

lemma isRationalFun_firstLetterFun : IsRationalFun firstLetterFun := by
  classical
  have h := isRationalFun_ite_lang (L := ({[]} : Language Bool)) (isRegular_singleton [])
    (f := fun _ : List Bool => ([] : List Bool)) (g := fun _ : List Bool => [true])
    (isRationalFun_const _) (isRationalFun_const _)
  refine h.congr (fun w v => ?_)
  have hmem : (w ∈ ({[]} : Language Bool)) = (w = []) := rfl
  simp only [firstLetterFun, hmem]

/-- The number of outputs of `firstLetterFun` is at most `2`, so it is `O(n^0)`. -/
lemma outCount_firstLetterFun (n : ℕ) :
    (firstLetterFun '' {w : List Bool | w.length ≤ n}).ncard ≤ 2 * (n + 1) ^ 0 := by
  have hsub : firstLetterFun '' {w : List Bool | w.length ≤ n} ⊆ {[], [true]} := by
    rintro v ⟨w, -, rfl⟩
    by_cases h : w = []
    · rw [firstLetterFun, if_pos h]
      exact Set.mem_insert _ _
    · rw [firstLetterFun, if_neg h]
      exact Set.mem_insert_of_mem _ rfl
  have hfin : ({[], [true]} : Set (List Bool)).Finite := Set.toFinite _
  calc (firstLetterFun '' {w : List Bool | w.length ≤ n}).ncard
      ≤ ({[], [true]} : Set (List Bool)).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ 2 := by
        refine le_trans (Set.ncard_insert_le _ _) ?_
        simp
    _ = 2 * (n + 1) ^ 0 := by ring

/-- `firstLetterFun` is not constant. -/
lemma firstLetterFun_not_const : firstLetterFun [] ≠ firstLetterFun [true] := by
  rw [firstLetterFun, firstLetterFun, if_pos rfl, if_neg (by simp)]
  simp

end Transducers.Exercises
