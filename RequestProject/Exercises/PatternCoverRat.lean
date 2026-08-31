/-
The rational function that writes the words of finitely many `k`-patterns: the encoding of the
index of the pattern in the first block of a sorted word.
-/
import RequestProject.Exercises.PatternCover
import RequestProject.Exercises.SortedPattern

/-!
# One rational function for finitely many `k`-patterns

`Transducers.Exercises.patEmit` turns a sorted word `a_1^{c_1} ⋯ a_k^{c_k}` into the word
`us 0 · (xs 0)^{c_1} ⋯ us k` of *one* `k`-pattern.  The cover of a language of polynomial growth
(`Transducers.Exercises.RegGrowth.exists_pattern_cover`) consists of *finitely many* patterns, and
this file builds a single rational function whose values include all their words:

* `Transducers.Exercises.sortedOfCounts` — the sorted word with prescribed numbers of occurrences;
* `Transducers.Exercises.shrink` — the sequential rewriting that keeps only every `r`-th letter
  `a_1` and all other letters, so that a first block of `i + r · c` letters `a_1` becomes one of
  `c` letters;
* `Transducers.Exercises.exists_rational_cover_of_patterns` — writing `c_1 = i + r · c` with
  `i < r` for the number of letters `a_1`, the residue `i` selects the pattern and the quotient
  `c` is its first exponent.  The residue is read by a finite automaton, so the case distinction
  is rational (`Transducers.isRationalFun_ite`).

This is what makes the *index* of the pattern in the finite cover harmless: `k` exponents are
still available, because the first one carries the index only through its residue.
-/

namespace Transducers.Exercises

open Transducers

/-! ### Sorted words with prescribed numbers of occurrences -/

/-- A constant function is rational. -/
lemma isRationalFun_const {A B : Type} [Finite A] [Finite B] (p : List B) :
    IsRationalFun (fun _ : List A => p) := by
  have hval : ∀ w : List A, seqFinEval (fun (_ : Unit) (_ : A) => ())
      (fun _ _ => ([] : List B)) (fun _ => p) () w = p := by
    intro w
    induction w with
    | nil => rfl
    | cons a w ih => rw [seqFinEval_cons, List.nil_append]; exact ih
  have h := isRationalFun_seqFinEval (fun (_ : Unit) (_ : A) => ())
    (() : Unit) (fun _ _ => ([] : List B)) (fun _ => p)
  exact (funext hval : (seqFinEval (fun (_ : Unit) (_ : A) => ())
    (fun _ _ => ([] : List B)) (fun _ => p) ()) = fun _ => p) ▸ h


section Counts

variable {k : ℕ}

lemma cnt_append (v v' : List (Fin k)) (i : ℕ) : cnt (v ++ v') i = cnt v i + cnt v' i := by
  induction v with
  | nil => simp
  | cons a v ih => rw [List.cons_append, cnt_cons, cnt_cons, ih]; omega

lemma cnt_replicate (m : ℕ) (a : Fin k) (i : ℕ) :
    cnt (List.replicate m a) i = if i = (a : ℕ) then m else 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, cnt_cons, ih]; split <;> omega

/-- The blocks `a^(n a)`, for the letters `a` of a list, written one after the other. -/
def blocksOf (n : ℕ → ℕ) : List (Fin k) → List (Fin k)
  | [] => []
  | a :: l => List.replicate (n (a : ℕ)) a ++ blocksOf n l

/-- The sorted word with `n i` occurrences of the letter of index `i`. -/
def sortedOfCounts (k : ℕ) (n : ℕ → ℕ) : List (Fin k) :=
  blocksOf n (List.finRange k)

lemma mem_blocksOf {n : ℕ → ℕ} {l : List (Fin k)} {a : Fin k} (h : a ∈ blocksOf n l) : a ∈ l := by
  induction l with
  | nil => exact absurd h (by simp [blocksOf])
  | cons b l ih =>
      rw [blocksOf, List.mem_append] at h
      rcases h with h | h
      · rw [List.eq_of_mem_replicate h]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

lemma blocksOf_pairwise {n : ℕ → ℕ} {l : List (Fin k)} (hl : l.Pairwise (· ≤ ·)) :
    (blocksOf n l).Pairwise (· ≤ ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rw [blocksOf]
      refine List.pairwise_append.mpr ⟨?_, ih hl.2, fun x hx y hy => ?_⟩
      · exact List.pairwise_replicate.mpr (Or.inr le_rfl)
      · rw [List.eq_of_mem_replicate hx]
        exact hl.1 y (mem_blocksOf hy)

lemma cnt_blocksOf (n : ℕ → ℕ) (l : List (Fin k)) {j : ℕ} (hj : j < k) :
    cnt (blocksOf n l) j = l.count ⟨j, hj⟩ * n j := by
  induction l with
  | nil => simp [blocksOf]
  | cons a l ih =>
      rw [blocksOf, cnt_append, ih, cnt_replicate]
      by_cases h : (⟨j, hj⟩ : Fin k) = a
      · rw [← h, List.count_cons_self, if_pos (rfl : j = ((⟨j, hj⟩ : Fin k) : ℕ))]
        ring
      · rw [List.count_cons_of_ne (fun hc => h hc.symm),
          if_neg (fun hc : j = (a : ℕ) => h (Fin.ext hc)), Nat.zero_add]

/-- The word `sortedOfCounts k n` is sorted. -/
lemma sortedOfCounts_sorted (k : ℕ) (n : ℕ → ℕ) :
    (sortedOfCounts k n).Pairwise (· ≤ ·) :=
  blocksOf_pairwise (List.pairwise_le_finRange k)

/-- The letter of index `j` occurs `n j` times in `sortedOfCounts k n`. -/
lemma cnt_sortedOfCounts (k : ℕ) (n : ℕ → ℕ) {j : ℕ} (hj : j < k) :
    cnt (sortedOfCounts k n) j = n j := by
  rw [sortedOfCounts, cnt_blocksOf n _ hj,
    List.count_eq_one_of_mem (List.nodup_finRange k) (List.mem_finRange _), one_mul]

end Counts

/-! ### Keeping only every `r`-th letter of the first block -/

section Shrink

variable (r' k : ℕ)

/-- The state of the automaton that counts the letters `a_1` modulo `r`. -/
def shrinkMu : Fin (r' + 1) → Fin k → Fin (r' + 1) :=
  fun t a => if (a : ℕ) = 0 then ⟨((t : ℕ) + 1) % (r' + 1), Nat.mod_lt _ (Nat.succ_pos r')⟩ else t

/-- The output of the rewriting that keeps every `r`-th letter `a_1` and every other letter. -/
def shrinkPsi : Fin (r' + 1) → Fin k → List (Fin k) :=
  fun t a => if (a : ℕ) = 0 then (if (t : ℕ) = r' then [a] else []) else [a]

/-- The rewriting that keeps only every `r`-th letter `a_1`, started with `t` letters `a_1`
already read. -/
def shrinkFrom (t : Fin (r' + 1)) : List (Fin k) → List (Fin k) :=
  seqFinEval (shrinkMu r' k) (shrinkPsi r' k) (fun _ => []) t

/-- The rewriting that keeps only every `r`-th letter `a_1` and all other letters. -/
def shrink : List (Fin k) → List (Fin k) := shrinkFrom r' k 0

variable {r' k}

lemma shrinkFrom_nil (t : Fin (r' + 1)) : shrinkFrom r' k t [] = [] := rfl

lemma shrinkFrom_cons (t : Fin (r' + 1)) (a : Fin k) (v : List (Fin k)) :
    shrinkFrom r' k t (a :: v) =
      shrinkPsi r' k t a ++ shrinkFrom r' k (shrinkMu r' k t a) v := rfl

lemma shrinkFrom_sublist (t : Fin (r' + 1)) (v : List (Fin k)) :
    List.Sublist (shrinkFrom r' k t v) v := by
  induction v generalizing t with
  | nil => exact List.Sublist.refl _
  | cons a v ih =>
      rw [shrinkFrom_cons]
      by_cases h : (a : ℕ) = 0
      · by_cases h' : (t : ℕ) = r'
        · rw [show shrinkPsi r' k t a = [a] by simp only [shrinkPsi, if_pos h, if_pos h'],
            List.singleton_append]
          exact List.Sublist.cons₂ a (ih _)
        · rw [show shrinkPsi r' k t a = [] by simp only [shrinkPsi, if_pos h, if_neg h'],
            List.nil_append]
          exact List.Sublist.cons a (ih _)
      · rw [show shrinkPsi r' k t a = [a] by simp only [shrinkPsi, if_neg h],
          List.singleton_append]
        exact List.Sublist.cons₂ a (ih _)

/-- The three values of the output of the rewriting. -/
lemma shrinkPsi_zero_keep {t : Fin (r' + 1)} {a : Fin k} (ha : (a : ℕ) = 0)
    (h : (t : ℕ) = r') : shrinkPsi r' k t a = [a] := by
  simp only [shrinkPsi, if_pos ha, if_pos h]

lemma shrinkPsi_zero_drop {t : Fin (r' + 1)} {a : Fin k} (ha : (a : ℕ) = 0)
    (h : (t : ℕ) ≠ r') : shrinkPsi r' k t a = [] := by
  simp only [shrinkPsi, if_pos ha, if_neg h]

lemma shrinkPsi_ne {t : Fin (r' + 1)} {a : Fin k} (ha : (a : ℕ) ≠ 0) :
    shrinkPsi r' k t a = [a] := by
  simp only [shrinkPsi, if_neg ha]

lemma shrinkMu_zero {t : Fin (r' + 1)} {a : Fin k} (ha : (a : ℕ) = 0) :
    ((shrinkMu r' k t a : Fin (r' + 1)) : ℕ) = ((t : ℕ) + 1) % (r' + 1) := by
  simp only [shrinkMu, if_pos ha]

lemma shrinkMu_ne {t : Fin (r' + 1)} {a : Fin k} (ha : (a : ℕ) ≠ 0) :
    shrinkMu r' k t a = t := by
  simp only [shrinkMu, if_neg ha]

/-- The rewriting keeps `(t + c) / r` of the `c` letters `a_1`, where `t` is the number of
letters `a_1` already read. -/
lemma cnt_shrinkFrom_zero (t : Fin (r' + 1)) (v : List (Fin k)) :
    cnt (shrinkFrom r' k t v) 0 = ((t : ℕ) + cnt v 0) / (r' + 1) := by
  induction v generalizing t with
  | nil =>
      show 0 = ((t : ℕ) + 0) / (r' + 1)
      rw [Nat.add_zero, Nat.div_eq_of_lt t.isLt]
  | cons a v ih =>
      rw [shrinkFrom_cons, cnt_append, ih]
      by_cases ha : (a : ℕ) = 0
      · have hcnt : cnt (a :: v) 0 = cnt v 0 + 1 := by rw [cnt_cons, if_pos ha.symm]
        have hone : cnt [a] 0 = 1 := by rw [cnt_cons, cnt_nil, if_pos ha.symm]
        rw [hcnt]
        by_cases h' : (t : ℕ) = r'
        · have hmu : ((shrinkMu r' k t a : Fin (r' + 1)) : ℕ) = 0 := by
            rw [shrinkMu_zero ha, h', Nat.mod_self]
          have harith : ((r' : ℕ) + (cnt v 0 + 1)) / (r' + 1) = cnt v 0 / (r' + 1) + 1 := by
            rw [show (r' : ℕ) + (cnt v 0 + 1) = cnt v 0 + 1 * (r' + 1) by ring,
              Nat.add_mul_div_right _ _ (Nat.succ_pos r')]
          rw [shrinkPsi_zero_keep ha h', hone, hmu, h', Nat.zero_add, harith]
          omega
        · have hlt : (t : ℕ) + 1 < r' + 1 := by have := t.isLt; omega
          have hmu : ((shrinkMu r' k t a : Fin (r' + 1)) : ℕ) = (t : ℕ) + 1 := by
            rw [shrinkMu_zero ha, Nat.mod_eq_of_lt hlt]
          rw [shrinkPsi_zero_drop ha h', hmu, cnt_nil, Nat.zero_add]
          congr 1
          omega
      · have hcnt : cnt (a :: v) 0 = cnt v 0 := cnt_cons_of_ne (fun h => ha h.symm) v
        have hzero : cnt [a] 0 = 0 := by rw [cnt_cons, cnt_nil, if_neg (fun h => ha h.symm)]
        rw [shrinkPsi_ne ha, hzero, shrinkMu_ne ha, hcnt, Nat.zero_add]

/-- The rewriting keeps all the letters other than `a_1`. -/
lemma cnt_shrinkFrom_ne (t : Fin (r' + 1)) (v : List (Fin k)) {j : ℕ} (hj : j ≠ 0) :
    cnt (shrinkFrom r' k t v) j = cnt v j := by
  induction v generalizing t with
  | nil => rfl
  | cons a v ih =>
      rw [shrinkFrom_cons, cnt_append, ih, cnt_cons]
      by_cases ha : (a : ℕ) = 0
      · have hne : ¬ (j = (a : ℕ)) := by omega
        rw [if_neg hne, Nat.add_zero]
        by_cases h' : (t : ℕ) = r'
        · rw [shrinkPsi_zero_keep ha h', cnt_cons, cnt_nil, if_neg hne, Nat.zero_add]
        · rw [shrinkPsi_zero_drop ha h', cnt_nil, Nat.zero_add]
      · rw [shrinkPsi_ne ha, cnt_cons, cnt_nil, Nat.zero_add, Nat.add_comm]


theorem isRationalFun_shrink (r' k : ℕ) : IsRationalFun (shrink r' k) :=
  isRationalFun_seqFinEval _ _ _ _

end Shrink

/-! ### Selecting a pattern by the residue of the first block -/

/-- The number of letters `a_1`, modulo `r`, is the state of a finite automaton. -/
lemma strTrans_shrinkMu (r' k : ℕ) (v : List (Fin k)) (t : Fin (r' + 1)) :
    ((strTrans (shrinkMu r' k) v t : Fin (r' + 1)) : ℕ) = ((t : ℕ) + cnt v 0) % (r' + 1) := by
  induction v generalizing t with
  | nil => simp [strTrans, Nat.mod_eq_of_lt t.isLt]
  | cons a v ih =>
      have hstep : strTrans (shrinkMu r' k) (a :: v) t
          = strTrans (shrinkMu r' k) v (shrinkMu r' k t a) := by simp [strTrans]
      rw [hstep, ih]
      by_cases ha : (a : ℕ) = 0
      · have hcnt : cnt (a :: v) 0 = cnt v 0 + 1 := by rw [cnt_cons, if_pos ha.symm]
        rw [hcnt, shrinkMu_zero ha, Nat.mod_add_mod]
        congr 1
        omega
      · have hcnt : cnt (a :: v) 0 = cnt v 0 := cnt_cons_of_ne (fun h => ha h.symm) v
        rw [hcnt, shrinkMu_ne ha]

/-- **A finite family of rational functions can be selected by the residue of the number of
letters `a_1`.** -/
lemma exists_rational_select {B : Type} [Finite B] (k r' : ℕ)
    (E : ℕ → List (Fin k) → List B) (hE : ∀ i, IsRationalFun (E i)) :
    ∀ m : ℕ, ∃ e : List (Fin k) → List B, IsRationalFun e ∧
      ∀ v : List (Fin k), cnt v 0 % (r' + 1) < m → e v = E (cnt v 0 % (r' + 1)) v := by
  classical
  intro m
  induction m with
  | zero => exact ⟨fun _ => [], isRationalFun_const _, fun v hv => absurd hv (Nat.not_lt_zero _)⟩
  | succ m ih =>
      obtain ⟨e, he, hspec⟩ := ih
      have hst : ∀ v : List (Fin k),
          ((strTrans (shrinkMu r' k) v (0 : Fin (r' + 1)) : Fin (r' + 1)) : ℕ)
            = cnt v 0 % (r' + 1) := by
        intro v
        rw [strTrans_shrinkMu]
        simp
      refine ⟨fun v => if ((strTrans (shrinkMu r' k) v (0 : Fin (r' + 1)) : Fin (r' + 1)) : ℕ) = m
          then E m v else e v,
        isRationalFun_ite (shrinkMu r' k) (0 : Fin (r' + 1)) (fun t => (t : ℕ) = m) (hE m) he,
        fun v hv => ?_⟩
      show (if ((strTrans (shrinkMu r' k) v (0 : Fin (r' + 1)) : Fin (r' + 1)) : ℕ) = m
        then E m v else e v) = E (cnt v 0 % (r' + 1)) v
      by_cases hcase : cnt v 0 % (r' + 1) = m
      · rw [if_pos (by rw [hst v, hcase]), hcase]
      · rw [if_neg (by rw [hst v]; exact hcase)]
        exact hspec v (by omega)

/-- **One rational function for finitely many `k`-patterns.**  For `k ≥ 1` there is a rational
function on the sorted words of `{a_1, …, a_k}*` whose values include the words of all the
patterns of a finite list.  The number of letters `a_1` is written `i + r · c` with `i` the index
of the pattern in the list and `c` the exponent of its first loop. -/
theorem exists_rational_cover_of_patterns {B : Type} [Finite B] {k : ℕ} (hk : 1 ≤ k)
    (F : List ((ℕ → List B) × (ℕ → List B))) :
    ∃ e : List (Fin k) → List B, IsRationalFun e ∧
      ∀ P ∈ F, ∀ c : ℕ → ℕ, ∃ u : List (Fin k), e (sortedFun k u) = chainWord P.1 P.2 k c := by
  classical
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, F.length = r' + 1 ∨ F = [] := by
    cases hF : F with
    | nil => exact ⟨0, Or.inr rfl⟩
    | cons P₀ Fs => exact ⟨Fs.length, Or.inl (by rw [List.length_cons])⟩
  rcases hr' with hlen | hnil
  swap
  · exact ⟨fun _ => [], isRationalFun_const _, by rw [hnil]; simp⟩
  set Pf : ℕ → (ℕ → List B) × (ℕ → List B) :=
    fun i => F.getD i (fun _ => [], fun _ => []) with hPf
  set E : ℕ → List (Fin k) → List B :=
    fun i v => patEmit (Pf i).1 (Pf i).2 k (shrink r' k v) with hE
  have hErat : ∀ i, IsRationalFun (E i) := fun i =>
    isRationalFun_comp (isRationalFun_shrink r' k) (isRationalFun_patEmit (Pf i).1 (Pf i).2 k)
  obtain ⟨e, he, hspec⟩ := exists_rational_select k r' E hErat (r' + 1)
  refine ⟨e, he, fun P hP c => ?_⟩
  obtain ⟨i, hi, hPi⟩ : ∃ i, i < r' + 1 ∧ Pf i = P := by
    obtain ⟨i, hi, hval⟩ := List.mem_iff_getElem.mp hP
    refine ⟨i, by omega, ?_⟩
    rw [hPf]
    simp only
    rw [List.getD_eq_getElem F _ hi, hval]
  set n : ℕ → ℕ := fun j => if j = 0 then i + (r' + 1) * c 0 else c j with hn
  refine ⟨sortedOfCounts k n, ?_⟩
  have hsorted := sortedOfCounts_sorted k n
  have hk0 : (0 : ℕ) < k := hk
  have hcnt0 : cnt (sortedOfCounts k n) 0 = i + (r' + 1) * c 0 := by
    rw [cnt_sortedOfCounts k n hk0, hn]
    simp
  have hmod : cnt (sortedOfCounts k n) 0 % (r' + 1) = i := by
    rw [hcnt0, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  rw [sortedFun_of_sorted hsorted, hspec _ (by rw [hmod]; exact hi), hmod, hE]
  simp only
  have hsub : List.Sublist (shrink r' k (sortedOfCounts k n)) (sortedOfCounts k n) :=
    shrinkFrom_sublist _ _
  have hssorted : (shrink r' k (sortedOfCounts k n)).Pairwise (· ≤ ·) :=
    hsorted.sublist hsub
  rw [patEmit_sorted (Pf i).1 (Pf i).2 k hssorted, hPi]
  refine RegGrowth.chainWord_congr_counts P.1 P.2 k (fun j hj => ?_)
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · rw [shrink, cnt_shrinkFrom_zero, hcnt0]
    show (((0 : Fin (r' + 1)) : ℕ) + (i + (r' + 1) * c 0)) / (r' + 1) = c 0
    rw [Fin.val_zero, Nat.zero_add, Nat.add_mul_div_left _ _ (Nat.succ_pos r'),
      Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [shrink, cnt_shrinkFrom_ne _ _ (by omega), cnt_sortedOfCounts k n hj, hn]
    simp only
    rw [if_neg (by omega)]

end Transducers.Exercises
