/-
The ruler word, and the `n + 1` local conditions that single it out.

This is the combinatorial core of the construction of `RequestProject/Exercises/TwoDFAExp.lean`,
which proves the claim of Exercise `exer:2dfa-complexity` of the chapter *Two-way transducers*
(`2dfa.tex`) of *Transducers* (M. Bojańczyk) by a construction that the book does not give.

The *ruler word* of height `h` over the letters `j, j + 1, …, j + h` is

  `rul j 0 = [j]`,   `rul j (h + 1) = rul j h ++ (j + h + 1) :: rul j h`,

so `rul 0 2 = 0 1 0 2 0 1 0`; it has length `2 ^ (h + 1) - 1`.

For a level `j`, write `subLv j v` for the subsequence of the letters of `v` that are at least `j`.
The condition

  `Cond j v :  subLv j v = intl j (subLv (j + 1) v)`,     where `intl j [x₁, …, x_m] = j x₁ j ⋯ x_m j`,

says that, among the letters at least `j`, those equal to `j` and those larger than `j` alternate,
beginning and ending with `j`.  The two facts proved here are that `rul 0 n` satisfies `Cond j` for
every `j ≤ n` (`cond_rul`), and that it is the *only* word over the letters `0, …, n` that does
(`eq_rul_of_cond`).  Since each `Cond j` is checked by a one-way automaton with three states
(`dfold_expJ_iff`), the word `rul 0 n`, of exponential length, is the shortest — indeed the only —
word accepted by a two-way automaton with `4 * (n + 1)` states.
-/
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace Transducers
namespace Exercises
namespace Ruler

/-! ## Subsequences of high letters, interleaving, and the ruler word -/

/-- The subsequence of the letters of `v` that are at least `j`. -/
def subLv (j : ℕ) (v : List ℕ) : List ℕ := v.filter (fun a => decide (j ≤ a))

@[simp] lemma subLv_nil (j : ℕ) : subLv j [] = [] := rfl

lemma subLv_cons (j a : ℕ) (v : List ℕ) :
    subLv j (a :: v) = if j ≤ a then a :: subLv j v else subLv j v := by
  unfold subLv
  by_cases h : j ≤ a <;> simp [h]

lemma subLv_append (j : ℕ) (u v : List ℕ) : subLv j (u ++ v) = subLv j u ++ subLv j v :=
  List.filter_append _ _

@[simp] lemma subLv_zero (v : List ℕ) : subLv 0 v = v := by
  unfold subLv; simp

lemma mem_subLv (j : ℕ) (v : List ℕ) {a : ℕ} (h : a ∈ subLv j v) : j ≤ a := by
  have := List.of_mem_filter h
  simpa using this

lemma subLv_eq_self {j : ℕ} {v : List ℕ} (h : ∀ a ∈ v, j ≤ a) : subLv j v = v :=
  List.filter_eq_self.2 (fun a ha => by simpa using h a ha)

lemma subLv_eq_nil {j : ℕ} {v : List ℕ} (h : ∀ a ∈ v, a < j) : subLv j v = [] :=
  List.filter_eq_nil_iff.2 (fun a ha => by simpa using Nat.not_le.2 (h a ha))

lemma subLv_subLv (j j' : ℕ) (hj : j ≤ j') (v : List ℕ) : subLv j' (subLv j v) = subLv j' v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      rw [subLv_cons, subLv_cons]
      by_cases h : j ≤ a
      · rw [if_pos h, subLv_cons, ih]
      · rw [if_neg h, ih, if_neg (by omega)]

/-- `ilv j [x₁, …, x_m] = x₁ j x₂ j ⋯ x_m j`. -/
def ilv (j : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => x :: j :: ilv j xs

/-- `intl j [x₁, …, x_m] = j x₁ j x₂ j ⋯ x_m j`. -/
def intl (j : ℕ) (v : List ℕ) : List ℕ := j :: ilv j v

@[simp] lemma ilv_nil (j : ℕ) : ilv j [] = [] := rfl

@[simp] lemma ilv_cons (j x : ℕ) (xs : List ℕ) : ilv j (x :: xs) = x :: j :: ilv j xs := rfl

lemma ilv_append (j : ℕ) (u v : List ℕ) : ilv j (u ++ v) = ilv j u ++ ilv j v := by
  induction u with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma intl_append (j x : ℕ) (u v : List ℕ) :
    intl j (u ++ x :: v) = intl j u ++ x :: intl j v := by
  unfold intl
  rw [ilv_append]
  simp

@[simp] lemma length_ilv (j : ℕ) (v : List ℕ) : (ilv j v).length = 2 * v.length := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [ih]; omega

/-- The ruler word of height `h` over the letters `j, …, j + h`. -/
def rul (j : ℕ) : ℕ → List ℕ
  | 0 => [j]
  | h + 1 => rul j h ++ (j + h + 1) :: rul j h

lemma rul_zero (j : ℕ) : rul j 0 = [j] := rfl

lemma rul_succ (j h : ℕ) : rul j (h + 1) = rul j h ++ (j + h + 1) :: rul j h := rfl

lemma length_rul (j h : ℕ) : (rul j h).length = 2 ^ (h + 1) - 1 := by
  induction h with
  | zero => rw [rul_zero]; simp
  | succ h ih =>
      rw [rul_succ]
      simp only [List.length_append, List.length_cons, ih]
      have : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
      ring_nf
      omega

lemma rul_ne_nil (j h : ℕ) : rul j h ≠ [] := by
  cases h with
  | zero => simp [rul_zero]
  | succ h => simp [rul_succ]

lemma mem_rul (j h : ℕ) {a : ℕ} (ha : a ∈ rul j h) : j ≤ a ∧ a ≤ j + h := by
  induction h with
  | zero =>
      rw [rul_zero] at ha
      simp at ha
      omega
  | succ h ih =>
      rw [rul_succ] at ha
      rcases List.mem_append.1 ha with h1 | h1
      · have := ih h1; omega
      · rcases List.mem_cons.1 h1 with rfl | h2
        · omega
        · have := ih h2; omega

lemma subLv_rul_self (j h : ℕ) : subLv j (rul j h) = rul j h :=
  subLv_eq_self (fun _ ha => (mem_rul j h ha).1)

/-- Removing the lowest letter of a ruler word leaves the ruler word one level up. -/
lemma subLv_succ_rul (j h : ℕ) : subLv (j + 1) (rul j (h + 1)) = rul (j + 1) h := by
  induction h with
  | zero =>
      rw [rul_succ, rul_zero, subLv_append, subLv_cons]
      simp [subLv_cons, rul_zero]
  | succ h ih =>
      rw [rul_succ, subLv_append, subLv_cons, if_pos (by omega), ih, rul_succ]
      congr 2
      omega

lemma subLv_succ_rul_zero (j : ℕ) : subLv (j + 1) (rul j 0) = [] := by
  rw [rul_zero]; rw [subLv_cons, if_neg (by omega)]; rfl

/-- A ruler word is the interleaving, with its lowest letter, of the ruler word one level up. -/
lemma rul_succ_eq_intl (j h : ℕ) : rul j (h + 1) = intl j (rul (j + 1) h) := by
  induction h with
  | zero => rw [rul_succ, rul_zero, rul_zero]; simp [intl]
  | succ h ih =>
      rw [rul_succ, ih, rul_succ, intl_append]
      congr 2
      omega

/-- Every ruler word satisfies its own lowest-level condition. -/
lemma cond_rul_self (j h : ℕ) : subLv j (rul j h) = intl j (subLv (j + 1) (rul j h)) := by
  rw [subLv_rul_self]
  cases h with
  | zero => rw [subLv_succ_rul_zero, rul_zero]; rfl
  | succ h => rw [subLv_succ_rul, rul_succ_eq_intl]

/-! ## The conditions satisfied by `rul 0 n`, and their rigidity -/

/-- The condition of level `j`: among the letters at least `j`, those equal to `j` and those larger
alternate, beginning and ending with `j`. -/
def Cond (j : ℕ) (v : List ℕ) : Prop := subLv j v = intl j (subLv (j + 1) v)

lemma subLv_rul_zero (n : ℕ) : ∀ j ≤ n, subLv j (rul 0 n) = rul j (n - j) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      have hj' : j ≤ n := by omega
      rw [← subLv_subLv j (j + 1) (by omega), ih hj']
      have : n - j = (n - (j + 1)) + 1 := by omega
      rw [this, subLv_succ_rul]

/-- **The ruler word satisfies every condition.** -/
lemma cond_rul (n : ℕ) : ∀ j ≤ n, Cond j (rul 0 n) := by
  intro j hj
  unfold Cond
  have h1 : subLv j (rul 0 n) = rul j (n - j) := subLv_rul_zero n j hj
  have h2 : subLv (j + 1) (rul 0 n) = subLv (j + 1) (rul j (n - j)) := by
    rw [← subLv_subLv j (j + 1) (by omega), h1]
  rw [h1, h2]
  conv_lhs => rw [← subLv_rul_self j (n - j)]
  exact cond_rul_self j (n - j)

/-- **The ruler word is the only word over `0, …, n` satisfying every condition.** -/
theorem eq_rul_of_cond {n : ℕ} {v : List ℕ} (hle : ∀ a ∈ v, a ≤ n)
    (hcond : ∀ j ≤ n, Cond j v) : v = rul 0 n := by
  have key : ∀ d j, j + d = n + 1 → subLv j v = subLv j (rul 0 n) := by
    intro d
    induction d with
    | zero =>
        intro j hj
        have hjn : j = n + 1 := by omega
        subst hjn
        rw [subLv_eq_nil (fun a ha => by have := hle a ha; omega),
          subLv_eq_nil (fun a ha => by have := (mem_rul 0 n ha).2; omega)]
    | succ d ih =>
        intro j hj
        have hjn : j ≤ n := by omega
        have h1 := hcond j hjn
        have h2 := ih (j + 1) (by omega)
        unfold Cond at h1
        rw [h1, h2, ← (cond_rul n j hjn : Cond j (rul 0 n))]
  have := key (n + 1) 0 (by omega)
  simpa using this

/-! ## Checking a condition with a three-state one-way automaton -/

/-- The states of the one-way automaton that checks the condition of level `j`: `expJ` expects the
next letter at least `j` to be equal to `j`, `expHi` expects it to be larger, and `dead` records a
violation. -/
inductive PSt where
  | expJ : PSt
  | expHi : PSt
  | dead : PSt
  deriving DecidableEq, Fintype, Repr

/-- One step of the automaton that checks the condition of level `j`. -/
def dstep (j a : ℕ) : PSt → PSt
  | .dead => .dead
  | .expJ => if a < j then .expJ else if a = j then .expHi else .dead
  | .expHi => if a < j then .expHi else if a = j then .dead else .expJ

/-- The run of the automaton that checks the condition of level `j`. -/
def dfold (j : ℕ) (v : List ℕ) (s : PSt) : PSt := v.foldl (fun s a => dstep j a s) s

@[simp] lemma dfold_nil (j : ℕ) (s : PSt) : dfold j [] s = s := rfl

@[simp] lemma dfold_cons (j a : ℕ) (v : List ℕ) (s : PSt) :
    dfold j (a :: v) s = dfold j v (dstep j a s) := rfl

@[simp] lemma dstep_dead (j a : ℕ) : dstep j a .dead = .dead := rfl

lemma dstep_of_lt {j a : ℕ} (h : a < j) (s : PSt) : dstep j a s = s := by
  cases s <;> simp only [dstep, if_pos h]

lemma dstep_self_expJ (j : ℕ) : dstep j j .expJ = .expHi := by
  simp [dstep]

lemma dstep_self_expHi (j : ℕ) : dstep j j .expHi = .dead := by
  simp [dstep]

lemma dstep_of_gt_expJ {j a : ℕ} (h : j < a) : dstep j a .expJ = .dead := by
  simp only [dstep, if_neg (by omega : ¬ a < j), if_neg (by omega : ¬ a = j)]

lemma dstep_of_gt_expHi {j a : ℕ} (h : j < a) : dstep j a .expHi = .expJ := by
  simp only [dstep, if_neg (by omega : ¬ a < j), if_neg (by omega : ¬ a = j)]

@[simp] lemma dfold_dead (j : ℕ) (v : List ℕ) : dfold j v .dead = .dead := by
  induction v with
  | nil => rfl
  | cons a v ih => rw [dfold_cons, dstep_dead, ih]

/-- The low letters do not affect the automaton of level `j`. -/
lemma dfold_subLv (j : ℕ) (v : List ℕ) (s : PSt) : dfold j v s = dfold j (subLv j v) s := by
  induction v generalizing s with
  | nil => rfl
  | cons a v ih =>
      rw [subLv_cons]
      by_cases h : j ≤ a
      · rw [if_pos h, dfold_cons, dfold_cons, ih]
      · rw [if_neg h, dfold_cons, ih, dstep_of_lt (Nat.lt_of_not_le h)]

/-- The two halves of the correctness of the automaton of level `j`, on a word all of whose letters
are at least `j`. -/
lemma dfold_iff_aux (j : ℕ) : ∀ u : List ℕ, (∀ a ∈ u, j ≤ a) →
    ((dfold j u .expJ = .expHi ↔ u = intl j (subLv (j + 1) u)) ∧
     (dfold j u .expHi = .expHi ↔ u = ilv j (subLv (j + 1) u))) := by
  intro u
  induction u with
  | nil => intro _; constructor <;> simp [intl]
  | cons a u ih =>
      intro hu
      have ha : j ≤ a := hu a (by simp)
      have ihu := ih (fun b hb => hu b (by simp [hb]))
      rcases eq_or_lt_of_le ha with heq | hlt
      · -- the letter is `j` itself
        have haj : a = j := heq.symm
        subst haj
        have hsub : subLv (a + 1) (a :: u) = subLv (a + 1) u := by
          rw [subLv_cons, if_neg (by omega)]
        constructor
        · rw [dfold_cons, dstep_self_expJ, ihu.2, hsub]
          constructor
          · intro h; rw [intl, ← h]
          · intro h; rw [intl] at h; exact (List.cons_inj_right a).1 h
        · rw [dfold_cons, dstep_self_expHi, dfold_dead, hsub]
          simp only [reduceCtorEq, false_iff]
          intro hcon
          rcases hs : subLv (a + 1) u with _ | ⟨x, xs⟩
          · rw [hs, ilv_nil] at hcon; exact absurd hcon (List.cons_ne_nil _ _)
          · rw [hs, ilv_cons] at hcon
            have hx : x ∈ subLv (a + 1) u := by rw [hs]; simp
            have hax : a = x := (List.cons.inj hcon).1
            have := mem_subLv _ _ hx
            omega
      · -- the letter is larger than `j`
        have hsub : subLv (j + 1) (a :: u) = a :: subLv (j + 1) u := by
          rw [subLv_cons, if_pos (by omega)]
        constructor
        · rw [dfold_cons, dstep_of_gt_expJ hlt, dfold_dead, hsub]
          simp only [reduceCtorEq, false_iff]
          intro hcon
          rw [intl] at hcon
          have : a = j := (List.cons.inj hcon).1
          omega
        · rw [dfold_cons, dstep_of_gt_expHi hlt, ihu.1, hsub, ilv_cons]
          constructor
          · intro h; rw [intl] at h; rw [← h]
          · intro h
            rw [intl]
            exact (List.cons.inj h).2

/-- **The automaton of level `j` checks exactly the condition of level `j`.** -/
theorem dfold_expJ_iff (j : ℕ) (v : List ℕ) : dfold j v .expJ = .expHi ↔ Cond j v := by
  rw [dfold_subLv j v]
  have h := (dfold_iff_aux j (subLv j v) (fun a ha => mem_subLv j v ha)).1
  rw [h, subLv_subLv j (j + 1) (by omega)]
  rfl

end Ruler
end Exercises
end Transducers
