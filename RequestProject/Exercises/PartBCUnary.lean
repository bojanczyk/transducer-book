/-
Auxiliary facts for the solution to Exercise `exer:rational-one-letter-input` of *Transducers*
(M. Bojańczyk): a bimachine over a one-letter input alphabet.

The author's solution runs a bimachine (Theorem `thm:bimachines`) on the unary inputs.  Over a
one-letter alphabet the prefix and the suffix automaton are deterministic automata with a single
letter, so their runs are eventually periodic: there are a threshold `lam` and a period `per` such
that the state after `n` letters and the state after `n + per` letters agree for every `n >= lam`.
The output of the bimachine is the concatenation of the pieces produced in the gaps of the input,
and the piece of a gap is determined by the number of letters on its left and on its right; so, on
the inputs of a fixed length modulo `per`, increasing the length by `per` inserts one more period
of gaps in the middle, and that period produces the same pieces as the other ones.  This is the
content of `eval_replicate_period`.

Everything here is stated for the input alphabet `Unit`; a one-letter alphabet is isomorphic to it.
-/
import RequestProject.PartB.Bimachine

namespace Transducers
namespace Exercises
namespace Unary

/-! ## Eventually periodic orbits -/

/-- The orbit of a point under a self-map of a finite type is eventually periodic. -/
lemma exists_eventual_period {X : Type} [Finite X] (step : X → X) (x₀ : X) :
    ∃ l k : ℕ, 0 < k ∧ ∀ n ≥ l, step^[n + k] x₀ = step^[n] x₀ := by
  have main : ∀ i j : ℕ, i < j → step^[i] x₀ = step^[j] x₀ →
      ∃ l k : ℕ, 0 < k ∧ ∀ n ≥ l, step^[n + k] x₀ = step^[n] x₀ := by
    intro i j hlt hEq
    refine ⟨i, j - i, by omega, fun n hn => ?_⟩
    have key : ∀ d : ℕ, step^[(i + d) + (j - i)] x₀ = step^[i + d] x₀ := by
      intro d
      have e1 : (i + d) + (j - i) = d + j := by omega
      have e2 : i + d = d + i := by omega
      rw [e1, e2, Function.iterate_add_apply, Function.iterate_add_apply, hEq]
    have h := key (n - i)
    rwa [show i + (n - i) = n by omega] at h
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => step^[n] x₀)
  rcases lt_or_gt_of_ne hij with h | h
  · exact main i j h hEq
  · exact main j i h hEq.symm

lemma iterate_period_mul {X : Type} (step : X → X) (x₀ : X) {l k : ℕ}
    (h : ∀ n ≥ l, step^[n + k] x₀ = step^[n] x₀) (t : ℕ) :
    ∀ n ≥ l, step^[n + k * t] x₀ = step^[n] x₀ := by
  induction t with
  | zero => simp
  | succ t ih =>
      intro n hn
      have : n + k * (t + 1) = (n + k * t) + k := by ring
      rw [this, h _ (le_trans hn (Nat.le_add_right _ _)), ih n hn]


/-! ## Concatenating a sequence of pieces -/

/-- The concatenation `g 0 ++ g 1 ++ … ++ g (n-1)` of the first `n` pieces of a sequence. -/
def cat {B : Type} (g : ℕ → List B) (n : ℕ) : List B := ((List.range n).map g).flatten

@[simp] lemma cat_zero {B : Type} (g : ℕ → List B) : cat g 0 = [] := rfl

lemma cat_add {B : Type} (g : ℕ → List B) (a b : ℕ) :
    cat g (a + b) = cat g a ++ cat (fun t => g (a + t)) b := by
  simp [cat, List.range_add, Function.comp_def]

lemma cat_congr {B : Type} {g g' : ℕ → List B} {n : ℕ} (h : ∀ i < n, g i = g' i) :
    cat g n = cat g' n := by
  unfold cat
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

/-- If the sequence repeats with period `per` throughout the first `per * m` pieces, then their
concatenation is the concatenation of the first `per` of them, repeated `m` times. -/
lemma cat_period {B : Type} (g : ℕ → List B) (per m : ℕ)
    (h : ∀ t, t + per < per * m + per → g (t + per) = g t) :
    cat g (per * m) = (List.replicate m (cat g per)).flatten := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
      have hsplit : per * (m + 1) = per + per * m := by ring
      rw [hsplit, cat_add]
      have h' : ∀ t, t + per < per * m + per → g (per + (t + per)) = g (per + t) := by
        intro t ht
        have : (per + t) + per < per * m + per + per := by omega
        have := h (per + t) (by omega)
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      rw [ih (fun t => g (per + t)) h']
      have hper : cat (fun t => g (per + t)) per = cat g per := by
        refine cat_congr ?_
        intro u hu
        have := h u (by omega)
        simpa [Nat.add_comm] using this
      rw [hper, List.replicate_succ]
      simp


/-! ## A bimachine over a one-letter input alphabet -/

section Bimach

variable {B P S : Type} (M : Bimachine Unit B P S)

/-- The state of the prefix automaton after reading `i` letters. -/
def pfx (i : ℕ) : P := (fun p => M.prefixStep p ())^[i] M.prefixInit

/-- The state of the suffix automaton after reading `j` letters. -/
def sfx (j : ℕ) : S := (fun s => M.suffixStep s ())^[j] M.suffixInit

/-- The piece of output produced in a gap that has `i` letters on its left and `j` letters on its
right. -/
def piece (i j : ℕ) : List B := M.out (pfx M i) (sfx M j)

lemma strTrans_replicate {A Q : Type} (step : Q → A → Q) (a : A) (i : ℕ) (q : Q) :
    strTrans step (List.replicate i a) q = (fun q => step q a)^[i] q := by
  induction i generalizing q with
  | zero => rfl
  | succ i ih =>
      rw [List.replicate_succ, Function.iterate_succ_apply]
      show List.foldl step (step q a) (List.replicate i a) = _
      exact ih (step q a)

/-- The output of a bimachine on the unary input of length `N` is the concatenation of the pieces
of its `N + 1` gaps. -/
lemma eval_replicate (N : ℕ) :
    M.eval (List.replicate N ()) = cat (fun i => piece M i (N - i)) (N + 1) := by
  unfold Bimachine.eval cat
  rw [List.length_replicate]
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  have hiN : i ≤ N := by
    have := List.mem_range.1 hi
    omega
  have htake : (List.replicate N ()).take i = List.replicate i () := by
    simp [List.take_replicate, Nat.min_eq_left hiN]
  have hdrop : ((List.replicate N ()).drop i).reverse = List.replicate (N - i) () := by
    simp [List.drop_replicate]
  rw [htake, hdrop]
  simp [piece, pfx, sfx, strTrans_replicate]

end Bimach


/-! ## The output of a unary bimachine on the inputs of a fixed residue class -/

section Parts

variable {B P S : Type} (M : Bimachine Unit B P S) (lam per : ℕ)

/-- The pieces of the first `lam` gaps. -/
def leftPart (a : ℕ) : List B := cat (fun i => piece M i (a - i)) lam

/-- The pieces of one period of gaps in the middle. -/
def loopPart (a : ℕ) : List B := cat (fun u => piece M (lam + u) (a - lam - u)) per

/-- The pieces of the remaining gaps in the middle. -/
def midPart (a : ℕ) : List B := cat (fun v => piece M (lam + v) (a - lam - v)) (a - 2 * lam + 1)

/-- The pieces of the last `lam` gaps. -/
def rightPart (a : ℕ) : List B := cat (fun u => piece M (a - lam + 1 + u) (lam - 1 - u)) lam

end Parts

section Core

variable {B P S : Type} {M : Bimachine Unit B P S} {lam per : ℕ}

/-- **The key computation.**  Over a one-letter input alphabet, if the runs of the prefix and of
the suffix automaton are periodic with period `per` from position `lam` on, then on the inputs of
length `a + per * m`, for a fixed `a ≥ 2 * lam + per`, the bimachine outputs a string of the form
`x yᵐ z`: increasing `m` by one inserts one more period of gaps in the middle, and that period
produces the same pieces as the other ones. -/
theorem eval_replicate_period
    (hp : ∀ n, lam ≤ n → ∀ t, pfx M (n + per * t) = pfx M n)
    (hs : ∀ n, lam ≤ n → ∀ t, sfx M (n + per * t) = sfx M n)
    {a : ℕ} (ha : 2 * lam + per ≤ a) (m : ℕ) :
    M.eval (List.replicate (a + per * m) ()) =
      leftPart M lam a ++ ((List.replicate m (loopPart M lam per a)).flatten ++
        (midPart M lam a ++ rightPart M lam a)) := by
  set N := a + per * m with hN
  rw [eval_replicate]
  have hsplit : N + 1 = lam + (per * m + ((a - 2 * lam + 1) + lam)) := by omega
  rw [hsplit, cat_add, cat_add, cat_add]
  -- the block of one period, which is what gets repeated
  have hloop : cat (fun t => piece M (lam + t) (N - (lam + t))) per = loopPart M lam per a := by
    refine cat_congr ?_
    intro u hu
    have e2 : sfx M (N - (lam + u)) = sfx M (a - lam - u) := by
      have h := hs (a - lam - u) (by omega) m
      rw [show (a - lam - u) + per * m = N - (lam + u) by omega] at h
      exact h
    show piece M (lam + u) (N - (lam + u)) = piece M (lam + u) (a - lam - u)
    rw [piece, piece, e2]
  congr 1
  · -- the first `lam` gaps
    refine cat_congr ?_
    intro i hi
    have e2 : sfx M (N - i) = sfx M (a - i) := by
      have h := hs (a - i) (by omega) m
      rw [show (a - i) + per * m = N - i by omega] at h
      exact h
    show piece M i (N - i) = piece M i (a - i)
    rw [piece, piece, e2]
  congr 1
  · -- the periodic block in the middle
    have hT : ∀ t, t + per < per * m + per →
        piece M (lam + (t + per)) (N - (lam + (t + per))) = piece M (lam + t) (N - (lam + t)) := by
      intro t ht
      have htm : t < per * m := by omega
      have e1 : pfx M (lam + (t + per)) = pfx M (lam + t) := by
        have h := hp (lam + t) (by omega) 1
        rw [show (lam + t) + per * 1 = lam + (t + per) by ring] at h
        exact h
      have e2 : sfx M (N - (lam + (t + per))) = sfx M (N - (lam + t)) := by
        have h := hs (N - (lam + (t + per))) (by omega) 1
        rw [show (N - (lam + (t + per))) + per * 1 = N - (lam + t) by omega] at h
        exact h.symm
      rw [piece, piece, e1, e2]
    rw [cat_period (fun t => piece M (lam + t) (N - (lam + t))) per m hT, hloop]
  congr 1
  · -- the remaining gaps in the middle
    refine cat_congr ?_
    intro v hv
    have e1 : pfx M (lam + (per * m + v)) = pfx M (lam + v) := by
      have h := hp (lam + v) (by omega) m
      rw [show (lam + v) + per * m = lam + (per * m + v) by ring] at h
      exact h
    have e2 : sfx M (N - (lam + (per * m + v))) = sfx M (a - lam - v) := by
      rw [show N - (lam + (per * m + v)) = a - lam - v by omega]
    show piece M (lam + (per * m + v)) (N - (lam + (per * m + v))) = piece M (lam + v) (a - lam - v)
    rw [piece, piece, e1, e2]
  · -- the last `lam` gaps
    refine cat_congr ?_
    intro u hu
    have e1 : pfx M (lam + (per * m + ((a - 2 * lam + 1) + u))) = pfx M (a - lam + 1 + u) := by
      have h := hp (a - lam + 1 + u) (by omega) m
      rw [show (a - lam + 1 + u) + per * m = lam + (per * m + ((a - 2 * lam + 1) + u)) by
        omega] at h
      exact h
    have e2 : sfx M (N - (lam + (per * m + ((a - 2 * lam + 1) + u)))) = sfx M (lam - 1 - u) := by
      rw [show N - (lam + (per * m + ((a - 2 * lam + 1) + u))) = lam - 1 - u by omega]
    show piece M (lam + (per * m + ((a - 2 * lam + 1) + u)))
        (N - (lam + (per * m + ((a - 2 * lam + 1) + u)))) = piece M (a - lam + 1 + u) (lam - 1 - u)
    rw [piece, piece, e1, e2]

end Core


/-! ## The graph of a rational function over a one-letter input alphabet -/

section Graph

variable {B : Type}

/-- Every string over a one-letter alphabet is a power of its unique letter. -/
lemma eq_replicate_unit (w : List Unit) : w = List.replicate w.length () := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a; rw [List.length_cons, List.replicate_succ, ← ih]

/-- A bimachine over a one-letter input alphabet has periodic runs: there are a threshold `lam`
and a period `per` such that both the prefix and the suffix automaton are in the same state after
`n` and after `n + per` letters, for every `n ≥ lam`. -/
lemma exists_periodicity {P S : Type} [Finite P] [Finite S] (M : Bimachine Unit B P S) :
    ∃ lam per : ℕ, 0 < per ∧
      (∀ n, lam ≤ n → ∀ t, pfx M (n + per * t) = pfx M n) ∧
      (∀ n, lam ≤ n → ∀ t, sfx M (n + per * t) = sfx M n) := by
  obtain ⟨l₁, k₁, hk₁, h₁⟩ := exists_eventual_period (fun p => M.prefixStep p ()) M.prefixInit
  obtain ⟨l₂, k₂, hk₂, h₂⟩ := exists_eventual_period (fun s => M.suffixStep s ()) M.suffixInit
  refine ⟨max l₁ l₂, k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_, ?_⟩
  · intro n hn t
    have h := iterate_period_mul (fun p => M.prefixStep p ()) M.prefixInit h₁ (k₂ * t) n
      (le_trans (le_max_left _ _) hn)
    show (fun p => M.prefixStep p ())^[n + k₁ * k₂ * t] M.prefixInit = _
    rw [show n + k₁ * k₂ * t = n + k₁ * (k₂ * t) by ring]
    exact h
  · intro n hn t
    have h := iterate_period_mul (fun s => M.suffixStep s ()) M.suffixInit h₂ (k₁ * t) n
      (le_trans (le_max_right _ _) hn)
    show (fun s => M.suffixStep s ())^[n + k₁ * k₂ * t] M.suffixInit = _
    rw [show n + k₁ * k₂ * t = n + k₂ * (k₁ * t) by ring]
    exact h

/-- The data of the finite union: for a bimachine with threshold `lam` and period `per`, the
`2 * lam + 2 * per` triples `(x, y, z)` and the coefficients of the exercise. -/
def coefB (lam per : ℕ) (i : ℕ) : ℕ := if i < 2 * lam + per then 0 else per

def wordX {P S : Type} (M : Bimachine Unit B P S) (lam per : ℕ) (i : ℕ) : List B :=
  if i < 2 * lam + per then M.eval (List.replicate i ()) else leftPart M lam i

def wordY {P S : Type} (M : Bimachine Unit B P S) (lam per : ℕ) (i : ℕ) : List B :=
  if i < 2 * lam + per then [] else loopPart M lam per i

def wordZ {P S : Type} (M : Bimachine Unit B P S) (lam per : ℕ) (i : ℕ) : List B :=
  if i < 2 * lam + per then [] else midPart M lam i ++ rightPart M lam i

lemma eval_eq_wordX {P S : Type} {M : Bimachine Unit B P S} {lam per : ℕ}
    (hp : ∀ n, lam ≤ n → ∀ t, pfx M (n + per * t) = pfx M n)
    (hs : ∀ n, lam ≤ n → ∀ t, sfx M (n + per * t) = sfx M n) (i k : ℕ) :
    M.eval (List.replicate (i + coefB lam per i * k) ()) =
      wordX M lam per i ++ (List.replicate k (wordY M lam per i)).flatten ++ wordZ M lam per i := by
  unfold coefB wordX wordY wordZ
  by_cases hi : i < 2 * lam + per
  · simp [hi]
  · simp only [hi, if_false]
    rw [eval_replicate_period hp hs (by omega) k, List.append_assoc]

lemma exists_index (lam per : ℕ) (hper : 0 < per) (N : ℕ) :
    ∃ i < 2 * lam + per + per, ∃ k : ℕ, i + coefB lam per i * k = N := by
  by_cases hN : N < 2 * lam + per
  · exact ⟨N, by omega, 0, by simp [coefB, hN]⟩
  · refine ⟨2 * lam + per + (N - (2 * lam + per)) % per, ?_, (N - (2 * lam + per)) / per, ?_⟩
    · have := Nat.mod_lt (N - (2 * lam + per)) hper
      omega
    · have hnot : ¬ (2 * lam + per + (N - (2 * lam + per)) % per < 2 * lam + per) := by omega
      simp only [coefB, hnot, if_false]
      have := Nat.div_add_mod (N - (2 * lam + per)) per
      have hmul : per * ((N - (2 * lam + per)) / per) = (N - (2 * lam + per)) / per * per :=
        Nat.mul_comm _ _
      omega

end Graph

end Unary
end Exercises
end Transducers
