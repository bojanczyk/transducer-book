/-
Exercise `exer:non-weak-simon-tree-not-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): even for an aperiodic monoid, Simon trees cannot be computed by
a first-order rational function.

The monoid is the book's `{0, 1, 2}` with addition capped at `2` (`Transducers.Exercises.Cap2`),
with the homomorphism `Transducers.Exercises.capHom : {a}* → {0, 1, 2}` that maps a string to its
length capped at `2`.  A first-order rational function is a first-order relabelling
(`Transducers.IsFORelabelling`); by Theorem `thm:fo-rational-functions` it is computed by an
aperiodic bimachine (`Transducers.isAperiodicBimachine_of_isFORelabelling`), and that is the form
used in the proof.  As in Lemma `lem:factorisation-forest-rational`, a rational function is
string-to-string in this project, so the book's polynomial type `facttype{h,k}` is replaced by the
bracket encoding `Transducers.FactTree.enc` of trees.

The proof.  On the input `aᴺ`, the states of the prefix automaton of an aperiodic bimachine are
eventually constant, and so are those of the suffix automaton; so for `N = 2K + n` the output is
`α βⁿ⁺¹ γ` for fixed words `α, β, γ`.  Counting letters and brackets as `n` grows shows that `β`
contains exactly one letter and is balanced.  For `n = 2` the output contains a factor `a R a R a`
with `R` a balanced word of brackets, which is impossible in the encoding of a Simon tree
(`Transducers.Exercises.no_simon_enc_window`, `EvalNonWeak.lean`).
-/
import RequestProject.Exercises.EvalNonWeak
import RequestProject.PartC.FORelabBimach

namespace Transducers.Exercises

open FactTree TreeSym

/-! ## Bimachines on a one-letter input alphabet -/

lemma strTrans_replicate {Q : Type} (δ : Q → Unit → Q) (n : ℕ) (q : Q) :
    strTrans δ (List.replicate n ()) q = (strTrans δ [()])^[n] q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (δ q ())

lemma bimachine_eval_replicate {B P S : Type} (M : Bimachine Unit B P S) (N : ℕ) :
    M.eval (List.replicate N ()) = ((List.range (N + 1)).map fun i =>
      M.out ((strTrans M.prefixStep [()])^[i] M.prefixInit)
        ((strTrans M.suffixStep [()])^[N - i] M.suffixInit)).flatten := by
  rw [Bimachine.eval, List.length_replicate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i ≤ N := by simp at hi; omega
  rw [List.take_replicate, List.drop_replicate, List.reverse_replicate, strTrans_replicate,
    strTrans_replicate, min_eq_left hi']

/-- On the inputs `a^{2K+n}`, an aperiodic bimachine (whose automata stabilise after `K` steps)
outputs `α βⁿ⁺¹ γ` for fixed words `α, β, γ`. -/
lemma bimachine_eval_pumped {B P S : Type} (M : Bimachine Unit B P S) (K : ℕ)
    (hp : ∀ n ≥ K, (strTrans M.prefixStep [()])^[n] M.prefixInit =
      (strTrans M.prefixStep [()])^[K] M.prefixInit)
    (hs : ∀ n ≥ K, (strTrans M.suffixStep [()])^[n] M.suffixInit =
      (strTrans M.suffixStep [()])^[K] M.suffixInit) :
    ∃ α β γ : List B, ∀ n : ℕ,
      M.eval (List.replicate (2 * K + n) ()) = α ++ (List.replicate (n + 1) β).flatten ++ γ := by
  set pf : ℕ → P := fun i => (strTrans M.prefixStep [()])^[i] M.prefixInit with hpf
  set sf : ℕ → S := fun j => (strTrans M.suffixStep [()])^[j] M.suffixInit with hsf
  refine ⟨((List.range K).map fun i => M.out (pf i) (sf K)).flatten, M.out (pf K) (sf K),
    ((List.range K).map fun i => M.out (pf K) (sf (K - 1 - i))).flatten, fun n => ?_⟩
  rw [bimachine_eval_replicate, show 2 * K + n + 1 = K + ((n + 1) + K) by ring, List.range_add,
    List.range_add, List.map_append, List.map_append, List.map_append, List.map_map,
    List.map_map, List.map_map, List.flatten_append, List.flatten_append, List.append_assoc]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [hpf, hsf]
    rw [hs _ (by omega)]
  congr 1
  · rw [show List.replicate (n + 1) (M.out (pf K) (sf K)) =
      (List.range (n + 1)).map (fun _ => M.out (pf K) (sf K)) by simp]
    congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp_apply, hpf, hsf]
    rw [hp _ (by omega), hs _ (by omega)]
  · congr 1
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    simp only [Function.comp_apply, hpf, hsf]
    rw [hp _ (by omega), show 2 * K + n - (K + (n + 1 + i)) = K - 1 - i by omega]

/-! ## The exercise -/

lemma exists_split_one_letter :
    ∀ u : List (TreeSym Unit), lets u = 1 →
      ∃ u₁ u₂, u = u₁ ++ TreeSym.letter () :: u₂ ∧ lets u₁ = 0 ∧ lets u₂ = 0
  | [], h => by simp at h
  | x :: u, h => by
    cases x with
    | letter a =>
      simp only [lets_cons, symLet] at h
      exact ⟨[], u, by simp, rfl, by omega⟩
    | op =>
      simp only [lets_cons, symLet, zero_add] at h
      obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := exists_split_one_letter u h
      exact ⟨TreeSym.op :: u₁, u₂, rfl, by simp [symLet, h₁], h₂⟩
    | cl =>
      simp only [lets_cons, symLet, zero_add] at h
      obtain ⟨u₁, u₂, rfl, h₁, h₂⟩ := exists_split_one_letter u h
      exact ⟨TreeSym.cl :: u₁, u₂, rfl, by simp [symLet, h₁], h₂⟩

lemma lets_flatten_replicate {A : Type} (k : ℕ) (β : List (TreeSym A)) :
    lets (List.replicate k β).flatten = k * lets β := by
  rw [lets_flatten, List.map_replicate, List.sum_replicate, smul_eq_mul]

lemma bal_flatten_replicate {A : Type} (k : ℕ) (β : List (TreeSym A)) :
    bal (List.replicate k β).flatten = k * bal β := by
  rw [bal_flatten, List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- The heart of the exercise: no function computed by an aperiodic bimachine maps every string
`w ∈ {a}*` to the encoding of a Simon tree for `capHom` with underlying string `w` -- whatever the
height of the trees. -/
theorem not_isAperiodicBimachine_simon (f : List Unit → List (TreeSym Unit))
    (hf : IsAperiodicBimachine f) :
    ¬ ∀ w : List Unit, ∃ t : FactTree Unit, f w = t.enc ∧ t.yield = w ∧ t.IsSimon capHom := by
  obtain ⟨P, S, _, _, M, rfl, hP, hS⟩ := hf
  intro hall
  obtain ⟨KP, hKP⟩ := hP [()]
  obtain ⟨KS, hKS⟩ := hS [()]
  set K := max KP KS
  have hp : ∀ n ≥ K, (strTrans M.prefixStep [()])^[n] M.prefixInit =
      (strTrans M.prefixStep [()])^[K] M.prefixInit := fun n hn => by
    rw [hKP n (le_trans (le_max_left _ _) hn), hKP K (le_max_left _ _)]
  have hs : ∀ n ≥ K, (strTrans M.suffixStep [()])^[n] M.suffixInit =
      (strTrans M.suffixStep [()])^[K] M.suffixInit := fun n hn => by
    rw [hKS n (le_trans (le_max_right _ _) hn), hKS K (le_max_right _ _)]
  obtain ⟨α, β, γ, hαβγ⟩ := bimachine_eval_pumped M K hp hs
  -- the counts of letters and brackets of the outputs
  have hcount : ∀ n : ℕ, lets α + (n + 1) * lets β + lets γ = 2 * K + n ∧
      bal α + (n + 1) * bal β + bal γ = 0 := by
    intro n
    obtain ⟨t, ht, hy, -⟩ := hall (List.replicate (2 * K + n) ())
    rw [hαβγ n] at ht
    have h1 := enc_lets t
    have h2 := enc_bal t
    rw [← ht, hy, List.length_replicate, lets_append, lets_append, lets_flatten_replicate] at h1
    rw [← ht, bal_append, bal_append, bal_flatten_replicate] at h2
    push_cast at h2
    exact ⟨h1, h2⟩
  have hβl : lets β = 1 := by
    have h0 := (hcount 0).1
    have h1 := (hcount 1).1
    simp only [zero_add, one_mul] at h0
    omega
  have hβb : bal β = 0 := by
    have h0 := (hcount 0).2
    have h1 := (hcount 1).2
    push_cast at h0 h1
    linarith
  obtain ⟨β₁, β₂, rfl, h₁, h₂⟩ := exists_split_one_letter β hβl
  -- the output on `a^{2K+2}` contains the factor `a R a R a` with `R = β₂ β₁`
  obtain ⟨t, ht, -, hsim⟩ := hall (List.replicate (2 * K + 2) ())
  rw [hαβγ 2] at ht
  refine no_simon_enc_window (α ++ β₁) (β₂ ++ β₁) (β₂ ++ γ) (by simp [h₁, h₂]) ?_ t hsim ?_
  · simp only [bal_append, bal_cons, symBal] at hβb ⊢
    linarith
  · rw [← ht]
    simp [List.replicate_succ]

/-- **Exercise `exer:non-weak-simon-tree-not-aperiodic`.**  Even under the assumption that the
monoid is aperiodic, a (non-weak) Simon tree cannot be computed by a first-order definable rational
function.  The monoid is `{0, 1, 2}` with addition capped at `2`, which is aperiodic (`x³ = x²` for
every element), with the homomorphism `capHom : {a}* → {0, 1, 2}` mapping a string to its length
capped at `2`; and no first-order relabelling `f` (Theorem `thm:fo-rational-functions`: no function
computed by an aperiodic bimachine) maps every string `w` to the bracket encoding of a Simon tree
for `capHom` whose underlying string is `w`.

The book's codomain `facttype{h,k}` bounds the height of the trees by a constant `k`; the statement
here has no such bound, so it is stronger: it rules out Simon trees of any height. -/
theorem non_weak_simon_tree_not_aperiodic :
    (∀ x : Cap2, x ^ 3 = x ^ 2) ∧
    ¬ ∃ f : List Unit → List (TreeSym Unit), IsFORelabelling f ∧
      ∀ w : List Unit, ∃ t : FactTree Unit, f w = t.enc ∧ t.yield = w ∧ t.IsSimon capHom :=
  ⟨Cap2.aperiodic, fun ⟨f, hf, hall⟩ =>
    not_isAperiodicBimachine_simon f (isAperiodicBimachine_of_isFORelabelling hf) hall⟩

end Transducers.Exercises
