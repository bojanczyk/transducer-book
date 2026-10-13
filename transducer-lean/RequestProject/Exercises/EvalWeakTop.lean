/-
Exercise `exer:weak-simon-tree-aperiodic` of Part D, Section *Evaluation*
(`partDPolyregular/evaluation.tex`): if the monoid is aperiodic, then weak Simon trees can be
computed by an aperiodic rational function.

By the induction of `EvalWeakInd.lean` (`Transducers.Exercises.wgood_univ`), there are a bound `K`,
a finite aperiodic monoid `N`, a map `θ : M → N` and a rank function `G : N → N → ℕ` such that
every nonempty string `x₀ x₁ ⋯ xₙ` has a weak Simon tree with all leaves at depth `K + 1`, whose
bracket encoding is

  `[ᴷ⁺¹ x₀ ]^{r₁} [^{r₁} x₁ ⋯ ]^{rₙ} [^{rₙ} xₙ ]ᴷ⁺¹`,

where `rᵢ = G (θ-value of x₀ ⋯ xᵢ₋₁) (θ-value of xᵢ ⋯ xₙ)`.  This output is produced by a
bimachine whose prefix automaton computes the `θ`-value of the prefix (in `N`) and whose suffix
automaton computes the `θ`-value of the suffix together with its first letter; both automata are
aperiodic because `N` is.  By Theorem `thm:fo-rational-functions`
(`Transducers.isFORelabelling_of_isAperiodicBimachine`) the function is a first-order relabelling.
-/
import RequestProject.Exercises.EvalWeakInd
import RequestProject.PartC.FOBimachRelab

namespace Transducers.Exercises

open FactTree TreeSym Simon

section Machine

variable {A N : Type} [Monoid N] (ψ : A → N) (G : N → N → ℕ) (K : ℕ)

/-- The bimachine: the prefix automaton computes the value of the prefix and whether it is
nonempty, the suffix automaton the value of the suffix and its first letter. -/
def weakMachine : Bimachine A (TreeSym A) (N × Bool) (N × Option A) where
  prefixInit := (1, false)
  prefixStep := fun p a => (p.1 * ψ a, true)
  suffixInit := (1, none)
  suffixStep := fun q a => (ψ a * q.1, some a)
  out := fun p q => match p.2, q.2 with
    | false, none => [op, cl]
    | false, some a => List.replicate (K + 1) op ++ [letter a]
    | true, some a => List.replicate (G p.1 q.1) cl ++ List.replicate (G p.1 q.1) op ++ [letter a]
    | true, none => List.replicate (K + 1) cl

lemma weakMachine_suffix : ∀ l : List A,
    strTrans (weakMachine ψ G K).suffixStep l.reverse (weakMachine ψ G K).suffixInit =
      (val ψ l, l.head?)
  | [] => rfl
  | x :: l => by
    have ih := weakMachine_suffix l
    simp only [strTrans] at ih ⊢
    rw [List.reverse_cons, List.foldl_append, ih]
    simp [weakMachine]

lemma weakMachine_evalFrom : ∀ (xs : List A) (α : N) (x0 : A),
    (weakMachine ψ G K).evalFrom (α * ψ x0, true) xs =
      body (rk ψ G α x0 xs 1) ++ List.replicate (K + 1) cl
  | [], α, x0 => by
    rw [Bimachine.evalFrom_nil]
    simp [weakMachine]
  | x1 :: xs, α, x0 => by
    rw [Bimachine.evalFrom_cons, weakMachine_suffix, rk_cons, body_cons]
    have ih := weakMachine_evalFrom xs (α * ψ x0) x1
    have hstep : (weakMachine ψ G K).prefixStep (α * ψ x0, true) x1 = (α * ψ x0 * ψ x1, true) :=
      rfl
    rw [hstep, ih]
    simp [weakMachine]

lemma weakMachine_eval (x0 : A) (xs : List A) :
    (weakMachine ψ G K).eval (x0 :: xs) = encR K x0 (rk ψ G 1 x0 xs 1) := by
  rw [Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_cons, weakMachine_suffix]
  have hstep : (weakMachine ψ G K).prefixStep (weakMachine ψ G K).prefixInit x0 =
      ((1 : N) * ψ x0, true) := rfl
  rw [hstep, weakMachine_evalFrom]
  simp [weakMachine, encR]

lemma weakMachine_eval_nil : (weakMachine ψ G K).eval [] = [op, cl] := by
  rw [Bimachine.eval_eq_evalFrom, Bimachine.evalFrom_nil]
  rfl

lemma weakMachine_prefix_iter (w : List A) (hw : w ≠ []) :
    ∀ (n : ℕ) (p : N × Bool), 1 ≤ n →
      (strTrans (weakMachine ψ G K).prefixStep w)^[n] p = (p.1 * val ψ w ^ n, true) := by
  have h1 : ∀ p : N × Bool, strTrans (weakMachine ψ G K).prefixStep w p = (p.1 * val ψ w, true) := by
    intro p
    obtain ⟨w', x, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
    induction w' generalizing p with
    | nil => simp [strTrans, weakMachine]
    | cons y w' ih =>
      have := ih (p.1 * ψ y, true) (by simp)
      simp only [strTrans, List.concat_eq_append, List.cons_append, List.foldl_cons] at this ⊢
      rw [show (weakMachine ψ G K).prefixStep p y = (p.1 * ψ y, true) from rfl, this]
      simp [mul_assoc]
  intro n p hn
  induction n, hn using Nat.le_induction with
  | base => simp [h1]
  | succ n _ ih =>
    rw [Function.iterate_succ_apply', ih, h1, pow_succ, mul_assoc]

lemma weakMachine_suffix_iter (w : List A) (hw : w ≠ []) :
    ∀ (n : ℕ) (q : N × Option A), 1 ≤ n →
      (strTrans (weakMachine ψ G K).suffixStep w)^[n] q =
        (val ψ w.reverse ^ n * q.1, w.getLast? ) := by
  have h1 : ∀ q : N × Option A,
      strTrans (weakMachine ψ G K).suffixStep w q = (val ψ w.reverse * q.1, w.getLast?) := by
    intro q
    obtain ⟨w', x, rfl⟩ := (List.eq_nil_or_concat w).resolve_left hw
    induction w' generalizing q with
    | nil => simp [strTrans, weakMachine]
    | cons y w' ih =>
      have := ih (ψ y * q.1, some y) (by simp)
      simp only [strTrans, List.concat_eq_append, List.cons_append, List.foldl_cons] at this ⊢
      rw [show (weakMachine ψ G K).suffixStep q y = (ψ y * q.1, some y) from rfl, this]
      refine Prod.ext ?_ ?_
      · simp [mul_assoc]
      · show (w' ++ [x]).getLast? = (y :: (w' ++ [x])).getLast?
        rw [← List.cons_append, List.getLast?_append, List.getLast?_append]; simp
  intro n q hn
  induction n, hn using Nat.le_induction with
  | base => simp [h1]
  | succ n _ ih =>
    rw [Function.iterate_succ_apply', ih, h1, pow_succ', mul_assoc]

lemma weakMachine_aperiodic (hN : Aper N) :
    TransAperiodic (weakMachine ψ G K).prefixStep ∧
      TransAperiodic (weakMachine ψ G K).suffixStep := by
  constructor
  · intro w
    rcases eq_or_ne w [] with rfl | hw
    · exact ⟨0, fun n _ => by
        have : strTrans (weakMachine ψ G K).prefixStep ([] : List A) = id := rfl
        rw [this, Function.iterate_id, Function.iterate_id]⟩
    · obtain ⟨m, hm⟩ := hN (val ψ w)
      refine ⟨m + 1, fun n hn => funext fun p => ?_⟩
      rw [weakMachine_prefix_iter ψ G K w hw n p (by omega),
        weakMachine_prefix_iter ψ G K w hw (m + 1) p (by omega),
        pow_stable hm n (by omega), pow_stable hm (m + 1) (by omega)]
  · intro w
    rcases eq_or_ne w [] with rfl | hw
    · exact ⟨0, fun n _ => by
        have : strTrans (weakMachine ψ G K).suffixStep ([] : List A) = id := rfl
        rw [this, Function.iterate_id, Function.iterate_id]⟩
    · obtain ⟨m, hm⟩ := hN (val ψ w.reverse)
      refine ⟨m + 1, fun n hn => funext fun q => ?_⟩
      rw [weakMachine_suffix_iter ψ G K w hw n q (by omega),
        weakMachine_suffix_iter ψ G K w hw (m + 1) q (by omega),
        pow_stable hm n (by omega), pow_stable hm (m + 1) (by omega)]

end Machine

/-- **Exercise `exer:weak-simon-tree-aperiodic`**, in terms of aperiodic bimachines.  If the finite
monoid `M` is aperiodic, then there are a bound `k` and a function computed by an aperiodic
bimachine which maps every input string `w` to the bracket encoding of a weak Simon tree for `h`
with yield `w` and height at most `k`. -/
theorem weak_simon_tree_aperiodicBimachine {A M : Type} [Finite A] [Monoid M] [Finite M]
    (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (h : FreeMonoid A →* M) :
    ∃ (k : ℕ) (f : List A → List (TreeSym A)), IsAperiodicBimachine f ∧
      ∀ w : List A, ∃ t : FactTree A,
        f w = t.enc ∧ t.yield = w ∧ t.IsWeakSimon h ∧ t.height ≤ k := by
  classical
  haveI := Fintype.ofFinite M
  obtain ⟨K, N, _, _, hN, θ, G, hK⟩ := wgood_univ hM
  set φ : A → M := fun a => h (FreeMonoid.of a) with hφ
  refine ⟨K + 1, (weakMachine (θ ∘ φ) G K).eval,
    ⟨N × Bool, N × Option A, inferInstance, inferInstance, weakMachine (θ ∘ φ) G K, rfl,
      weakMachine_aperiodic (θ ∘ φ) G K hN⟩, fun w => ?_⟩
  rcases eq_or_ne w [] with rfl | hw
  · refine ⟨.node [], by rw [weakMachine_eval_nil]; simp [FactTree.enc], by simp,
      .node [] (by simp) (by simp), ?_⟩
    simp [height]
  · obtain ⟨t, hy, hws, hh, x0, xs, rfl, he⟩ :=
      hK A φ w hw fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
    exact ⟨t, by rw [weakMachine_eval, he], hy, hws.isWeakSimon, hh⟩

/-- **Exercise `exer:weak-simon-tree-aperiodic`.**  If the finite monoid `M` is aperiodic, then
weak Simon trees (`Transducers.FactTree.IsWeakSimon`) can be computed by an aperiodic rational
function: there are a bound `k` and a first-order relabelling (equivalently, by Theorem
`thm:fo-rational-functions`, a first-order rational function) mapping every input string `w` to the
bracket encoding (`Transducers.FactTree.enc`) of a weak Simon tree for `h` with yield `w` and height
at most `k`. -/
theorem weak_simon_tree_aperiodic {A M : Type} [Finite A] [Monoid M] [Finite M]
    (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (h : FreeMonoid A →* M) :
    ∃ (k : ℕ) (f : List A → List (TreeSym A)), IsFORelabelling f ∧
      ∀ w : List A, ∃ t : FactTree A,
        f w = t.enc ∧ t.yield = w ∧ t.IsWeakSimon h ∧ t.height ≤ k := by
  obtain ⟨k, f, hf, hall⟩ := weak_simon_tree_aperiodicBimachine hM h
  exact ⟨k, f, isFORelabelling_of_isAperiodicBimachine hf, hall⟩

end Transducers.Exercises
