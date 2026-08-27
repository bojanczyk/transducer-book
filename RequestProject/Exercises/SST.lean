/-
The exercises of the chapter *Streaming string transducers* (`sst.tex`) of *Transducers*
(M. Bojańczyk).

Exercises are not numbered results of the book, so they are recorded in `EXERCISES.md` and not in
`THEOREMS.md`, and each of them is referred to by its LaTeX label.  The copyful ssts and the
polynomial automata that several of these exercises introduce are defined in
`RequestProject/Exercises/SSTAux.lean`, next to the auxiliary facts about them that the solutions
take for granted.

Each statement follows the exercise, and each proof follows the author's own solution, unless the
docstring says otherwise.
-/
import RequestProject.Exercises.SSTAux

namespace Transducers.Exercises

open Transducers

/-! ## Streaming string transducers (`sst.tex`) -/

/-! ### Exercise `exer:sst-sorting` -/

/-- The sst of the author's solution to Exercise `exer:sst-sorting`: one state and two registers,
`X` collecting the letters `a` (here `false`) and `Y` the letters `b` (here `true`), with the
output function `XY`.  Both updates are copyless, since each register name is used once. -/
def sortSST : SST Bool Bool Unit Bool where
  init := ()
  step := fun _ a => ((), fun x => if x = a then [Sum.inl x, Sum.inr a] else [Sum.inl x])
  step_copyless := by
    intro q a
    refine copyless_of_self _ fun v => ?_
    by_cases hv : v = a
    · exact ⟨[], [a], by simp [hv]⟩
    · exact ⟨[], [], by simp [hv]⟩
  final := fun _ => [Sum.inl false, Sum.inl true]

lemma sortSST_registers (w : List Bool) (η : Bool → List Bool) :
    ((w.foldl sortSST.stepConfig ((), η)).2)
      = fun x => η x ++ List.replicate (w.count x) x := by
  induction w generalizing η with
  | nil => funext x; simp
  | cons a w ih =>
      have hstep : (sortSST.stepConfig ((), η) a).2
          = fun x => if x = a then η x ++ [a] else η x := by
        funext x
        by_cases hx : x = a <;>
          simp [hx, SST.stepConfig, sortSST, SST.subst]
      rw [show ((a :: w).foldl sortSST.stepConfig ((), η))
            = w.foldl sortSST.stepConfig ((), (sortSST.stepConfig ((), η) a).2) from rfl,
        ih]
      funext x
      rw [hstep]
      by_cases hx : x = a
      · subst hx
        simp [List.replicate_succ]
      · have : a ≠ x := fun h => hx h.symm
        simp [hx, this]

/-- **Exercise `exer:sst-sorting`.**  The sst `Transducers.Exercises.sortSST` sorts its input: it
outputs all the letters `a` (here `false`) first, followed by all the letters `b` (here `true`). -/
theorem sortSST_eval (w : List Bool) :
    sortSST.eval w
      = List.replicate (w.count false) false ++ List.replicate (w.count true) true := by
  have h := sortSST_registers w (fun _ => [])
  show SST.subst (sortSST.runConfig w).2 (sortSST.final (sortSST.runConfig w).1) = _
  rw [show (sortSST.runConfig w).2 = (w.foldl sortSST.stepConfig ((), fun _ => [])).2 from rfl, h]
  simp [sortSST, SST.subst]

/-- **Exercise `exer:sst-sorting`.**  Sorting a string over a two-letter alphabet is computed by an
sst. -/
theorem isSST_sort :
    IsSST (fun w : List Bool =>
      List.replicate (w.count false) false ++ List.replicate (w.count true) true) :=
  ⟨Unit, Bool, inferInstance, inferInstance, sortSST, funext sortSST_eval⟩

/-! ### Exercise `exer:sst-copyful-sst` -/

section Continuity

variable {A B Q X σ : Type} [Fintype X]

/-- The dfa of the author's solution to Exercise `exer:sst-copyful-sst`: instead of the string
stored in a register, it stores the transformation that the string induces on the states of a dfa
for the output language. -/
def CopyfulSST.dfaOf (T : CopyfulSST A B Q X) (D : DFA B σ) : DFA A (Q × (X → σ → σ)) where
  start := (T.init, fun _ => id)
  step := fun c a => ((T.step c.1 a).1, fun x => substTrans D c.2 ((T.step c.1 a).2 x))
  accept := {c | substTrans D c.2 (T.final c.1) D.start ∈ D.accept}

lemma CopyfulSST.dfaOf_evalFrom (T : CopyfulSST A B Q X) (D : DFA B σ)
    (w : List A) (q : Q) (η : X → List B) :
    (T.dfaOf D).evalFrom (q, fun x t => D.evalFrom t (η x)) w
      = ((w.foldl T.stepConfig (q, η)).1,
          fun x t => D.evalFrom t ((w.foldl T.stepConfig (q, η)).2 x)) := by
  induction w generalizing q η with
  | nil => rfl
  | cons a w ih =>
      rw [DFA.evalFrom_cons]
      have hstep : (T.dfaOf D).step (q, fun x t => D.evalFrom t (η x)) a
          = ((T.stepConfig (q, η) a).1,
              fun x t => D.evalFrom t ((T.stepConfig (q, η) a).2 x)) := by
        refine Prod.ext rfl ?_
        funext x t
        exact (evalFrom_subst D η ((T.step q a).2 x) t).symm
      rw [hstep]
      exact ih _ _

lemma CopyfulSST.dfaOf_accepts (T : CopyfulSST A B Q X) (D : DFA B σ) :
    (T.dfaOf D).accepts = {w : List A | T.eval w ∈ D.accepts} := by
  ext w
  rw [DFA.mem_accepts]
  show (T.dfaOf D).evalFrom (T.dfaOf D).start w ∈ (T.dfaOf D).accept ↔ _
  rw [show (T.dfaOf D).start = (T.init, fun (_ : X) (t : σ) => D.evalFrom t (([] : List B))) from
    rfl, T.dfaOf_evalFrom D w T.init (fun _ => [])]
  show substTrans D _ _ D.start ∈ D.accept ↔ _
  rw [← evalFrom_subst]
  simp only [DFA.mem_accepts, DFA.eval]
  rfl

/-- **Exercise `exer:sst-copyful-sst`.**  Copyful ssts are continuous: the inverse image of a
regular language is regular.  The proof is the author's: the inverse image is recognised by the
automaton which, instead of the string stored in a register, stores only the transformation that
the string induces on the states of a dfa for the output language. -/
theorem CopyfulSST.continuous [Finite Q] [Finite A] [Finite B] (T : CopyfulSST A B Q X) :
    Continuous T.eval := by
  classical
  intro L hL
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  haveI : Finite (Q × (X → σ → σ)) := inferInstance
  exact ⟨Q × (X → σ → σ), Fintype.ofFinite _, T.dfaOf D, T.dfaOf_accepts D⟩

/-- **Exercise `exer:sst-copyful-sst`.**  A function computed by a copyful sst is continuous. -/
theorem continuous_of_isCopyfulSST {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsCopyfulSST f) : Continuous f := by
  obtain ⟨Q, X, hQ, hX, T, rfl⟩ := hf
  exact T.continuous

end Continuity

/-! ### Exercise `exer:sst-copyful-sst-output-size` -/

section OutputSize

variable {A B Q X : Type} [Fintype X]

lemma regSize_stepConfig_le (T : CopyfulSST A B Q X) {N : ℕ}
    (hN : ∀ (q : Q) (a : A), ∑ x : X, ((T.step q a).2 x).length ≤ N)
    (q : Q) (η : X → List B) (a : A) :
    regSize (T.stepConfig (q, η) a).2 + 1 ≤ (N + 1) * (regSize η + 1) := by
  have h1 : regSize (T.stepConfig (q, η) a).2 ≤ N * (regSize η + 1) := by
    have hsum : ∑ x : X, (SST.subst η ((T.step q a).2 x)).length
        ≤ ∑ x : X, ((T.step q a).2 x).length * (regSize η + 1) :=
      Finset.sum_le_sum fun x _ => length_subst_le η ((T.step q a).2 x)
    calc regSize (T.stepConfig (q, η) a).2
        = ∑ x : X, (SST.subst η ((T.step q a).2 x)).length := rfl
      _ ≤ ∑ x : X, ((T.step q a).2 x).length * (regSize η + 1) := hsum
      _ = (∑ x : X, ((T.step q a).2 x).length) * (regSize η + 1) := by
          rw [Finset.sum_mul]
      _ ≤ N * (regSize η + 1) := Nat.mul_le_mul_right _ (hN q a)
  calc regSize (T.stepConfig (q, η) a).2 + 1
      ≤ N * (regSize η + 1) + 1 := Nat.add_le_add_right h1 1
    _ ≤ N * (regSize η + 1) + (regSize η + 1) := by
        exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _
    _ = (N + 1) * (regSize η + 1) := by ring

lemma regSize_foldl_le (T : CopyfulSST A B Q X) {N : ℕ}
    (hN : ∀ (q : Q) (a : A), ∑ x : X, ((T.step q a).2 x).length ≤ N)
    (w : List A) (q : Q) (η : X → List B) :
    regSize (w.foldl T.stepConfig (q, η)).2 + 1
      ≤ (N + 1) ^ w.length * (regSize η + 1) := by
  induction w generalizing q η with
  | nil => simp
  | cons a w ih =>
      rw [show ((a :: w).foldl T.stepConfig (q, η))
            = w.foldl T.stepConfig (T.stepConfig (q, η) a) from rfl]
      have h := ih (T.stepConfig (q, η) a).1 (T.stepConfig (q, η) a).2
      calc regSize (w.foldl T.stepConfig (T.stepConfig (q, η) a)).2 + 1
          ≤ (N + 1) ^ w.length * (regSize (T.stepConfig (q, η) a).2 + 1) := h
        _ ≤ (N + 1) ^ w.length * ((N + 1) * (regSize η + 1)) :=
            Nat.mul_le_mul_left _ (regSize_stepConfig_le T hN q η a)
        _ = (N + 1) ^ (w.length + 1) * (regSize η + 1) := by ring
        _ = (N + 1) ^ (a :: w).length * (regSize η + 1) := by simp

/-- **Exercise `exer:sst-copyful-sst-output-size`** (the upper bound).  The output of a copyful
sst has at most exponential size: there are constants `M` and `c ≥ 1` with
`|T.eval w| ≤ M · c^{|w|}`.  In particular it is not doubly exponential.  The proof is the
author's: reading one input letter multiplies the combined length of the registers by at most the
fixed constant `c`, the maximal number of times a register name is used in an update. -/
theorem CopyfulSST.output_length_exp_bound [Finite Q] [Finite A] (T : CopyfulSST A B Q X) :
    ∃ M c : ℕ, 1 ≤ c ∧ ∀ w : List A, (T.eval w).length ≤ M * c ^ w.length := by
  obtain ⟨N, hN⟩ := Finite.exists_le (fun p : Q × A => ∑ x : X, ((T.step p.1 p.2).2 x).length)
  obtain ⟨M, hM⟩ := Finite.exists_le (fun q : Q => (T.final q).length)
  refine ⟨M, N + 1, Nat.le_add_left 1 N, fun w => ?_⟩
  have hreg : regSize (T.runConfig w).2 + 1 ≤ (N + 1) ^ w.length := by
    have h := regSize_foldl_le T (fun q a => hN (q, a)) w T.init (fun _ => [])
    simpa [regSize] using h
  calc (T.eval w).length
      = (SST.subst (T.runConfig w).2 (T.final (T.runConfig w).1)).length := rfl
    _ ≤ (T.final (T.runConfig w).1).length * (regSize (T.runConfig w).2 + 1) :=
        length_subst_le _ _
    _ ≤ M * (N + 1) ^ w.length :=
        Nat.mul_le_mul (hM _) hreg

end OutputSize

/-- The copyful sst of the author's solution: one register `X`, which starts empty and is updated
by `X ↦ XXa`, with the output function `X`.  After reading `n` letters the register stores a string
of length `2ⁿ - 1`. -/
def doubleSST : CopyfulSST Unit Unit Unit Unit where
  init := ()
  step := fun _ _ => ((), fun _ => [Sum.inl (), Sum.inl (), Sum.inr ()])
  final := fun _ => [Sum.inl ()]

lemma doubleSST_register (n : ℕ) (η : Unit → List Unit) :
    (((List.replicate n ()).foldl doubleSST.stepConfig ((), η)).2 ()).length
      = 2 ^ n * ((η ()).length + 1) - 1 := by
  induction n generalizing η with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ,
        show ((() :: List.replicate n ()).foldl doubleSST.stepConfig ((), η))
          = (List.replicate n ()).foldl doubleSST.stepConfig
              (doubleSST.stepConfig ((), η) ()) from rfl]
      have hstep : (doubleSST.stepConfig ((), η) ()).2 ()
          = η () ++ (η () ++ [()]) := by
        simp [CopyfulSST.stepConfig, doubleSST, SST.subst]
      rw [show (doubleSST.stepConfig ((), η) ()) = ((), (doubleSST.stepConfig ((), η) ()).2) from
        rfl, ih]
      rw [hstep]
      have : (η () ++ (η () ++ [()])).length = 2 * (η ()).length + 1 := by
        simp [List.length_append]
        ring
      rw [this]
      have h2 : 2 ^ (n + 1) * ((η ()).length + 1)
          = 2 ^ n * (2 * (η ()).length + 1 + 1) := by ring
      rw [h2]

lemma doubleSST_eval_length (n : ℕ) :
    (doubleSST.eval (List.replicate n ())).length = 2 ^ n - 1 := by
  have h := doubleSST_register n (fun _ => [])
  show (SST.subst (doubleSST.runConfig _).2 (doubleSST.final _)).length = _
  rw [show (doubleSST.runConfig (List.replicate n ())).2
        = ((List.replicate n ()).foldl doubleSST.stepConfig ((), fun _ => [])).2 from rfl]
  simpa [doubleSST, SST.subst] using h

/-- **Exercise `exer:sst-copyful-sst-output-size`** (the bound is attained).  The function
`aⁿ ↦ a^{2ⁿ-1}` is computed by a copyful sst. -/
theorem exists_isCopyfulSST_exponential :
    ∃ f : List Unit → List Unit, IsCopyfulSST f ∧
      ∀ n : ℕ, (f (List.replicate n ())).length = 2 ^ n - 1 :=
  ⟨doubleSST.eval, ⟨Unit, Unit, inferInstance, inferInstance, doubleSST, rfl⟩,
    doubleSST_eval_length⟩

/-! ### Exercise `exer:sst-copyful-sst-no-composition` -/

lemma list_unit_eq_replicate (l : List Unit) : l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x; simpa [List.replicate_succ] using ih

/-- A linear function is eventually below the powers of two. -/
lemma exists_linear_lt_two_pow (a b : ℕ) : ∃ n : ℕ, a + b * n < 2 ^ n := by
  refine ⟨2 * (a + 2 * b + 1), ?_⟩
  set m := a + 2 * b + 1 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hm : m < 2 ^ m := Nat.lt_two_pow_self
  have h1 : a + b * (2 * m) < m * m := by nlinarith
  have h2 : m * m ≤ 2 ^ (2 * m) := by
    calc m * m ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul (le_of_lt hm) (le_of_lt hm)
      _ = 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
  omega

/-- The doubly exponential function `n ↦ 2^{2ⁿ-1}-1` outgrows every function `M · cⁿ`. -/
lemma exists_gt_exp_bound (M c : ℕ) : ∃ n : ℕ, M * c ^ n < 2 ^ (2 ^ n - 1) - 1 := by
  obtain ⟨k, hk⟩ : ∃ k, M ≤ 2 ^ k := ⟨M, le_of_lt Nat.lt_two_pow_self⟩
  obtain ⟨j, hj⟩ : ∃ j, c ≤ 2 ^ j := ⟨c, le_of_lt Nat.lt_two_pow_self⟩
  obtain ⟨n, hn⟩ := exists_linear_lt_two_pow (k + 3) j
  refine ⟨n, ?_⟩
  have hMc : M * c ^ n ≤ 2 ^ (k + j * n) := by
    calc M * c ^ n ≤ 2 ^ k * (2 ^ j) ^ n :=
          Nat.mul_le_mul hk (Nat.pow_le_pow_left hj n)
      _ = 2 ^ (k + j * n) := by rw [← pow_mul, ← pow_add]
  have hle : k + j * n + 2 ≤ 2 ^ n - 1 := by omega
  have hpow : 2 ^ (k + j * n + 2) ≤ 2 ^ (2 ^ n - 1) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have hexp : 2 ^ (k + j * n + 2) = 4 * 2 ^ (k + j * n) := by ring
  have hone : 1 ≤ 2 ^ (k + j * n) := Nat.one_le_two_pow
  omega

/-- **Exercise `exer:sst-copyful-sst-no-composition`.**  Copyful ssts are not closed under
composition.  The proof is the author's: the function `aⁿ ↦ a^{2ⁿ-1}` is computed by a copyful
sst, but its composition with itself has doubly exponential output size, which Exercise
`exer:sst-copyful-sst-output-size` forbids. -/
theorem exists_isCopyfulSST_comp_not_isCopyfulSST :
    ∃ f : List Unit → List Unit, IsCopyfulSST f ∧ ¬ IsCopyfulSST (f ∘ f) := by
  refine ⟨doubleSST.eval, ⟨Unit, Unit, inferInstance, inferInstance, doubleSST, rfl⟩, ?_⟩
  rintro ⟨Q, X, hQ, hX, T, hT⟩
  obtain ⟨M, c, _, hbound⟩ := T.output_length_exp_bound
  obtain ⟨n, hn⟩ := exists_gt_exp_bound M c
  have hlen : (doubleSST.eval (doubleSST.eval (List.replicate n ()))).length
      = 2 ^ (2 ^ n - 1) - 1 := by
    rw [show doubleSST.eval (List.replicate n ())
          = List.replicate (doubleSST.eval (List.replicate n ())).length () from
      list_unit_eq_replicate _, doubleSST_eval_length, doubleSST_eval_length]
  have hb := hbound (List.replicate n ())
  rw [hT] at hb
  simp only [Function.comp_apply] at hb
  rw [hlen, List.length_replicate] at hb
  omega

/-! ### Exercises `exer:sst-polynomial-automaton` and
`exer:sst-polynomial-automaton-doubly-exponential` -/

/-- The polynomial automaton of the author's solution to Exercise `exer:sst-polynomial-automaton`:
one register, which starts with `1` and is doubled in each step. -/
noncomputable def doublingPolyAut : PolyAut Unit Unit Unit where
  init := ()
  initVal := fun _ => 1
  step := fun _ _ => ((), fun _ => 2 * MvPolynomial.X ())
  final := fun _ => MvPolynomial.X ()

lemma doublingPolyAut_run (n : ℕ) (v : ℚ) :
    (((List.replicate n ()).foldl doublingPolyAut.stepVal ((), fun _ => v)).2 ())
      = 2 ^ n * v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ,
        show ((() :: List.replicate n ()).foldl doublingPolyAut.stepVal ((), fun _ => v))
          = (List.replicate n ()).foldl doublingPolyAut.stepVal
              (doublingPolyAut.stepVal ((), fun _ => v) ()) from rfl]
      rw [show doublingPolyAut.stepVal ((), fun _ => v) () = ((), fun _ => 2 * v) by
        simp [PolyAut.stepVal, doublingPolyAut]]
      rw [ih]
      ring

/-- **Exercise `exer:sst-polynomial-automaton`.**  The function `aⁿ ↦ 2ⁿ` is computed by a
polynomial automaton. -/
theorem isPolyAut_two_pow :
    IsPolyAut (fun w : List Unit => (2 : ℚ) ^ w.length) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, doublingPolyAut, ?_⟩
  funext w
  rw [show w = List.replicate w.length () from list_unit_eq_replicate w]
  show MvPolynomial.eval (doublingPolyAut.runConfig _).2 (MvPolynomial.X ()) = _
  simp only [MvPolynomial.eval_X]
  rw [show (doublingPolyAut.runConfig (List.replicate w.length ())).2
        = ((List.replicate w.length ()).foldl doublingPolyAut.stepVal ((), fun _ => 1)).2 from rfl,
    doublingPolyAut_run]
  simp

/-- The polynomial automaton of the author's solution to Exercise
`exer:sst-polynomial-automaton-doubly-exponential`: one register, which starts with `2` and is
squared in each step. -/
noncomputable def squaringPolyAut : PolyAut Unit Unit Unit where
  init := ()
  initVal := fun _ => 2
  step := fun _ _ => ((), fun _ => MvPolynomial.X () * MvPolynomial.X ())
  final := fun _ => MvPolynomial.X ()

lemma squaringPolyAut_run (n : ℕ) (v : ℚ) :
    (((List.replicate n ()).foldl squaringPolyAut.stepVal ((), fun _ => v)).2 ())
      = v ^ (2 ^ n) := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ,
        show ((() :: List.replicate n ()).foldl squaringPolyAut.stepVal ((), fun _ => v))
          = (List.replicate n ()).foldl squaringPolyAut.stepVal
              (squaringPolyAut.stepVal ((), fun _ => v) ()) from rfl]
      rw [show squaringPolyAut.stepVal ((), fun _ => v) () = ((), fun _ => v * v) by
        simp [PolyAut.stepVal, squaringPolyAut]]
      rw [ih, show v * v = v ^ 2 by ring, ← pow_mul]
      congr 1
      ring

/-- **Exercise `exer:sst-polynomial-automaton-doubly-exponential`.**  The function `aⁿ ↦ 2^{2ⁿ}` is
computed by a polynomial automaton. -/
theorem isPolyAut_two_pow_two_pow :
    IsPolyAut (fun w : List Unit => (2 : ℚ) ^ (2 ^ w.length)) := by
  refine ⟨Unit, Unit, inferInstance, inferInstance, squaringPolyAut, ?_⟩
  funext w
  rw [show w = List.replicate w.length () from list_unit_eq_replicate w]
  show MvPolynomial.eval (squaringPolyAut.runConfig _).2 (MvPolynomial.X ()) = _
  simp only [MvPolynomial.eval_X]
  rw [show (squaringPolyAut.runConfig (List.replicate w.length ())).2
        = ((List.replicate w.length ()).foldl squaringPolyAut.stepVal ((), fun _ => 2)).2 from rfl,
    squaringPolyAut_run]
  simp

end Transducers.Exercises
