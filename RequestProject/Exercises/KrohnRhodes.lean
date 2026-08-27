/-
Two further exercises of the chapter *The Krohn-Rhodes Decomposition Theorem*
(`krohn-rhodes.tex`) of *Transducers* (M. Bojańczyk).

The exercises of that chapter that were formalised first live in
`RequestProject/Exercises/PartA.lean`; this file continues them, and reuses the machinery
(`CompClosure`, `FlipFlopFam`, `ReversibleFam`, `isReversibleMealy_of_compClosure`) that is
developed there.  Exercises are not numbered results of the book, so they are recorded in
`EXERCISES.md` and not in `THEOREMS.md`, and they are referred to by their LaTeX label.
-/
import RequestProject.Exercises.PartA

namespace Transducers

/-! ## The Krohn-Rhodes Decomposition Theorem (`krohn-rhodes.tex`), continued -/

/-! ### Exercises `exer:simple-decomposition-example` and `exer:simple-decomposition-example-2` -/

/-- The function of Exercise `exer:simple-decomposition-example`: every letter of the input is
replaced by the first input letter, `a₁ ⋯ aₙ ↦ a₁ⁿ`. -/
def firstConst {A : Type} : List A → List A
  | [] => []
  | a :: w => a :: w.map (fun _ => a)

@[simp] lemma firstConst_nil {A : Type} : firstConst ([] : List A) = [] := rfl

@[simp] lemma firstConst_cons {A : Type} (a : A) (w : List A) :
    firstConst (a :: w) = a :: w.map (fun _ => a) := rfl

/-- The first machine of the author's solution: its two states record whether a letter has already
been read, and the output of a position is the input letter together with the state *before* the
transition, so that exactly the first position is marked `false`.  Every letter has the constant
state transformation with value `true`, so this is a flip-flop machine. -/
def firstMark (A : Type) : Mealy A (A × Bool) Bool := ⟨false, fun s a => (true, (a, s))⟩

/-- The second machine of the author's solution: its states are `A + 1`, it stores the first input
letter, and it outputs the state *after* the transition.  A letter marked `false` — the first one —
has the constant state transformation with that letter as value, and a letter marked `true` has the
identity state transformation, so this is a flip-flop machine as well. -/
def pickFirst (A : Type) : Mealy (A × Bool) A (Option A) :=
  ⟨none, fun q ab => ((if ab.2 then q else some ab.1), (if ab.2 then q else some ab.1).getD ab.1)⟩

lemma firstMark_flipFlop (A : Type) : (firstMark A).FlipFlop := by
  intro a
  exact Or.inr ⟨true, fun _ => rfl⟩

lemma pickFirst_flipFlop (A : Type) : (pickFirst A).FlipFlop := by
  rintro ⟨a, b⟩
  cases b with
  | true => exact Or.inl rfl
  | false => exact Or.inr ⟨some a, fun _ => rfl⟩

lemma firstMark_run_true {A : Type} (w : List A) :
    (firstMark A).run true w = w.map (fun x => (x, true)) := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa [firstMark] using ih

lemma pickFirst_run_some {A : Type} (a : A) (w : List A) :
    (pickFirst A).run (some a) (w.map (fun x => (x, true))) = w.map (fun _ => a) := by
  induction w with
  | nil => rfl
  | cons x w ih => simpa [pickFirst] using ih

lemma pickFirst_eval_firstMark_eval {A : Type} (w : List A) :
    (pickFirst A).eval ((firstMark A).eval w) = firstConst w := by
  cases w with
  | nil => rfl
  | cons a w =>
      show (pickFirst A).run none ((firstMark A).run false (a :: w)) = _
      rw [Mealy.run_cons]
      show (pickFirst A).run none ((a, false) :: (firstMark A).run true w) = _
      rw [firstMark_run_true, Mealy.run_cons]
      simpa [pickFirst] using pickFirst_run_some a w

/-- **Exercise `exer:simple-decomposition-example`.**  The function that replaces every letter of
the input by the first input letter is a composition of flip-flop Mealy machines.  The
decomposition is the author's: a first flip-flop marks the first position, and a second flip-flop,
whose states are `A + 1`, stores the letter found there. -/
theorem firstConst_flipflop_decomposition {A : Type} [Finite A] :
    CompClosure FlipFlopFam A A (firstConst : List A → List A) := by
  have h : (firstConst : List A → List A) = (pickFirst A).eval ∘ (firstMark A).eval :=
    funext fun w => (pickFirst_eval_firstMark_eval w).symm
  rw [h]
  exact CompClosure.comp
    (CompClosure.base ⟨Bool, inferInstance, firstMark A, rfl, firstMark_flipFlop A⟩)
    (CompClosure.base ⟨Option A, inferInstance, pickFirst A, rfl, pickFirst_flipFlop A⟩)

/-- **Exercise `exer:simple-decomposition-example-2`.**  The same function is not a composition of
reversible Mealy machines, as soon as the input alphabet has two distinct letters (over a
one-letter alphabet it is the identity, which is reversible).  The proof is the author's, and the
one of `Transducers.delay_not_reversible_composition`: a composition of reversible machines is a
single reversible machine, the state transformation of `a` has finite order, so the machine is in
its initial state before the last letter of both `b` and `aᵏb`, and hence produces the same last
output letter, whereas the function outputs `b` on the first input and `a` on the second. -/
theorem firstConst_not_reversible_composition {A : Type} {a b : A} (hab : a ≠ b) :
    ¬ CompClosure ReversibleFam A A (firstConst : List A → List A) := by
  intro h
  obtain ⟨Q, hQ, M, hM, hrev⟩ := isReversibleMealy_of_compClosure h
  haveI := hQ
  obtain ⟨i, j, hij, hfe⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ => (M.letterTrans a)^[n] M.init)
  obtain ⟨i, j, hlt, hfe⟩ : ∃ i j : ℕ, i < j ∧
      (M.letterTrans a)^[i] M.init = (M.letterTrans a)^[j] M.init := by
    rcases lt_or_gt_of_ne hij with h' | h'
    · exact ⟨i, j, h', hfe⟩
    · exact ⟨j, i, h', hfe.symm⟩
  obtain ⟨m, hiter⟩ : ∃ m : ℕ, (M.letterTrans a)^[m + 1] M.init = M.init := by
    refine ⟨j - i - 1, ?_⟩
    have hji : j = i + (j - i - 1 + 1) := by omega
    rw [hji, Function.iterate_add_apply] at hfe
    exact ((Function.Injective.iterate (hrev a).1 i) hfe).symm
  have htr : M.trans (List.replicate (m + 1) a) M.init = M.init := by
    rw [Mealy.trans_replicate, hiter]
  have e1 : (M.eval (List.replicate (m + 1) a ++ [b])).getLast? = some ((M.step M.init b).2) := by
    rw [M.eval_append, htr]
    simp [Mealy.run]
  have e2 : (M.eval [b]).getLast? = some ((M.step M.init b).2) := by
    simp [Mealy.eval, Mealy.run]
  rw [hM] at e1 e2
  have hmap : ∀ l : List A, l.map (fun _ => a) = List.replicate l.length a := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [List.replicate_succ, ih]
  have g1 : (firstConst (List.replicate (m + 1) a ++ [b])).getLast? = some a := by
    have h1 : firstConst (List.replicate (m + 1) a ++ [b]) = List.replicate (m + 2) a := by
      rw [List.replicate_succ, List.cons_append, firstConst_cons, hmap]
      simp [List.replicate_succ]
    rw [h1, List.replicate_succ']
    exact List.getLast?_concat
  have g2 : (firstConst ([b] : List A)).getLast? = some b := by simp
  rw [g1] at e1
  rw [g2] at e2
  rw [← e2] at e1
  exact hab (by simpa using e1)

end Transducers
