/-
Append-only streaming string transducers with one register compute rational functions.

A streaming string transducer with a single register whose every update is `x := x · u`, and
whose final output is `x · u'`, never moves anything backwards: it reads the input from left to
right and appends, at every letter, a block that depends on the letter and on the state reached
on the prefix before it, and one last block at the end that depends on the state reached on the
whole input.  Such a function is a sequential rewriting with a final output, hence a bimachine
whose suffix automaton only has to remember the letter that follows the current gap, hence a
rational function (Theorem `thm:bimachines`).

This is the observation that the solution of Exercise `exer:forward-for-transducer` of
*Transducers* (M. Bojańczyk) needs about the *scan* of the enumeration: the project shows the
scanning machine is a streaming string transducer, hence computes a regular function, whereas the
exercise needs its function to be rational.  The scanning machine has one register and only
appends to it, so the lemma below applies; see
`Transducers.Exercises.isRationalFun_scanFun` in
`RequestProject/Exercises/ForwardForTop.lean`.
-/
import RequestProject.PartC.RatSeq
import RequestProject.PartC.SSTDef

namespace Transducers
namespace Exercises

variable {A B Q : Type}

/-! ## Append-only transducers with one register -/

/-- The state reached by a deterministic automaton after reading a string. -/
def sstState (step : Q → A → Q) : Q → List A → Q
  | q, [] => q
  | q, a :: w => sstState step (step q a) w

/-- The string appended to the register while reading a string. -/
def sstCollect (step : Q → A → Q) (out : Q → A → List B) : Q → List A → List B
  | _, [] => []
  | q, a :: w => out q a ++ sstCollect step out (step q a) w

lemma seqFinEval_eq_collect (step : Q → A → Q) (out : Q → A → List B) (fin : Q → List B) :
    ∀ (q : Q) (w : List A),
      seqFinEval step out fin q w = sstCollect step out q w ++ fin (sstState step q w) := by
  intro q w
  induction w generalizing q with
  | nil => simp [sstCollect, sstState]
  | cons a w ih => simp [sstCollect, sstState, ih, List.append_assoc]

lemma subst_unit_append (r : Unit → List B) (l : List B) :
    SST.subst r (Sum.inl () :: l.map (Sum.inr : B → Unit ⊕ B)) = r () ++ l := by
  rw [SST.subst]
  simp only [List.map_cons, List.map_map, List.flatten_cons]
  congr 1
  induction l with
  | nil => rfl
  | cons b l ih => simpa using ih

section AppendOnly

variable (T : SST A B Q Unit) (out : Q → A → List B) (fin : Q → List B)
  (hstep : ∀ q a, (T.step q a).2 () = Sum.inl () :: (out q a).map Sum.inr)

include hstep

lemma foldl_stepConfig_append : ∀ (w : List A) (q : Q) (r : Unit → List B),
    w.foldl T.stepConfig (q, r)
      = (sstState (fun q a => (T.step q a).1) q w,
          fun _ => r () ++ sstCollect (fun q a => (T.step q a).1) out q w) := by
  intro w
  induction w with
  | nil => intro q r; simp [sstState, sstCollect]
  | cons a w ih =>
      intro q r
      have hcfg : T.stepConfig (q, r) a
          = ((T.step q a).1, fun _ => r () ++ out q a) := by
        refine Prod.ext rfl ?_
        funext x
        cases x
        rw [SST.stepConfig]
        simp only
        rw [hstep q a, subst_unit_append]
      rw [List.foldl_cons, hcfg, ih]
      refine Prod.ext rfl ?_
      funext x
      simp [sstCollect, List.append_assoc]

include fin in
/-- **An append-only transducer with one register computes a sequential rewriting with a final
output.** -/
theorem sst_eval_eq_seqFinEval
    (hfinal : ∀ q, T.final q = Sum.inl () :: (fin q).map Sum.inr) (w : List A) :
    T.eval w = seqFinEval (fun q a => (T.step q a).1) out fin T.init w := by
  rw [SST.eval, SST.runConfig, foldl_stepConfig_append T out hstep w T.init (fun _ => []),
    hfinal, subst_unit_append, seqFinEval_eq_collect]
  simp

end AppendOnly

/-- **An append-only transducer with one register computes a rational function.** -/
theorem isRationalFun_of_appendOnlySST [Finite A] [Finite B] [Finite Q] (T : SST A B Q Unit)
    (out : Q → A → List B) (fin : Q → List B)
    (hstep : ∀ q a, (T.step q a).2 () = Sum.inl () :: (out q a).map Sum.inr)
    (hfinal : ∀ q, T.final q = Sum.inl () :: (fin q).map Sum.inr) :
    IsRationalFun T.eval := by
  have h : T.eval = seqFinEval (fun q a => (T.step q a).1) out fin T.init :=
    funext (sst_eval_eq_seqFinEval T out fin hstep hfinal)
  exact h ▸ isRationalFun_seqFinEval _ T.init out fin

end Exercises
end Transducers
