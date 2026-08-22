/-
Sequential rewritings are rational functions.

A *sequential rewriting* reads the input string from left to right and, at every
letter, produces a block that depends on the letter and on the state of a
deterministic automaton on the prefix that precedes it.  This is a special case
of a bimachine (the suffix automaton only has to remember the letter that
follows the current gap), and it is the last of the small builders of rational
functions used in the proof of Lemma C.2.10 of *Transducers* (M. Bojańczyk).
-/
import RequestProject.PartC.RatBuild

namespace Transducers

variable {A B Mo : Type}

/-- A sequential rewriting: at every letter the block `ψ m a` is produced, where
`m` is the state reached by the deterministic automaton `(Mo, μ, m₀)` on the
prefix that precedes the letter. -/
def seqEval (μ : Mo → A → Mo) (ψ : Mo → A → List B) : Mo → List A → List B
  | _, [] => []
  | m, a :: w => ψ m a ++ seqEval μ ψ (μ m a) w

@[simp] lemma seqEval_nil (μ : Mo → A → Mo) (ψ : Mo → A → List B) (m : Mo) :
    seqEval μ ψ m [] = [] := rfl

@[simp] lemma seqEval_cons (μ : Mo → A → Mo) (ψ : Mo → A → List B) (m : Mo) (a : A)
    (w : List A) : seqEval μ ψ m (a :: w) = ψ m a ++ seqEval μ ψ (μ m a) w := rfl

/-- The bimachine computing a sequential rewriting. -/
def seqBim (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → A → List B) : Bimachine A B Mo (Option A) where
  prefixInit := m₀
  prefixStep := μ
  suffixInit := none
  suffixStep := fun _ a => some a
  out := fun p s => match s with | none => [] | some a => ψ p a

lemma seqBim_evalFrom (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → A → List B) (p : Mo)
    (w : List A) : (seqBim μ m₀ ψ).evalFrom p w = seqEval μ ψ p w := by
  induction w generalizing p with
  | nil => simp [seqBim]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', bmSfx_cons, ih]
      rfl

/-- A sequential rewriting is a rational function. -/
theorem isRationalFun_seqEval [Finite A] [Finite B] [Finite Mo] (μ : Mo → A → Mo) (m₀ : Mo)
    (ψ : Mo → A → List B) : IsRationalFun (seqEval μ ψ m₀) :=
  isRationalFun_of_bimachine (seqBim μ m₀ ψ) (fun w => by
    rw [Bimachine.eval_eq_evalFrom]
    exact seqBim_evalFrom μ m₀ ψ m₀ w)

end Transducers
