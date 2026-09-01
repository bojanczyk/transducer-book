/-
The time order of the visits to a cut can be read off from a rational
annotation of the input.

`RequestProject/PartC/TwoWayAnnot.lean` annotates every position of the input
with the state of a deterministic automaton `D` on the prefix and with the
acceptance function of `D` on the suffix, and shows that the annotation is
computed by a bimachine, hence is a rational function
(`TwoWay.isRationalFun_annot`).  That construction is generic in the marked
alphabet, so it can be used with *any* automaton over marked inputs.

Here it is used with the automaton of `RequestProject/PartC/TwoWayOrder.lean`,
whose marker is a *pair* of states: the annotation of a position then decides,
for every pair `(q₁, q₂)` of states, whether the run of `M` visits the cut
adjacent to that position in the state `q₁` before it ever visits it in the
state `q₂`.  Since the visits to a cut are in pairwise distinct states, this
determines the *sequence* of visits to every cut, and not only the set of states
that occur there, which is what the record-breaking columns of the book's snake
lemma are defined from.
-/
import RequestProject.PartC.TwoWayAnnotBim
import RequestProject.PartC.TwoWayOrder

namespace Transducers

namespace TwoWay

open scoped Classical

variable {A B Q S : Type} (D : DFA (Marked A (Q × Q)) S) (M : TwoWay A B Q)

/-- Evaluating `D` on the input marked, at the cut left of the letter `a`, with
a pair of states. -/
lemma rhoOf_step_before_inl_iff (hD : D.accepts = {z | (orderAut M).Accepts z})
    (x : List A) (a : A) (y : List A) (q₁ q₂ : Q) :
    rhoOf D y (D.step (leftSt D x) (a, some (Sum.inl (q₁, q₂)))) = true ↔
      VisitsBefore M (x ++ a :: y) (Cfg.conf x q₁ (a :: y)) (Cfg.conf x q₂ (a :: y)) := by
  have hev : D.eval (plainList (Q × Q) x ++ (a, some (Sum.inl (q₁, q₂))) :: plainList (Q × Q) y)
      = D.evalFrom (D.step (leftSt D x) (a, some (Sum.inl (q₁, q₂)))) (plainList (Q × Q) y) := by
    rw [DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_cons]; rfl
  have hr : rhoOf D y (D.step (leftSt D x) (a, some (Sum.inl (q₁, q₂))))
      = decide (D.eval (plainList (Q × Q) x ++ (a, some (Sum.inl (q₁, q₂)))
        :: plainList (Q × Q) y) ∈ D.accept) := by
    rw [hev]; rfl
  rw [hr, decide_eq_true_iff, ← DFA.mem_accepts, hD,
    visits_before_iff_accepts_left M x a y q₁ q₂]
  exact Iff.rfl

/-- Evaluating `D` on the input marked, at the cut right of the letter `a`, with
a pair of states. -/
lemma rhoOf_step_before_inr_iff (hD : D.accepts = {z | (orderAut M).Accepts z})
    (x : List A) (a : A) (y : List A) (q₁ q₂ : Q) :
    rhoOf D y (D.step (leftSt D x) (a, some (Sum.inr (q₁, q₂)))) = true ↔
      VisitsBefore M (x ++ a :: y) (Cfg.conf (x ++ [a]) q₁ y) (Cfg.conf (x ++ [a]) q₂ y) := by
  have hev : D.eval (plainList (Q × Q) x ++ (a, some (Sum.inr (q₁, q₂))) :: plainList (Q × Q) y)
      = D.evalFrom (D.step (leftSt D x) (a, some (Sum.inr (q₁, q₂)))) (plainList (Q × Q) y) := by
    rw [DFA.eval, DFA.evalFrom_of_append, DFA.evalFrom_cons]; rfl
  have hr : rhoOf D y (D.step (leftSt D x) (a, some (Sum.inr (q₁, q₂))))
      = decide (D.eval (plainList (Q × Q) x ++ (a, some (Sum.inr (q₁, q₂)))
        :: plainList (Q × Q) y) ∈ D.accept) := by
    rw [hev]; rfl
  rw [hr, decide_eq_true_iff, ← DFA.mem_accepts, hD,
    visits_before_iff_accepts_right M x a y q₁ q₂]
  exact Iff.rfl

/-- **The annotation of a position decides in which order the run visits the cut
to the left of that position.** -/
theorem onRunLeft_before_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q₁ q₂ : Q) :
    onRunLeft D c (q₁, q₂) = true ↔
      VisitsBefore M w (Cfg.conf (w.take j) q₁ (w.drop j))
        (Cfg.conf (w.take j) q₂ (w.drop j)) := by
  rw [annot_eq_at D w hj hc]
  have hdrop : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj
  show rhoOf D (w.drop (j + 1))
      (D.step (leftSt D (w.take j)) (w[j], some (Sum.inl (q₁, q₂)))) = true ↔ _
  rw [rhoOf_step_before_inl_iff D M hD (w.take j) (w[j]'hj) (w.drop (j + 1)) q₁ q₂, ← hdrop,
    List.take_append_drop]

/-- **The annotation of a position decides in which order the run visits the cut
to the right of that position.** -/
theorem onRunRight_before_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q₁ q₂ : Q) :
    onRunRight D c (q₁, q₂) = true ↔
      VisitsBefore M w (Cfg.conf (w.take (j + 1)) q₁ (w.drop (j + 1)))
        (Cfg.conf (w.take (j + 1)) q₂ (w.drop (j + 1))) := by
  rw [annot_eq_at D w hj hc]
  have hdrop : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj
  have htake : w.take (j + 1) = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem hj
  show rhoOf D (w.drop (j + 1))
      (D.step (leftSt D (w.take j)) (w[j], some (Sum.inr (q₁, q₂)))) = true ↔ _
  rw [rhoOf_step_before_inr_iff D M hD (w.take j) (w[j]'hj) (w.drop (j + 1)) q₁ q₂, ← htake,
    ← hdrop, List.take_append_drop]

/-! ## The first and the last visit to a cut, read off from the annotation -/

/-- The annotation decides whether the run visits the cut to the left of the
annotated position in a given state. -/
theorem onRunLeft_self_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    onRunLeft D c (q, q) = true ↔ Visits M w (Cfg.conf (w.take j) q (w.drop j)) := by
  rw [onRunLeft_before_iff D M hD w hj c hc q q, visitsBefore_self_iff]

/-- The annotation decides whether the run visits the cut to the right of the
annotated position in a given state. -/
theorem onRunRight_self_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    onRunRight D c (q, q) = true ↔
      Visits M w (Cfg.conf (w.take (j + 1)) q (w.drop (j + 1))) := by
  rw [onRunRight_before_iff D M hD w hj c hc q q, visitsBefore_self_iff]

/-- **The state of the last visit to the cut to the left of a position is read
off from the annotation of that position.** -/
theorem isLastVisitAt_left_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    IsLastVisitAt M w (w.take j) (w.drop j) q ↔
      ∀ q' : Q, onRunLeft D c (q', q') = true → onRunLeft D c (q', q) = true := by
  constructor
  · intro h q' hq'
    rw [onRunLeft_before_iff D M hD w hj c hc q' q]
    exact h q' ((onRunLeft_self_iff D M hD w hj c hc q').1 hq')
  · intro h q' hq'
    rw [← onRunLeft_before_iff D M hD w hj c hc q' q]
    exact h q' ((onRunLeft_self_iff D M hD w hj c hc q').2 hq')

/-- **The state of the first visit to the cut to the left of a position is read
off from the annotation of that position.** -/
theorem isFirstVisitAt_left_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    IsFirstVisitAt M w (w.take j) (w.drop j) q ↔
      ∀ q' : Q, onRunLeft D c (q', q') = true → onRunLeft D c (q, q') = true := by
  constructor
  · intro h q' hq'
    rw [onRunLeft_before_iff D M hD w hj c hc q q']
    exact h q' ((onRunLeft_self_iff D M hD w hj c hc q').1 hq')
  · intro h q' hq'
    rw [← onRunLeft_before_iff D M hD w hj c hc q q']
    exact h q' ((onRunLeft_self_iff D M hD w hj c hc q').2 hq')

/-- **The state of the last visit to the cut to the right of a position is read
off from the annotation of that position.** -/
theorem isLastVisitAt_right_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    IsLastVisitAt M w (w.take (j + 1)) (w.drop (j + 1)) q ↔
      ∀ q' : Q, onRunRight D c (q', q') = true → onRunRight D c (q', q) = true := by
  constructor
  · intro h q' hq'
    rw [onRunRight_before_iff D M hD w hj c hc q' q]
    exact h q' ((onRunRight_self_iff D M hD w hj c hc q').1 hq')
  · intro h q' hq'
    rw [← onRunRight_before_iff D M hD w hj c hc q' q]
    exact h q' ((onRunRight_self_iff D M hD w hj c hc q').2 hq')

/-- **The state of the first visit to the cut to the right of a position is read
off from the annotation of that position.** -/
theorem isFirstVisitAt_right_iff (hD : D.accepts = {z | (orderAut M).Accepts z}) (w : List A)
    {j : ℕ} (hj : j < w.length) (c : AnnLet A S) (hc : (annot D w)[j]? = some c) (q : Q) :
    IsFirstVisitAt M w (w.take (j + 1)) (w.drop (j + 1)) q ↔
      ∀ q' : Q, onRunRight D c (q', q') = true → onRunRight D c (q, q') = true := by
  constructor
  · intro h q' hq'
    rw [onRunRight_before_iff D M hD w hj c hc q q']
    exact h q' ((onRunRight_self_iff D M hD w hj c hc q').1 hq')
  · intro h q' hq'
    rw [← onRunRight_before_iff D M hD w hj c hc q q']
    exact h q' ((onRunRight_self_iff D M hD w hj c hc q').2 hq')

/-- **The time order of the visits of a run to the cuts of the input is computed
by a rational function.**  There is a rational annotation of the input, which
leaves the input letters in place, from which one can read off at every position
`j`, and for every pair of states `(q₁, q₂)`, whether the run visits the cut on
either side of `j` in the state `q₁` before it ever visits it in the state `q₂`.

This is the form in which the order of the visits enters the book's proof of the
snake lemma: the record-breaking columns are defined by a recursion that refers
to the first and to the last visit to a column, and the annotation makes that
recursion a property of a string over a fixed finite alphabet. -/
theorem exists_rational_visitOrder_annot [Finite A] [Finite Q] :
    ∃ (S : Type) (_ : Fintype S) (D : DFA (Marked A (Q × Q)) S),
      IsRationalFun (annot D) ∧
      (∀ w : List A, (annot D w).map AnnLet.letter = w) ∧
      (∀ (w : List A) (j : ℕ), j < w.length → ∀ c : AnnLet A S, (annot D w)[j]? = some c →
        ∀ q₁ q₂ : Q,
          (onRunLeft D c (q₁, q₂) = true ↔
            VisitsBefore M w (Cfg.conf (w.take j) q₁ (w.drop j))
              (Cfg.conf (w.take j) q₂ (w.drop j))) ∧
          (onRunRight D c (q₁, q₂) = true ↔
            VisitsBefore M w (Cfg.conf (w.take (j + 1)) q₁ (w.drop (j + 1)))
              (Cfg.conf (w.take (j + 1)) q₂ (w.drop (j + 1))))) := by
  classical
  obtain ⟨S, hS, D, hD⟩ := orderLang_isRegular M
  haveI : Fintype S := hS
  exact ⟨S, hS, D, isRationalFun_annot D, annot_map_letter D,
    fun w j hj c hc q₁ q₂ =>
      ⟨onRunLeft_before_iff D M hD w hj c hc q₁ q₂,
        onRunRight_before_iff D M hD w hj c hc q₁ q₂⟩⟩

end TwoWay

end Transducers
