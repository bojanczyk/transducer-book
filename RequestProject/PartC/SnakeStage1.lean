/-
**Stage 1 of the induction step of the book's snake lemma**: the rational
function that marks the record-breaking columns of a run and the pieces of the
record-breaker decomposition inside the blocks that they delimit.

This is the one remaining gap in Theorem C.2.9.  Everything else in the
induction step is proved:

* the decomposition of a halting run of width at most `K` into the pieces of the
  record-breaker decomposition is `TwoWay.runOut_eq_partsOut`
  (`RequestProject/PartC/SnakeParts.lean`);
* the identification of each piece with the whole run of a *window transducer*
  on a factor of the input, to which the induction hypothesis applies, is
  `TwoWay.exists_widthOut_excHalves`, `TwoWay.exists_widthOut_prog` and
  `TwoWay.exists_widthOut_finalProg`
  (`RequestProject/PartC/SnakePieceIdent.lean`);
* the *block function*, which recomputes the pieces of one block from the
  annotated input, is regular (`TwoWay.isRegularFun_blockFun`), and the
  neighbouring-block map combinator applied to it computes the output of the run
  (`TwoWay.pairMap_blockFun_eq_runOut`), both in
  `RequestProject/PartC/SnakeBlock.lean`.

What is stated here, and left open, is the book's first stage: *"we mark the
record-breakers, i.e. we compute the string `w₀ # w₁ # ⋯ # wₙ`, where `wᵢ` is
the part of the input string between the record-breakers `xᵢ₋₁` and `xᵢ`.  This
stage can be implemented by a rational function, since a nondeterministic
automaton with output can guess the record-breakers, and then check that they
satisfy the conditions in the definition."*  In the formalisation the annotation
has to carry a little more than the separators, because the pieces of a block
have to be recovered from the block alone: every letter of the annotated input
carries, for each of the `2K+1` piece slots of a block, the bit saying whether
it belongs to the window of that piece and the parameters of the window
transducer computing it (`TwoWay.SnakeLet`).  That is exactly what
`TwoWay.IsSnakeMarking` demands.

The intended proof is the book's: the annotation is *guessed* by a
nondeterministic automaton with output and *verified* by a regular language, the
verification being possible because

* the order in time of the visits of the run to a cut of the input is a rational
  annotation of the input (`TwoWay.exists_rational_visitOrder_annot` in
  `RequestProject/PartC/TwoWayAnnotOrd.lean`), so the crossing sequence at every
  cut is available letter by letter, and
* the record-breaking columns satisfy the left-to-right recursion "`x₀` is the
  starting column, and `xᵢ₊₁` is the column after the rightmost column visited
  before the last visit to `xᵢ`", which a finite automaton can follow along the
  annotated input by keeping track of the position, in the crossing sequence of
  the current cut, of the time of the last visit to `xᵢ`.
-/
import RequestProject.PartC.SnakeBlock

namespace Transducers

namespace TwoWay

open RegPair

variable {A B Q : Type}

/-- **Stage 1 of the induction step of the snake lemma** (still open).  For
every two-way transducer `M` and every width bound `K` there is a *rational*
annotation of the input which

* cuts the input into the blocks delimited by the record-breaking columns of the
  run, and
* marks, inside every pair of neighbouring blocks, the windows and the window
  transducers of the `2K+1` pieces into which the corresponding block of the
  record-breaker decomposition splits,

whenever the run halts and has width at most `K`, and which produces no
separator at all otherwise.  Together with
`TwoWay.pairMap_blockFun_eq_runOut` and `TwoWay.isRegularFun_blockFun` this
gives the induction step `Transducers.boundedWidth_isRegular_step`. -/
theorem exists_snakeMarking [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) (K : ℕ) :
    ∃ ann : List A → List (Option (SnakeLet A Q (2 * K + 1))),
      IsRationalFun ann ∧
      ∀ w : List A,
        (((∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K) →
            IsSnakeMarking M K w (ann w)) ∧
        (¬ ((∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K) →
            pairBlocks (ann w) = []) := by
  sorry

/-- **The width-`K` output function is the neighbouring-block map combinator
applied to the block function**, on the annotation of stage 1. -/
theorem widthOut_eq_pairMap [Finite A] [Finite B] [Finite Q] (M : TwoWay A B Q) (K : ℕ)
    {ann : List A → List (Option (SnakeLet A Q (2 * K + 1)))}
    (hann : ∀ w : List A,
      (((∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K) →
          IsSnakeMarking M K w (ann w)) ∧
      (¬ ((∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K) →
          pairBlocks (ann w) = [])) (w : List A) :
    widthOut M K w = pairMap (blockFun M (K - 1) (2 * K + 1)) (ann w) := by
  classical
  by_cases hgood : (∃ T, cfgAt M w T = some Cfg.halt) ∧ WidthLe M w K
  · obtain ⟨⟨T, hT⟩, hwidth⟩ := hgood
    rw [widthOut, if_pos hwidth,
      pairMap_blockFun_eq_runOut ((hann w).1 ⟨⟨T, hT⟩, hwidth⟩) hT hwidth]
  · have hnil : pairBlocks (ann w) = [] := (hann w).2 hgood
    rw [pairMap, hnil]
    simp only [List.map_nil, List.flatten_nil]
    by_cases hwidth : WidthLe M w K
    · have hhalt : ¬ ∃ T, cfgAt M w T = some Cfg.halt := fun h => hgood ⟨h, hwidth⟩
      rw [widthOut, if_pos hwidth, runOut, dif_neg hhalt]
    · rw [widthOut, if_neg hwidth]

end TwoWay

end Transducers
