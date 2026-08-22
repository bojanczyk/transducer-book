/-
The book's snake lemma ("the output of a snake graph is regular") and the
reduction of the hard half of Theorem C.2.9 (`two-way ⊆ regular`) to it.

The lemma is proved in the book by induction on the width `k` of the snake.
The two base cases, `k = 0` and `k = 1`, are proved in
`RequestProject/PartC/SnakeBase.lean`; the induction step, from `k + 1` to
`k + 2`, is `boundedWidth_isRegular_step`, which is **still open**.  Everything
that the book's proof of the induction step rests on is available:

* the closure properties of regular functions, Lemma C.2.10
  (`Transducers.regular_closure_properties`) and Claim C.2.11
  (`Transducers.sum_of_regular`), are proved in
  `RequestProject/PartC/RegClosure.lean` and `RequestProject/PartC/RegSum.lean`;
* the combinatorics of the induction step -- the decomposition of a run of
  width at most `k` into the loop parts and the progress parts of the
  record-breaking columns, and the resulting splitting of a halting run into
  finitely many consecutive pieces of width at most `k - 1` whose outputs
  concatenate to the output of the run -- is proved in
  `RequestProject/PartC/SnakeWalk.lean`, `RequestProject/PartC/SnakeRec.lean`
  and `RequestProject/PartC/SnakeLoop.lean`
  (`TwoWay.run_splitsInto_pred`, `TwoWay.runOutput_splits`);
* the *confinement* of those pieces to two consecutive blocks of the input --
  the book's "the loop and the progress parts of the `i`-th record-breaker are
  contained in `wᵢ₋₁ # wᵢ`", which is what makes the rational function that
  produces one copy of the input per piece have linear growth -- is proved in
  `RequestProject/PartC/SnakeConfine.lean` (`Walk.loop_confined`,
  `Walk.progress_confined`);
* the book's "without loss of generality the source column is before the target
  column, otherwise reverse the snake" is available as the *mirroring* of a
  two-way transducer, in `RequestProject/PartC/SnakeMirror.lean`
  (`TwoWay.mirror`, `TwoWay.reaches_mirror_iff`): swapping the two neighbouring
  letters in the transition function and swapping the two directions turns every
  run into the mirrored run on the reversed input, with the same output.

What is missing is the machine-theoretic half of the induction step: the
presentation of each piece of the run as the value, on a factor of the input cut
out by a rational function, of the width-`(k-1)` output function of a snake
*with an arbitrary source and target vertex*, and the gluing of the pieces with
the map combinator of Lemma C.2.10.  Carrying this out needs a version of
`TwoWay.widthOut` in which the source and the target of the run are marked in
the input, since the pieces of a run start and end in the middle of it; the
present formulation, with the run started in the initial configuration, is only
the case that the reduction below uses.
-/
import RequestProject.PartC.SnakeBase
import RequestProject.PartC.SnakeLoop

namespace Transducers

open TwoWay in
/-- **The induction step of the snake lemma**, the only remaining gap in
Theorem C.2.9: if the output of every snake of width at most `k + 1` is regular,
then so is the output of every snake of width at most `k + 2`.

It is stated here in the unconditional form "the width-`(k+2)` output function
of a two-way transducer is regular", because the induction hypothesis is over
*all* two-way transducers over *all* finite input alphabets, which is how the
book quantifies over all snake graphs of a given width.

The book's proof splits a run of width at most `k + 2` into the loop parts and
the progress parts of its record-breaking columns, all of which have width at
most `k + 1` (`TwoWay.run_splitsInto_pred`), computes the outputs of the parts
by the induction hypothesis, and glues them with the three closure properties
of Lemma C.2.10. -/
theorem boundedWidth_isRegular_step {A B Q : Type} [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) (k : ℕ) : IsRegularFun (widthOut M (k + 2)) := by
  sorry

open TwoWay in
/-- **The snake lemma** (the book's Lemma "the output of a snake graph is
regular", the missing ingredient of the hard half of Theorem C.2.9).  For every
two-way transducer `M` and every bound `k`, the function that outputs the run of
`M` on the inputs whose run has width at most `k`, and the empty string on all
other inputs, is regular.

The base cases `k = 0` and `k = 1` are proved in
`RequestProject/PartC/SnakeBase.lean`; the induction step is
`boundedWidth_isRegular_step`, which is still open. -/
theorem boundedWidth_isRegular {A B Q : Type} [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) (k : ℕ) : IsRegularFun (widthOut M k) := by
  match k with
  | 0 => exact widthOut_zero_isRegular M
  | 1 => exact widthOut_one_isRegular M
  | (k + 2) => exact boundedWidth_isRegular_step M k

open TwoWay in
/-- Every function computed by a two-way transducer is regular, *provided* the
snake lemma `boundedWidth_isRegular` holds: a halting run has width at most the
number of states, so the function computed by `M` is its own width-`|Q|` output
function. -/
theorem isRegularFun_of_isTwoWay {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsTwoWay f) : IsRegularFun f := by
  obtain ⟨Q, hQ, M, hM⟩ := hf
  haveI := hQ
  have hfe : f = widthOut M (Nat.card Q) := by
    funext w
    obtain ⟨T, hT, -⟩ := exists_halt_time M w (hM w)
    rw [widthOut, if_pos (widthLe_card M w hT), runOut_eq M w (hM w)]
  rw [hfe]
  exact boundedWidth_isRegular M _

end Transducers
