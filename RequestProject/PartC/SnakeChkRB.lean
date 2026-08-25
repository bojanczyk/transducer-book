/-
**The record-breaker decomposition is a chain of pieces.**

The mathematical half of stage 1 of the induction step of the book's snake
lemma: on every good input -- a nonempty input whose run halts and has width at
most `K` -- the record-breaker decomposition of the run supplies a chain of
pieces in the sense of `Transducers.TwoWay.Chk.ChainData`.  The blocks are cut
at the record-breaking columns (`TwoWay.snakeY`), the `2K+1` piece slots of a
pair are the `2K` halves of the `K` excursions of its record-breaking column
followed by the progress part, and the confinement of the pieces to two
neighbouring blocks is the one proved in
`RequestProject/PartC/SnakeConfine.lean`.

What this adds to `TwoWay.exists_isSnakeMarking`
(`RequestProject/PartC/SnakeData.lean`) is the *chain* structure: the entry and
the exit state of every piece, the cut at which it starts and the cut at which
it ends, and the window condition
(`Transducers.TwoWay.Chk.WinCond`) of its window -- the data that the checking
automaton of stage 1 verifies.
-/
import RequestProject.PartC.SnakeChkData
import RequestProject.PartC.SnakeChkRel
import RequestProject.PartC.SnakeData

namespace Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q : Type}

/-- **Every good input carries a chain of pieces**: the record-breaker
decomposition of its run. -/
theorem nonempty_chainData_of_good [Finite A] [Finite B] [Finite Q]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) {w : List A} (hgood : GoodInput M K w) :
    Nonempty (ChainData M K w) := by
  sorry

end Chk

end TwoWay

end Transducers
