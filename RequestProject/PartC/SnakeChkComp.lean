/-
**Completeness of the checking automaton of stage 1 of the induction step of the
book's snake lemma.**

Every good input carries an annotation that the checking automaton accepts: the
one built from the record-breaker decomposition of its run, whose existence is
the mathematical half of the book's first stage
(`RequestProject/PartC/SnakeData.lean`).
-/
import RequestProject.PartC.SnakeChkEnc
import RequestProject.PartC.SnakeChkRel
import RequestProject.PartC.SnakeData

namespace Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q S : Type}

/-- **The checking automaton is complete**: every good input has an annotation
that the checking automaton accepts. -/
theorem chk_complete [Finite A] [Finite B] [Finite Q] [Inhabited S]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop)
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    {w : List A} (hgood : GoodInput M K w) :
    ∃ u ∈ ChkLang M K stp ini acc, u.map lt = w := by
  sorry

end Chk

end TwoWay

end Transducers
