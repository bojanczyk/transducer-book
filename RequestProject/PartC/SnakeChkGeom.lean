/-
**Soundness of the checking automaton of stage 1 of the induction step of the
book's snake lemma.**

An annotation accepted by the checking automaton
(`Transducers.TwoWay.Chk.ChkLang`) describes a chain of pieces of the run of `M`
on the annotated input.  This file reads that chain off the annotation and
concludes that the neighbouring-block map combinator applied to the block
function reproduces the output of the run.
-/
import RequestProject.PartC.SnakeChkEnc
import RequestProject.PartC.SnakeChkSplit
import RequestProject.PartC.SnakeChkRel
import RequestProject.PartC.SnakeAssemble

namespace Transducers

namespace TwoWay

namespace Chk

open RegPair BlockIdx

variable {A B Q S : Type}

/-- **The checking automaton is sound**: an accepted annotation of a good input
describes a chain of pieces whose outputs concatenate to the output of the
run, so the neighbouring-block map combinator applied to the block function
computes the output of the run on it. -/
theorem chk_sound [Finite A] [Finite B] [Finite Q] [Inhabited S]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop)
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    {u : List (Gam A Q S K)} (hu : u ∈ ChkLang M K stp ini acc)
    (hgood : GoodInput M K (u.map lt)) :
    pairMap (blockFun M (K - 1) (2 * K + 1)) (homOf (snakeOutLet K) u)
      = runOut M (u.map lt) := by
  sorry

end Chk

end TwoWay

end Transducers
