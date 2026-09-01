/-
Part C: Regular functions, from *Transducers* (M. Bojańczyk).

This file collects the contents of the directory `RequestProject/PartC`: the numbered results of
Sections *The prime regular functions* to *Streaming string transducers* (`Statements.lean`) and
those of Section *Logic* on monadic second-order logic (`MSO.lean`), together with the combinatorics
of the runs of two-way transducers that the induction of the book's snake lemma rests on
(`SnakeRec.lean`, `SnakeLoop.lean`, `SnakeConfine.lean`, `SnakeMirror.lean`) and the book's
alphabet of snake letters, over which the snake lemma is stated (`SnakeAlph.lean` and the other
`SnakeAlph*.lean` files).  It also collects `RegBoundGap.lean`, which states the one construction
that is missing for the last effectivity hypothesis of Theorem
`thm:decidable-equivalence-regular` and proves that it would suffice. -/
import RequestProject.PartC.Statements
import RequestProject.PartC.RegBoundGap
import RequestProject.PartC.SnakeLoop
import RequestProject.PartC.SnakeConfine
import RequestProject.PartC.SnakeMirror
import RequestProject.PartC.SnakeLocal
import RequestProject.PartC.SnakePiece
import RequestProject.PartC.SnakePieceRev
import RequestProject.PartC.TwoWayOrder
import RequestProject.PartC.TwoWayAnnotOrd
import RequestProject.PartC.RatBi
import RequestProject.PartC.RegPair
import RequestProject.PartC.SnakeReg
import RequestProject.PartC.SnakeAlphReg
import RequestProject.PartC.MSO
import RequestProject.PartC.SSTRegular
import RequestProject.PartC.SSTTwoWay
import RequestProject.PartC.MSOWeak
import RequestProject.PartC.MultiDFA
