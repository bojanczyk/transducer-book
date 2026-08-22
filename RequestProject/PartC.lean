/-
Part C: Regular functions, from *Transducers* (M. Bojańczyk).

This file collects the contents of the directory `RequestProject/PartC`: the
numbered results of Sections C.1-C.3 (`Statements.lean`) and those of
Section C.4 on monadic second-order logic (`MSO.lean`), together with the
combinatorics of the runs of two-way transducers that the induction of the
book's snake lemma rests on (`SnakeRec.lean`, `SnakeLoop.lean`,
`SnakeConfine.lean`, `SnakeMirror.lean`).
-/
import RequestProject.PartC.Statements
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
import RequestProject.PartC.MSO
import RequestProject.PartC.SSTRegular
import RequestProject.PartC.SSTTwoWay
