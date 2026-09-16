/-
Part D, Section *A functional programming language*: the tiles of the reduction proving Lemma
`lem:tiling`.

Lemma `lem:tiling` asks for the undecidability of the tiling problem
(`RequestProject/PartD/Tiling.lean`), and the book proves it by the classical reduction in which
the rows of the square grid are the successive configurations of a Turing machine.  The machines
used here are the tape machines of `RequestProject/PCP/TuringMachine.lean`, whose configurations
are strings (`RequestProject/PCP/Rewriting.lean`): a configuration is a word `u q v`, and one step
of the machine rewrites two or three consecutive letters of it.

A cell of the grid carries one letter of a configuration, together with the letter that will
replace it in the row below and the *rôle* the cell plays in the rewriting that takes place between
the two rows.  The rôles are what makes a `2 × 2` window enough: a window sees only two
horizontally adjacent cells, while a rule of the machine may rewrite three, so the middle cell of a
three-letter rewriting carries the new state as well, and each pair of adjacent cells checks the
part of the rule that it can see.

This file defines the cells, the conditions a window must satisfy, and the instance of the tiling
problem that a machine and an input word give rise to.  The two directions of the reduction are in
`RequestProject/PartD/TilingRows.lean` and `RequestProject/PartD/TilingGrid.lean`.
-/
import RequestProject.PartD.Tiling
import RequestProject.PCP.TuringMachine

namespace Transducers
namespace TilingRed

open PCP

/-- **A cell of the grid.**

The letter of the configuration written in the cell is `sym`, given by its kind `k` (`0` for a tape
symbol, `1` for a state) and its value `v`; `nk` and `nv` describe in the same way the letter of
the row below.  The rôle of the cell in the rewriting between the two rows is

* `0`: the letter is not rewritten;
* `1`, `2`: the two cells of a rewriting `q a ⟶ b r` (a move to the right);
* `3`, `4`, `5`: the three cells of a rewriting `c q a ⟶ r c b` (a move to the left), the middle
  one of which records the new state `r` in `aux`, so that the pair `4, 5` can check the rule.

The remaining fields mark the two border columns (`lb`, `rb`), the first and the last row (`top`,
`fin`), record whether the accepting state occurs in the row at or to the left of the cell (`acc`),
and, in the first row only, count the position of the cell (`cnt`), so that the first row can be
required to carry the starting configuration. -/
structure Cell where
  /-- The kind of the letter: `0` for a tape symbol, `1` for a state. -/
  k : ℕ
  /-- The value of the letter. -/
  v : ℕ
  /-- The kind of the letter of the cell below. -/
  nk : ℕ
  /-- The value of the letter of the cell below. -/
  nv : ℕ
  /-- The rôle of the cell in the rewriting between the two rows. -/
  role : ℕ
  /-- The new state, recorded by the middle cell of a three-letter rewriting. -/
  aux : ℕ
  /-- Is the cell in the left border column? -/
  lb : Bool
  /-- Is the cell in the right border column? -/
  rb : Bool
  /-- Is the cell in the first row? -/
  top : Bool
  /-- Is the cell in the last row? -/
  fin : Bool
  /-- Does the accepting state occur in the row, at or to the left of the cell? -/
  acc : Bool
  /-- The position of the cell, counted in the first row only. -/
  cnt : ℕ
  deriving DecidableEq, Inhabited

/-- The letter written in the cell. -/
def Cell.sym (x : Cell) : Sym := if x.k = 0 then Sym.tape x.v else Sym.state x.v

/-- The letter written in the cell below. -/
def Cell.nsym (x : Cell) : Sym := if x.nk = 0 then Sym.tape x.nv else Sym.state x.nv

/-- The cells, as a piece of data. -/
def Cell.equivProd :
    Cell ≃ (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × (Bool × Bool × Bool × Bool × Bool) where
  toFun x := ((x.k, x.v, x.nk, x.nv, x.role, x.aux, x.cnt), (x.lb, x.rb, x.top, x.fin, x.acc))
  invFun p := ⟨p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1, p.1.2.2.2.2.1, p.1.2.2.2.2.2.1,
    p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2, p.1.2.2.2.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by rfl

instance : Primcodable Cell := Primcodable.ofEquiv _ Cell.equivProd

/-! ## The conditions on a cell and on a pair of cells -/

variable (M : TM) (w : List ℕ)

/-- **The conditions on a single cell.**  The letters are letters of the machine; the kinds of the
two letters are the ones its rôle prescribes; a cell of the left border column starts a rewriting
and one of the right border column ends one; the accepting state is recorded correctly at the left
border; a cell of the first row is not rewritten and carries the letter of the starting
configuration that its counter points at, the counter of the last column being at its cap, which
forces the first row to be long enough to hold the whole input; and a cell of the last row is
blank. -/
def validB (x : Cell) : Bool :=
  decide (x.k ≤ 1) && decide (x.nk ≤ 1) && decide (x.role ≤ 5) &&
  (if x.k = 0 then decide (x.v ∈ M.tapeSyms w) else decide (x.v ∈ M.states)) &&
  (if x.nk = 0 then decide (x.nv ∈ M.tapeSyms w) else decide (x.nv ∈ M.states)) &&
  (if x.role = 4 then decide (x.aux ∈ M.states) else decide (x.aux = 0)) &&
  (if x.role = 0 then decide (x.nk = x.k ∧ x.nv = x.v)
    else if x.role = 1 then decide (x.k = 1 ∧ x.nk = 0)
    else if x.role = 2 then decide (x.k = 0 ∧ x.nk = 1)
    else if x.role = 3 then decide (x.k = 0 ∧ x.nk = 1)
    else if x.role = 4 then decide (x.k = 1 ∧ x.nk = 0)
    else decide (x.k = 0 ∧ x.nk = 0)) &&
  (!x.lb || decide (x.role = 0 ∨ x.role = 1 ∨ x.role = 3)) &&
  (!x.rb || decide (x.role = 0 ∨ x.role = 2 ∨ x.role = 5)) &&
  (!x.lb || (x.acc == decide (x.k = 1 ∧ x.v = M.qacc))) &&
  (if x.top then
      decide (x.cnt ≤ w.length + 1) && decide (x.role = 0) &&
      (if x.cnt = 0 then decide (x.k = 1 ∧ x.v = M.q0)
        else decide (x.k = 0 ∧ x.v = w.getD (x.cnt - 1) 0)) &&
      (!x.rb || decide (x.cnt = w.length + 1)) && !x.fin
    else decide (x.cnt = 0)) &&
  (!x.fin || decide (x.k = 0 ∧ x.v = 0 ∧ x.nk = 0 ∧ x.nv = 0 ∧ x.role = 0 ∧ x.aux = 0) &&
    !x.acc)

/-- **The conditions on two horizontally adjacent cells** `x` (left) and `y` (right).  Only the
first column is a left border and only the last one is a right border; the first and the last row
are rows; the counter of the first row increases, up to its cap; the accepting state is recorded;
and the rôles of the two cells fit together, the pairs that make up a rewriting checking the rule
of the machine that is being applied. -/
def horizB (x y : Cell) : Bool :=
  !y.lb && !x.rb && (x.top == y.top) && (x.fin == y.fin) &&
  (!x.top || decide (y.cnt = min (x.cnt + 1) (w.length + 1))) &&
  (y.acc == (x.acc || decide (y.k = 1 ∧ y.v = M.qacc))) &&
  (if x.role = 0 then decide (y.role = 0 ∨ y.role = 1 ∨ y.role = 3)
    else if x.role = 1 then decide (y.role = 2) &&
      decide ((x.v, y.v, y.nv, x.nv, true) ∈ M.trans)
    else if x.role = 2 then decide (y.role = 0)
    else if x.role = 3 then decide (y.role = 4) && decide (x.nv = y.aux ∧ y.nv = x.v)
    else if x.role = 4 then decide (y.role = 5) &&
      decide ((x.v, y.v, x.aux, y.nv, false) ∈ M.trans)
    else decide (y.role = 0))

/-- **The conditions on two vertically adjacent cells** `x` (above) and `y` (below).  The last row
has no row below it; the border columns and the rows are marked coherently; and the letter of the
lower cell is the one the upper cell announces -- unless the lower cell is in the last row, in
which case the row above it is required to contain the accepting state, which is what the flag
`acc` of its last cell says. -/
def vertB (x y : Cell) : Bool :=
  !x.fin && (x.lb == y.lb) && (x.rb == y.rb) && !y.top && decide (y.cnt = 0) &&
  (if y.fin then !y.rb || x.acc else decide (y.k = x.nk ∧ y.v = x.nv))

/-- **The conditions on a `2 × 2` window**, listed as in `Transducers.Tiling.IsSolution`: the four
cells are cells of the machine, the two rows of the window are horizontally coherent, and the two
columns vertically so. -/
def windowB (a b c d : Cell) : Bool :=
  validB M w a && validB M w b && validB M w c && validB M w d &&
  horizB M w a b && horizB M w c d && vertB a c && vertB b d

/-! ## The two corner tiles -/

/-- The tile of the corner `(0,0)`: the first letter of the starting configuration, which is the
starting state, in the first row and the left border column. -/
def startTile : Cell :=
  { k := 1, v := M.q0, nk := 1, nv := M.q0, role := 0, aux := 0, lb := true, rb := false,
    top := true, fin := false, acc := decide (M.q0 = M.qacc), cnt := 0 }

/-- The tile of the corner `(n,n)`: a blank cell of the last row, in the right border column. -/
def finalTile : Cell :=
  { k := 0, v := 0, nk := 0, nv := 0, role := 0, aux := 0, lb := false, rb := true,
    top := false, fin := true, acc := false, cnt := 0 }

/-! ## Enumerating the cells -/

/-- The lists of tuples with prescribed entries: `tupleList [l₀, …, lₖ]` is the list of all
`[a₀, …, aₖ]` with `aᵢ ∈ lᵢ`. -/
def tupleList : List (List ℕ) → List (List ℕ)
  | [] => [[]]
  | l :: ls => l.flatMap fun a => (tupleList ls).map fun t => a :: t

lemma nil_mem_tupleList : [] ∈ tupleList [] := by simp [tupleList]

lemma cons_mem_tupleList {a : ℕ} {as : List ℕ} {l : List ℕ} {ls : List (List ℕ)}
    (h : a ∈ l) (h' : as ∈ tupleList ls) : a :: as ∈ tupleList (l :: ls) := by
  simp only [tupleList, List.mem_flatMap]
  exact ⟨a, h, List.mem_map_of_mem h'⟩

/-- Reading a cell off a list of twelve natural numbers. -/
def cellOfList (t : List ℕ) : Cell :=
  { k := t.getD 0 0, v := t.getD 1 0, nk := t.getD 2 0, nv := t.getD 3 0, role := t.getD 4 0,
    aux := t.getD 5 0, lb := t.getD 6 0 == 1, rb := t.getD 7 0 == 1, top := t.getD 8 0 == 1,
    fin := t.getD 9 0 == 1, acc := t.getD 10 0 == 1, cnt := t.getD 11 0 }

/-- The list of entries allowed in each field of a cell. -/
def fieldLists : List (List ℕ) :=
  [[0, 1], M.tapeSyms w ++ M.states, [0, 1], M.tapeSyms w ++ M.states, List.range 6,
    0 :: M.states, [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], List.range (w.length + 2)]

/-- All the cells of the machine `M` on the input `w`. -/
def allCells : List Cell :=
  ((tupleList (fieldLists M w)).map cellOfList).filter (validB M w)

/-- The largest code of a cell of the machine. -/
def maxCode : ℕ := (allCells M w).foldr (fun x m => max (Encodable.encode x) m) 0

/-- **The instance of the tiling problem** built from a machine and an input word: its tiles are
the cells, its two corner tiles are `Transducers.TilingRed.startTile` and
`Transducers.TilingRed.finalTile`, and its local constraint is the list of the windows satisfying
`Transducers.TilingRed.windowB`. -/
def inst : Tiling.Instance where
  maxTile := maxCode M w
  s := Encodable.encode (startTile M)
  t := Encodable.encode finalTile
  constraint :=
    (allCells M w).flatMap fun a => (allCells M w).flatMap fun b =>
      (allCells M w).flatMap fun c =>
        ((allCells M w).filter (windowB M w a b c)).map fun d =>
          (Encodable.encode a, Encodable.encode b, Encodable.encode c, Encodable.encode d)

end TilingRed
end Transducers
