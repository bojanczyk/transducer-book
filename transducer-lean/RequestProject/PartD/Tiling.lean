/-
Part D, Section *A functional programming language*: the tiling problem used in the proof of
Theorem `thm:undecidability-higher-order`.

The book states the problem inside the proof of Theorem `thm:undecidability-higher-order`, as

* a finite set of tiles `T`;
* two tiles `s, t ∈ T`, for two opposing corners;
* a local constraint `C ⊆ T⁴`;

a *solution* being a function `{0,…,n} × {0,…,n} → T`, for some `n`, which satisfies the conditions
of a picture that the text of the book refers to but that is not reproduced in the sources
available here.  The conditions are therefore taken from the author's own proof of Lemma
`lem:tiling-checker`, which says exactly what has to be checked:

> We first check that the corners use the correct tiles, by applying `f` to the pairs `(0,0)` and
> `(n,n)`.  Next … we compute a list that stores all pairs in `{0,…,n-1} × {0,…,n-1}`.  Using
> incrementation, we can convert the above list into a list of all `2 × 2` windows in the square
> grid.  Then … we can filter the list so that it only contains windows which are inconsistent with
> the local constraint, and finally we can answer whether the resulting list is empty.

So a solution is a function `f` on the square `{0,…,n}²` with `f(0,0) = s`, `f(n,n) = t`, and
`(f(i,j), f(i+1,j), f(i,j+1), f(i+1,j+1)) ∈ C` for all `i, j < n`; the order of the four tiles of a
window is fixed here to be that one, which is a choice of presentation of `C` and no restriction.

Two further decisions, both recorded in `THEOREMS.md`:

* **The tiles.**  An instance is a piece of data that an algorithm reads, so the finite set of
  tiles is presented concretely, as the set `{0,…,maxTile}` of natural numbers.  Every finite
  nonempty set of tiles is of this form after renaming, and a tiling problem with no tiles at all
  has no instances worth considering.
* **Where the solution is defined.**  A solution is a function `ℕ → ℕ → ℕ`, of which only the
  values on the square `{0,…,n}²` are constrained.  This is the same notion as a function defined
  on the square alone -- it is how the book itself views a solution in Lemma `lem:tiling-checker`,
  where the second argument of the term is "the extension of the solution to the infinite
  quadrant".
-/
import Mathlib

namespace Transducers
namespace Tiling

/-- **An instance of the tiling problem** (inside the proof of Theorem
`thm:undecidability-higher-order`): a finite set of tiles, here the set `{0,…,maxTile}`, two tiles
`s` and `t` for two opposing corners, and a local constraint, here the list of the quadruples of
tiles that a `2 × 2` window is allowed to carry. -/
structure Instance where
  /-- The tiles are the natural numbers `0, …, maxTile`. -/
  maxTile : ℕ
  /-- The tile of the corner `(0,0)`. -/
  s : ℕ
  /-- The tile of the corner `(n,n)`. -/
  t : ℕ
  /-- The local constraint: the allowed `2 × 2` windows, each listed as the quadruple
  `(f(i,j), f(i+1,j), f(i,j+1), f(i+1,j+1))`. -/
  constraint : List (ℕ × ℕ × ℕ × ℕ)
  deriving DecidableEq

/-- An instance is *well formed* if the two corner tiles and all the tiles occurring in the local
constraint are tiles of the instance. -/
structure Instance.WF (I : Instance) : Prop where
  s_le : I.s ≤ I.maxTile
  t_le : I.t ≤ I.maxTile
  constraint_le : ∀ c ∈ I.constraint,
    c.1 ≤ I.maxTile ∧ c.2.1 ≤ I.maxTile ∧ c.2.2.1 ≤ I.maxTile ∧ c.2.2.2 ≤ I.maxTile

/-- The instances of the tiling problem, as a piece of data that an algorithm can read. -/
def Instance.equivProd : Instance ≃ ℕ × ℕ × ℕ × List (ℕ × ℕ × ℕ × ℕ) where
  toFun I := (I.maxTile, I.s, I.t, I.constraint)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv I := by cases I; rfl
  right_inv p := by rfl

instance : Primcodable Instance := Primcodable.ofEquiv _ Instance.equivProd

/-- **A solution of size `n`** of an instance of the tiling problem: a tiling of the square
`{0,…,n}²` whose two opposing corners carry the tiles `s` and `t` and all of whose `2 × 2` windows
satisfy the local constraint. -/
structure IsSolution (I : Instance) (n : ℕ) (f : ℕ → ℕ → ℕ) : Prop where
  /-- Every cell of the square carries a tile of the instance. -/
  tile : ∀ i ≤ n, ∀ j ≤ n, f i j ≤ I.maxTile
  /-- The corner `(0,0)` carries the tile `s`. -/
  corner_s : f 0 0 = I.s
  /-- The opposing corner `(n,n)` carries the tile `t`. -/
  corner_t : f n n = I.t
  /-- Every `2 × 2` window satisfies the local constraint. -/
  window : ∀ i < n, ∀ j < n,
    (f i j, f (i + 1) j, f i (j + 1), f (i + 1) (j + 1)) ∈ I.constraint

/-- **The tiling problem**: does the instance have a solution? -/
def Solvable (I : Instance) : Prop := ∃ n f, IsSolution I n f

end Tiling
end Transducers
