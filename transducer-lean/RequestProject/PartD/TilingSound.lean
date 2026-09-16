/-
Part D, Section *A functional programming language*: a solution of the tiling problem describes an
accepting computation.

This is the first half of the reduction proving Lemma `lem:tiling`.  A solution of the instance
`Transducers.TilingRed.inst M w` is read as a computation of the machine `M` on the input `w`: the
rows of the grid are the successive configurations, the first one is the starting configuration --
which the counter carried by the cells of the first row forces -- and the last row but one contains
the accepting state, which the flag `acc` propagated along the rows records.

The argument is in two steps.  A solution is first turned into a *grid of cells*
(`Transducers.TilingRed.GridOk`): the codes it writes are codes of cells of the machine, and the
conditions of the local constraint hold of them.  Everything after that speaks about the cells
only.
-/
import RequestProject.PartD.TilingRows

namespace Transducers
namespace TilingRed

open PCP

/-- The cell whose code the grid writes at a position. -/
def cellAt (f : ℕ → ℕ → ℕ) (i j : ℕ) : Cell := (Encodable.decode (f i j)).getD default

/-- **A grid of cells**: what a solution of the instance `Transducers.TilingRed.inst M w`
amounts to.  The grid has `N + 1` rows and `N + 1` columns; its cells are cells of the machine,
horizontally and vertically adjacent cells satisfy the conditions of the local constraint, and the
two corners carry the two corner tiles. -/
structure GridOk (M : TM) (w : List ℕ) (N : ℕ) (c : ℕ → ℕ → Cell) : Prop where
  /-- Every cell of the grid is a cell of the machine. -/
  valid : ∀ i ≤ N, ∀ j ≤ N, validB M w (c i j) = true
  /-- Horizontally adjacent cells satisfy the horizontal conditions. -/
  horiz : ∀ i < N, ∀ j ≤ N, horizB M w (c i j) (c (i + 1) j) = true
  /-- Vertically adjacent cells satisfy the vertical conditions. -/
  vert : ∀ i ≤ N, ∀ j < N, vertB (c i j) (c i (j + 1)) = true
  /-- The corner `(0,0)` carries the starting tile. -/
  start : c 0 0 = startTile M
  /-- The corner `(N,N)` carries the final tile. -/
  final : c N N = finalTile

section Decode
variable {M : TM} {w : List ℕ} {N : ℕ} {f : ℕ → ℕ → ℕ}

/-- Each `2 × 2` window of a solution is a window of four cells of the machine. -/
lemma window_spec (hsol : Tiling.IsSolution (inst M w) N f) {i j : ℕ}
    (hi : i < N) (hj : j < N) :
    Encodable.encode (cellAt f i j) = f i j ∧
    Encodable.encode (cellAt f (i + 1) j) = f (i + 1) j ∧
    Encodable.encode (cellAt f i (j + 1)) = f i (j + 1) ∧
    Encodable.encode (cellAt f (i + 1) (j + 1)) = f (i + 1) (j + 1) ∧
    windowB M w (cellAt f i j) (cellAt f (i + 1) j) (cellAt f i (j + 1))
      (cellAt f (i + 1) (j + 1)) = true := by
  have hmem := hsol.window i hi j hj
  simp only [inst, List.mem_flatMap, List.mem_map, List.mem_filter, Prod.mk.injEq] at hmem
  obtain ⟨a, -, b, -, c, -, d, ⟨-, hwin⟩, h1, h2, h3, h4⟩ := hmem
  have ea : cellAt f i j = a := by rw [cellAt, ← h1]; simp
  have eb : cellAt f (i + 1) j = b := by rw [cellAt, ← h2]; simp
  have ec : cellAt f i (j + 1) = c := by rw [cellAt, ← h3]; simp
  have ed : cellAt f (i + 1) (j + 1) = d := by rw [cellAt, ← h4]; simp
  rw [ea, eb, ec, ed]
  exact ⟨h1, h2, h3, h4, hwin⟩

/-- Every cell of a solution is a cell of the machine. -/
lemma valid_cell (hsol : Tiling.IsSolution (inst M w) N f) (hN : 1 ≤ N) {i j : ℕ}
    (hi : i ≤ N) (hj : j ≤ N) : validB M w (cellAt f i j) = true := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases eq_or_lt_of_le hi with rfl | hi' <;> rcases eq_or_lt_of_le hj with rfl | hj'
  · exact windowB_valid₄ (window_spec hsol (i := m) (j := m) (by omega) (by omega)).2.2.2.2
  · exact windowB_valid₂ (window_spec hsol (i := m) (j := j) (by omega) hj').2.2.2.2
  · exact windowB_valid₃ (window_spec hsol (i := i) (j := m) hi' (by omega)).2.2.2.2
  · exact windowB_valid₁ (window_spec hsol hi' hj').2.2.2.2

/-- Every cell of a solution is the cell whose code the grid writes. -/
lemma encode_cell (hsol : Tiling.IsSolution (inst M w) N f) (hN : 1 ≤ N) {i j : ℕ}
    (hi : i ≤ N) (hj : j ≤ N) : Encodable.encode (cellAt f i j) = f i j := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases eq_or_lt_of_le hi with rfl | hi' <;> rcases eq_or_lt_of_le hj with rfl | hj'
  · exact (window_spec hsol (i := m) (j := m) (by omega) (by omega)).2.2.2.1
  · exact (window_spec hsol (i := m) (j := j) (by omega) hj').2.1
  · exact (window_spec hsol (i := i) (j := m) hi' (by omega)).2.2.1
  · exact (window_spec hsol hi' hj').1

/-- Two horizontally adjacent cells of a solution satisfy the horizontal conditions. -/
lemma horiz_cell (hsol : Tiling.IsSolution (inst M w) N f) (hN : 1 ≤ N) {i j : ℕ}
    (hi : i < N) (hj : j ≤ N) : horizB M w (cellAt f i j) (cellAt f (i + 1) j) = true := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases eq_or_lt_of_le hj with rfl | hj'
  · exact windowB_horiz₂ (window_spec hsol (i := i) (j := m) (by omega) (by omega)).2.2.2.2
  · exact windowB_horiz₁ (window_spec hsol hi hj').2.2.2.2

/-- Two vertically adjacent cells of a solution satisfy the vertical conditions. -/
lemma vert_cell (hsol : Tiling.IsSolution (inst M w) N f) (hN : 1 ≤ N) {i j : ℕ}
    (hi : i ≤ N) (hj : j < N) : vertB (cellAt f i j) (cellAt f i (j + 1)) = true := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rcases eq_or_lt_of_le hi with rfl | hi'
  · exact windowB_vert₂ (window_spec hsol (i := m) (j := j) (by omega) hj).2.2.2.2
  · exact windowB_vert₁ (window_spec hsol hi' hj).2.2.2.2

lemma startTile_ne_finalTile : startTile M ≠ finalTile := by
  intro h
  have := congrArg Cell.top h
  simp [startTile, finalTile] at this

/-- A solution has at least two rows: the two corner tiles are distinct. -/
lemma one_le_size (hsol : Tiling.IsSolution (inst M w) N f) : 1 ≤ N := by
  by_contra hN
  have hN0 : N = 0 := by omega
  subst hN0
  have h1 := hsol.corner_s
  have h2 := hsol.corner_t
  have : Encodable.encode (startTile M) = Encodable.encode (finalTile) := by
    rw [← show (inst M w).s = Encodable.encode (startTile M) from rfl,
      ← show (inst M w).t = Encodable.encode (finalTile) from rfl, ← h1, ← h2]
  exact startTile_ne_finalTile (Encodable.encode_injective this)

/-- **A solution of the instance is a grid of cells.** -/
lemma gridOk_of_isSolution (hsol : Tiling.IsSolution (inst M w) N f) :
    GridOk M w N (cellAt f) := by
  have hN : 1 ≤ N := one_le_size hsol
  refine ⟨fun i hi j hj => valid_cell hsol hN hi hj, fun i hi j hj => horiz_cell hsol hN hi hj,
    fun i hi j hj => vert_cell hsol hN hi hj, ?_, ?_⟩
  · refine Encodable.encode_injective ?_
    rw [encode_cell hsol hN (by omega) (by omega), hsol.corner_s]
    rfl
  · refine Encodable.encode_injective ?_
    rw [encode_cell hsol hN (by omega) (by omega), hsol.corner_t]
    rfl

end Decode

/-! ## The geometry of a grid of cells -/

section Grid
variable {M : TM} {w : List ℕ} {N : ℕ} {c : ℕ → ℕ → Cell}

lemma lb_first (hg : GridOk M w N c) : ∀ j ≤ N, (c 0 j).lb = true := by
  intro j
  induction j with
  | zero => intro _; rw [hg.start]; rfl
  | succ j ih =>
      intro hj
      rw [← vertB_lb (hg.vert 0 (by omega) j (by omega))]
      exact ih (by omega)

lemma rb_last (hg : GridOk M w N c) : ∀ j ≤ N, (c N j).rb = true := by
  have key : ∀ d j, j + d = N → (c N j).rb = true := by
    intro d
    induction d with
    | zero => intro j hj; rw [show j = N by omega, hg.final]; rfl
    | succ d ih =>
        intro j hj
        rw [vertB_rb (hg.vert N le_rfl j (by omega))]
        exact ih (j + 1) (by omega)
  intro j hj
  exact key (N - j) j (by omega)

lemma top_first (hg : GridOk M w N c) : ∀ i ≤ N, (c i 0).top = true := by
  intro i
  induction i with
  | zero => intro _; rw [hg.start]; rfl
  | succ i ih =>
      intro hi
      rw [← horizB_top (hg.horiz i (by omega) 0 (by omega))]
      exact ih (by omega)

lemma not_fin (hg : GridOk M w N c) {i j : ℕ} (hi : i ≤ N) (hj : j < N) : (c i j).fin = false :=
  vertB_notfin (hg.vert i hi j hj)

/-! ## The first row is the starting configuration -/

lemma cnt_first (hg : GridOk M w N c) : ∀ i ≤ N, (c i 0).cnt = min i (w.length + 1) := by
  intro i
  induction i with
  | zero => intro _; rw [hg.start]; simp [startTile]
  | succ i ih =>
      intro hi
      rw [horizB_cnt (hg.horiz i (by omega) 0 (by omega)) (top_first hg i (by omega)),
        ih (by omega)]
      omega

lemma le_size (hg : GridOk M w N c) (hN : 1 ≤ N) : w.length + 1 ≤ N := by
  have hv : validB M w (c N 0) = true := hg.valid N le_rfl 0 (by omega)
  have ht : (c N 0).top = true := top_first hg N le_rfl
  have hr : (c N 0).rb = true := rb_last hg 0 (by omega)
  have h1 := cnt_first hg N le_rfl
  have h2 := validB_top_rb hv ht hr
  omega

lemma sym_first (hg : GridOk M w N c) : ∀ i ≤ N,
    (c i 0).sym = (if i = 0 then Sym.state M.q0 else Sym.tape (w.getD (i - 1) 0)) := by
  intro i hi
  have hv : validB M w (c i 0) = true := hg.valid i hi 0 (by omega)
  have ht := top_first hg i hi
  have hc := cnt_first hg i hi
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · obtain ⟨hk, hvv⟩ := validB_top_zero hv ht (by omega)
    simp [Cell.sym, hk, hvv]
  · have hne : (c i 0).cnt ≠ 0 := by omega
    obtain ⟨hk, hvv⟩ := validB_top_succ hv ht hne
    have hidx : (c i 0).cnt - 1 = min (i - 1) w.length := by omega
    have hgd : w[min (i - 1) w.length]?.getD 0 = w[i - 1]?.getD 0 := by
      rcases le_or_gt w.length (i - 1) with hle | hlt
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      · rw [show min (i - 1) w.length = i - 1 by omega]
    rw [if_neg (show ¬ i = 0 by omega)]
    simp [Cell.sym, hk, hvv, hidx, hgd]

/-! ## The rows of a grid are the configurations of a computation -/

/-- The cells of the row `j` of the grid. -/
def row (c : ℕ → ℕ → Cell) (N j : ℕ) : List Cell := (List.range (N + 1)).map fun i => c i j

/-- The configuration written in the row `j` of the grid. -/
def str (c : ℕ → ℕ → Cell) (N j : ℕ) : List Sym := (row c N j).map Cell.sym

@[simp] lemma row_length {j : ℕ} : (row c N j).length = N + 1 := by simp [row]

lemma row_head? {j : ℕ} : (row c N j).head? = some (c 0 j) := by
  simp [row, List.range_succ_eq_map]

lemma row_getLast? {j : ℕ} : (row c N j).getLast? = some (c N j) := by
  rw [List.getLast?_eq_getElem?]
  simp [row]

lemma mem_row {x : Cell} {j : ℕ} (hx : x ∈ row c N j) : ∃ i ≤ N, c i j = x := by
  simp only [row, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, by omega, rfl⟩

/-- Every row of the grid describes a sequence of rewritings. -/
lemma reachesR_row (hg : GridOk M w N c) {j : ℕ} (hj : j ≤ N) :
    ReachesR (M.transRules w) (str c N j) ((row c N j).map Cell.nsym) := by
  refine reachesR_of_row (row c N j) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_row hx
    exact hg.valid i hi j hj
  · rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i < N := by simp only [row_length] at hi; omega
    have e1 : (row c N j)[i] = c i j := by simp [row]
    have e2 : (row c N j)[i + 1] = c (i + 1) j := by simp [row]
    rw [e1, e2]
    exact hg.horiz i hi' j hj
  · intro x hx
    rw [row_head?, Option.mem_def, Option.some_inj] at hx
    subst hx
    exact validB_lb_role (hg.valid 0 (by omega) j hj) (lb_first hg j hj)
  · intro x hx
    rw [row_getLast?, Option.mem_def, Option.some_inj] at hx
    subst hx
    exact validB_rb_role (hg.valid N le_rfl j hj) (rb_last hg j hj)

/-- The letters announced by a row are the letters of the row below. -/
lemma row_nsym (hg : GridOk M w N c) {j : ℕ} (hj : j + 1 < N) :
    (row c N j).map Cell.nsym = str c N (j + 1) := by
  simp only [row, str, List.map_map]
  refine List.map_congr_left ?_
  intro i hi
  have hi' : i ≤ N := by simp only [List.mem_range] at hi; omega
  obtain ⟨hk, hv⟩ := vertB_content (hg.vert i hi' j (by omega)) (not_fin hg hi' hj)
  simp [Function.comp, Cell.sym, Cell.nsym, hk, hv]

/-- The rows of the grid are reached from one another. -/
lemma reachesR_str (hg : GridOk M w N c) :
    ∀ j, j < N → ReachesR (M.transRules w) (str c N 0) (str c N j) := by
  intro j
  induction j with
  | zero => intro _; exact ReachesR.refl _ _
  | succ j ih =>
      intro hj
      refine (ih (by omega)).trans ?_
      have h := reachesR_row hg (j := j) (by omega)
      rwa [row_nsym hg hj] at h

/-! ## The accepting state -/

lemma acc_witness (hg : GridOk M w N c) {j : ℕ} (hj : j ≤ N) :
    ∀ i ≤ N, (c i j).acc = true → ∃ i' ≤ i, (c i' j).k = 1 ∧ (c i' j).v = M.qacc := by
  intro i
  induction i with
  | zero =>
      intro _ hacc
      have h := validB_lb_acc (hg.valid 0 (by omega) j hj) (lb_first hg j hj)
      rw [hacc] at h
      simp at h
      exact ⟨0, le_rfl, h.1, h.2⟩
  | succ i ih =>
      intro hi hacc
      have h := horizB_acc (hg.horiz i (by omega) j hj)
      rw [hacc] at h
      rcases Bool.or_eq_true_iff.mp h.symm with h' | h'
      · obtain ⟨i', hi', hk, hv⟩ := ih (by omega) h'
        exact ⟨i', by omega, hk, hv⟩
      · simp at h'
        exact ⟨i + 1, le_rfl, h'.1, h'.2⟩

/-! ## The first row is the starting configuration, extended by blanks -/

lemma range_map_eq_startCfg (M : TM) (w : List ℕ) (N : ℕ) (h : w.length + 1 ≤ N) :
    ((List.range (N + 1)).map
        fun i => if i = 0 then Sym.state M.q0 else Sym.tape (w.getD (i - 1) 0)) =
      M.startCfg w ++ List.replicate (N - w.length) (Sym.tape 0) := by
  refine List.ext_getElem (by simp [TM.startCfg]; omega) ?_
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [List.getElem_append_left (by simp [TM.startCfg])]
    simp [TM.startCfg]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rcases lt_or_ge k w.length with hk | hk
    · rw [List.getElem_append_left (by simp [TM.startCfg]; omega)]
      simp only [TM.startCfg, List.getElem_cons_succ, List.getElem_map]
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp
    · rw [List.getElem_append_right (by simp [TM.startCfg]; omega)]
      rw [List.getD_eq_default _ _ (by omega)]
      simp

lemma str_zero (hg : GridOk M w N c) (hN : 1 ≤ N) :
    str c N 0 = M.startCfg w ++ List.replicate (N - w.length) (Sym.tape 0) := by
  have h1 : str c N 0 = (List.range (N + 1)).map
      fun i => if i = 0 then Sym.state M.q0 else Sym.tape (w.getD (i - 1) 0) := by
    simp only [str, row, List.map_map]
    refine List.map_congr_left ?_
    intro i hi
    have hi' : i ≤ N := by simp only [List.mem_range] at hi; omega
    exact sym_first hg i hi'
  rw [h1, range_map_eq_startCfg M w N (le_size hg hN)]

lemma reaches_append_blanks (M : TM) (w : List ℕ) (a : List Sym) (k : ℕ) :
    Reaches (M.machineSRS w) a (a ++ List.replicate k (Sym.tape 0)) := by
  induction k with
  | zero => simpa using Reaches.refl _ _
  | succ k ih =>
      refine ih.trans (Reaches.single ?_)
      have h : Step (M.machineSRS w) (a ++ List.replicate k (Sym.tape 0))
          ((a ++ List.replicate k (Sym.tape 0)) ++ [Sym.tape 0]) :=
        Step.ext (by simp [TM.machineSRS])
      simpa [List.append_assoc, List.replicate_succ'] using h

/-- **A grid of cells describes an accepting computation.** -/
theorem accepts_of_gridOk (hg : GridOk M w N c) (hN : 1 ≤ N) : M.Accepts w := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hfin : (c (m + 1) (m + 1)).fin = true := by rw [hg.final]; rfl
  have hrb : (c (m + 1) (m + 1)).rb = true := by rw [hg.final]; rfl
  have hacc : (c (m + 1) m).acc = true :=
    vertB_acc (hg.vert (m + 1) le_rfl m (by omega)) hfin hrb
  obtain ⟨i', hi', hk, hv⟩ := acc_witness hg (j := m) (by omega) (m + 1) le_rfl hacc
  have hmem : Sym.state M.qacc ∈ str c (m + 1) m := by
    refine List.mem_map.2 ⟨c i' m, ?_, ?_⟩
    · exact List.mem_map.2 ⟨i', List.mem_range.2 (by omega), rfl⟩
    · simp [Cell.sym, hk, hv]
  refine ⟨str c (m + 1) m, ?_, hmem⟩
  refine Reaches.trans ?_ (ReachesRule.toReaches (S := M.machineSRS w)
    (reachesR_str hg m (by omega)))
  rw [str_zero hg hN]
  exact reaches_append_blanks M w (M.startCfg w) _

end Grid

/-- **The reduction is sound.**  If the instance `Transducers.TilingRed.inst M w` has a solution,
then the machine `M` accepts the input `w`. -/
theorem accepts_of_solvable {M : TM} {w : List ℕ} (h : Tiling.Solvable (inst M w)) :
    M.Accepts w := by
  obtain ⟨N, f, hsol⟩ := h
  exact accepts_of_gridOk (gridOk_of_isSolution hsol) (one_le_size hsol)

end TilingRed
end Transducers
