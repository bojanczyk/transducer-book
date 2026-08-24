/-! ## The block function computes the decomposition -/

/-- The output of the `r`-th piece of the `i`-th block of the record-breaker
decomposition of a run of width at most `K`: for `r = 2j` and `r = 2j+1` the two
halves of the `j`-th excursion of the loop part, and for `r = 2K` the progress
part. -/
noncomputable def pieceOutput (M : TwoWay A B Q) (w : List A) (K i r : ℕ) : List B :=
  if r = 2 * K then outRange M w (rbLast M w i) (progEnd M w i)
  else if r % 2 = 0 then outRange M w (excT M w i (r / 2)) (excS M w i (r / 2))
  else outRange M w (excS M w i (r / 2)) (excT M w i (r / 2 + 1))

/-- Grouping a concatenation over `2n` indices into pairs. -/
lemma flatMap_range_two_mul {C : Type} (g : ℕ → List C) :
    ∀ n : ℕ, (List.range (2 * n)).flatMap g
      = (List.range n).flatMap (fun j => g (2 * j) ++ g (2 * j + 1)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
      rw [h1, List.range_succ, List.range_succ, List.flatMap_append, List.range_succ,
        List.flatMap_append, List.flatMap_append, ih]
      simp [List.append_assoc]

/-- **The concatenation of the outputs of the `2K+1` pieces of a block is the
output of the block.** -/
lemma flatMap_pieceOutput (M : TwoWay A B Q) (w : List A) (K i : ℕ) :
    (List.range (2 * K + 1)).flatMap (pieceOutput M w K i) = blockOut M w K i := by
  rw [List.range_succ, List.flatMap_append,
    flatMap_range_two_mul (pieceOutput M w K i) K, blockOut, loopOut]
  have hloop : (List.range K).flatMap
        (fun j => pieceOutput M w K i (2 * j) ++ pieceOutput M w K i (2 * j + 1))
      = (List.range K).flatMap (fun j => outRange M w (excT M w i j) (excS M w i j) ++
          outRange M w (excS M w i j) (excT M w i (j + 1))) := by
    refine List.flatMap_congr ?_
    intro j hj
    have hjK : j < K := List.mem_range.1 hj
    have h1 : pieceOutput M w K i (2 * j)
        = outRange M w (excT M w i j) (excS M w i j) := by
      rw [pieceOutput, if_neg (by omega : ¬ 2 * j = 2 * K),
        if_pos (by omega : 2 * j % 2 = 0)]
      congr 2 <;> omega
    have h2 : pieceOutput M w K i (2 * j + 1)
        = outRange M w (excS M w i j) (excT M w i (j + 1)) := by
      rw [pieceOutput, if_neg (by omega : ¬ 2 * j + 1 = 2 * K),
        if_neg (by omega : ¬ (2 * j + 1) % 2 = 0)]
      congr 2 <;> omega
    rw [h1, h2]
  rw [hloop]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [pieceOutput, if_pos rfl]

/-- **The annotation is a correct marking** of the record-breaker decomposition
of the run of `M` on `w`: the neighbouring pairs of blocks of `u` are as many as
the record-breaking columns, and in the `i`-th of them each of the `2K+1` piece
slots computes the corresponding piece of the decomposition. -/
def IsSnakeMarking (M : TwoWay A B Q) (K : ℕ) (w : List A)
    (u : List (Option (SnakeLet A Q (2 * K + 1)))) : Prop :=
  (pairBlocks u).length = rbN M w + 1 ∧
    ∀ (i : ℕ) (z : List (Option (SnakeLet A Q (2 * K + 1)))), (pairBlocks u)[i]? = some z →
      ∀ r < 2 * K + 1, pieceOut M (K - 1) (paramOf r z) (extractWin r z)
        = pieceOutput M w K i r

/-- **The neighbouring-block map combinator applied to the block function
computes the output of the run**, on a correctly marked annotation of a halting
input of width at most `K`. -/
theorem pairMap_blockFun_eq_runOut {M : TwoWay A B Q} {K : ℕ} {w : List A}
    {u : List (Option (SnakeLet A Q (2 * K + 1)))} (hu : IsSnakeMarking M K w u)
    {T : ℕ} (hT : cfgAt M w T = some Cfg.halt) (hwidth : WidthLe M w K) :
    pairMap (blockFun M (K - 1) (2 * K + 1)) u = runOut M w := by
  have hmap : (pairBlocks u).map (blockFun M (K - 1) (2 * K + 1))
      = (List.range (rbN M w + 1)).map (blockOut M w K) := by
    refine List.ext_getElem (by simp [hu.1]) ?_
    intro i h1 h2
    have h1' : i < (pairBlocks u).length := by simpa using h1
    have hz : (pairBlocks u)[i]? = some ((pairBlocks u)[i]'h1') :=
      List.getElem?_eq_getElem h1'
    have hb := hu.2 i _ hz
    have hkey : blockFun M (K - 1) (2 * K + 1) ((pairBlocks u)[i]'h1')
        = blockOut M w K i := by
      rw [blockFun, ← flatMap_pieceOutput M w K i]
      refine List.flatMap_congr ?_
      intro r hr
      exact hb r (List.mem_range.1 hr)
    rw [List.getElem_map, List.getElem_map, List.getElem_range, hkey]
  rw [pairMap, hmap, ← List.flatMap_def, runOut_eq_partsOut hT hwidth]

end TwoWay

end Transducers
