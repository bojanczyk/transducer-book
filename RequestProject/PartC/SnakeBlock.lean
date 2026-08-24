/-
The *block function* of the induction step of the book's snake lemma: stages
2--4 of the book's proof.

`RequestProject/PartC/SnakeParts.lean` decomposes a halting run of width at most
`K` into the pieces of the record-breaker decomposition, and
`RequestProject/PartC/SnakePieceIdent.lean` identifies each piece with the whole
run of a *window transducer* on a factor of the input.  What is left is to
compute the concatenation of the outputs of those pieces by a regular function.
The book does this with the neighbouring-block map combinator
(`Transducers.RegPair.isRegularFun_pairMap`): the input is cut at the
record-breaking columns into blocks `w₀ # w₁ # ⋯ # wₙ`, the combinator presents
each pair `wᵢ₋₁ # wᵢ` of neighbouring blocks separately, and the pieces of the
`i`-th record-breaker -- which all live inside that pair -- are computed there.

This file supplies the function that is applied to one pair of neighbouring
blocks.  Its input is a pair of blocks of the *annotated* input: every letter
carries, for each of the `2K+1` piece slots of a block, a bit saying whether the
letter belongs to the window of that piece, and the parameters of the window
transducer of that piece.  The function

* cuts out the window of the piece with a homomorphism (`TwoWay.extractWin`),
* reads the parameters off the first annotated letter of the block
  (`TwoWay.paramOf`), and
* applies the width-`(K-1)` output function of the window transducer, which is
  regular by the induction hypothesis of the snake lemma.

The two results are `TwoWay.isRegularFun_blockFun` -- the block function is
regular -- and `TwoWay.pairMap_blockFun_eq_widthOut` -- if the annotation is
correct (`TwoWay.IsSnakeMarking`) then the neighbouring-block map combinator
applied to the block function computes the width-`K` output function.

What is *not* in this file is the book's stage 1, the rational function that
produces the annotation; see `RequestProject/PartC/SnakeReg.lean`.
-/
import RequestProject.PartC.SnakePieceIdent
import RequestProject.PartC.SnakeRegTools
import RequestProject.PartC.RegAut

namespace Transducers

namespace TwoWay

open RegPair

variable {A B Q : Type}

/-! ## The parameters of a piece -/

/-- The parameters of one piece of the record-breaker decomposition: the kind of
window transducer that computes it (`1` forward, `2` mirrored, `3` the last
piece forward, `4` the last piece mirrored, anything else the empty piece), the
two letters adjacent to its window, and the state in which the piece starts
together with the state in which it ends. -/
abbrev PieceParam (A Q : Type) := Fin 5 × Option A × Option A × Option (Q × Q)

/-- The output of a piece with the given parameters, on the given window. -/
noncomputable def pieceOut (M : TwoWay A B Q) (k : ℕ) (p : PieceParam A Q) (v : List A) :
    List B :=
  match p.2.2.2 with
  | none => []
  | some (q, f) =>
      if p.1 = 1 then widthOut (stopRight M p.2.1 p.2.2.1 q f) k v
      else if p.1 = 2 then widthOut (stopRight (mirror M) p.2.2.1 p.2.1 q f) k v.reverse
      else if p.1 = 3 then widthOut (M.withContext p.2.1 none q) k v
      else if p.1 = 4 then widthOut ((mirror M).withContext p.2.1 none q) k v.reverse
      else []

/-! ## The annotated alphabet -/

/-- A letter of the annotated input: the letter itself together with, for each
of the `R` piece slots of a block, the bit saying whether the letter belongs to
the window of that piece and the parameters of that piece. -/
abbrev SnakeLet (A Q : Type) (R : ℕ) := A × (Fin R → Bool × PieceParam A Q)

variable {R : ℕ}

/-- Does the annotated letter belong to the window of the `r`-th piece? -/
def inWin (r : ℕ) (c : SnakeLet A Q R) : Bool :=
  if h : r < R then (c.2 ⟨r, h⟩).1 else false

/-- The parameters of the `r`-th piece carried by an annotated letter. -/
def parAt (r : ℕ) (c : SnakeLet A Q R) : PieceParam A Q :=
  if h : r < R then (c.2 ⟨r, h⟩).2 else default

/-- The window of the `r`-th piece, cut out of an annotated block by a
homomorphism. -/
def extractWin (r : ℕ) : List (Option (SnakeLet A Q R)) → List A :=
  homOf (fun c => match c with
    | none => []
    | some g => if inWin r g then [g.1] else [])

/-- The first annotated letter of a block. -/
def firstLet (z : List (Option (SnakeLet A Q R))) : Option (SnakeLet A Q R) :=
  (z.filterMap id).head?

/-- The parameters of the `r`-th piece of a block, read off its first annotated
letter. -/
def paramOf (r : ℕ) (z : List (Option (SnakeLet A Q R))) : PieceParam A Q :=
  match firstLet z with
  | none => default
  | some c => parAt r c

/-- **The block function**: the concatenation of the outputs of the `R` pieces
of one pair of neighbouring blocks. -/
noncomputable def blockFun (M : TwoWay A B Q) (k R : ℕ)
    (z : List (Option (SnakeLet A Q R))) : List B :=
  (List.range R).flatMap (fun r => pieceOut M k (paramOf r z) (extractWin r z))

/-! ## The block function is regular -/

section Regular

variable [Finite A] [Finite B] [Finite Q]

/-- The window of a piece is cut out by a homomorphism, hence rationally. -/
lemma isRegularFun_extractWin (r : ℕ) :
    IsRegularFun (extractWin r : List (Option (SnakeLet A Q R)) → List A) :=
  isRegularFun_homOf _

/-- The state reached by the automaton that remembers the first annotated letter
of a block. -/
private def flStep (s : Option (Option (SnakeLet A Q R))) (x : Option (SnakeLet A Q R)) :
    Option (Option (SnakeLet A Q R)) :=
  match s with
  | some _ => s
  | none => match x with
    | none => none
    | some g => some (some g)

private lemma flStep_eval (z : List (Option (SnakeLet A Q R))) :
    (z.foldl flStep none).join = firstLet z := by
  induction z with
  | nil => rfl
  | cons x z ih =>
      rcases x with _ | g
      · simpa [flStep, firstLet] using ih
      · have habs : ∀ (z : List (Option (SnakeLet A Q R))) (v : Option (SnakeLet A Q R)),
            z.foldl flStep (some v) = some v := by
          intro z
          induction z with
          | nil => intro v; rfl
          | cons y z ih' => intro v; simpa [flStep] using ih' v
        simp [flStep, firstLet, habs]

/-- The parameters of a piece are decided by a regular condition on the block. -/
lemma isRegular_paramOf (r : ℕ) (e : PieceParam A Q) :
    Language.IsRegular
      {z : List (Option (SnakeLet A Q R)) | paramOf r z = e} := by
  classical
  have h := RegAut.isRegular_foldl (Γ := Option (SnakeLet A Q R))
    (S := Option (Option (SnakeLet A Q R))) flStep none
    {s | (match s.join with
          | none => (default : PieceParam A Q)
          | some c => parAt r c) = e}
  refine RegAut.isRegular_of_eq h ?_
  intro z
  have key : (match (z.foldl flStep none).join with
      | none => (default : PieceParam A Q)
      | some c => parAt r c) = paramOf r z := by
    rw [flStep_eval]; rfl
  simp only [Set.mem_setOf_eq]
  exact ⟨fun hz => key.trans hz, fun hz => key.symm.trans hz⟩

/-- Every piece function is regular, given the induction hypothesis of the snake
lemma. -/
lemma isRegularFun_pieceOut (M : TwoWay A B Q) (k : ℕ)
    (ih : ∀ (M' : TwoWay A B Q), IsRegularFun (widthOut M' k)) (p : PieceParam A Q) :
    IsRegularFun (fun v : List A => pieceOut M k p v) := by
  rcases hp : p.2.2.2 with _ | ⟨q, f⟩
  · simpa [pieceOut, hp] using isRegularFun_nil (A := A) (B := B)
  · have hrev : ∀ M' : TwoWay A B Q, IsRegularFun (fun v : List A => widthOut M' k v.reverse) :=
      fun M' => (isRegularFun_reverse (A := A)).comp' (ih M') (fun _ => rfl)
    by_cases h1 : p.1 = 1
    · simpa [pieceOut, hp, h1] using ih (stopRight M p.2.1 p.2.2.1 q f)
    · by_cases h2 : p.1 = 2
      · simpa [pieceOut, hp, h1, h2] using hrev (stopRight (mirror M) p.2.2.1 p.2.1 q f)
      · by_cases h3 : p.1 = 3
        · simpa [pieceOut, hp, h1, h2, h3] using ih (M.withContext p.2.1 none q)
        · by_cases h4 : p.1 = 4
          · simpa [pieceOut, hp, h1, h2, h3, h4] using
              hrev ((mirror M).withContext p.2.1 none q)
          · simpa [pieceOut, hp, h1, h2, h3, h4] using isRegularFun_nil (A := A) (B := B)

/-- **The block function is regular**, given the induction hypothesis of the
snake lemma. -/
theorem isRegularFun_blockFun (M : TwoWay A B Q) (k : ℕ)
    (ih : ∀ (M' : TwoWay A B Q), IsRegularFun (widthOut M' k)) (R : ℕ) :
    IsRegularFun (blockFun M k R) := by
  classical
  refine isRegularFun_flatMapRange (g := fun r z => pieceOut M k (paramOf r z) (extractWin r z))
    (fun r => ?_) R
  refine isRegularFun_ofFiniteCases (d := fun z => paramOf r z)
    (g := fun p z => pieceOut M k p (extractWin r z)) (fun p => ?_) (isRegular_paramOf r)
  exact (isRegularFun_extractWin r).comp' (isRegularFun_pieceOut M k ih p) (fun _ => rfl)

end Regular

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
