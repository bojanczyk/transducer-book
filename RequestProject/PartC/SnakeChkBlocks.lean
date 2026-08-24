/-
**Cutting the annotated string of stage 1 into blocks.**

The annotation of stage 1 of the induction step of the book's snake lemma is
letter to letter: every annotated letter carries a bit `sep` saying that a block
boundary precedes it and a bit `sepA` saying that a block boundary follows it,
and the homomorphism that produces the marked input inserts the separators
accordingly.  This file computes the list of blocks of the resulting string
(`Transducers.BlockIdx.splitSep_homOf_outLet`): they are the factors of the
annotation between consecutive marked positions, with an empty block in front
and, if the last letter carries `sepA`, an empty block at the end.

Nothing here is specific to transducers.
-/
import RequestProject.PartC.SnakeChkSplit
import RequestProject.PartC.SnakeAssemble

namespace Transducers

namespace BlockIdx

open RegPair TwoWay

variable {Γ C : Type}

/-! ## The separator-inserting homomorphism -/

/-- The image of an annotated letter: the letter, preceded and followed by a
separator as its two bits prescribe. -/
def outLet (sep sepA : Γ → Bool) (lett : Γ → C) (c : Γ) : List (Option C) :=
  (if sep c then [none] else []) ++ some (lett c) :: (if sepA c then [none] else [])

/-- The same without the trailing separator, which only the last letter of the
string may carry. -/
def outLetF (sep : Γ → Bool) (lett : Γ → C) (c : Γ) : List (Option C) :=
  (if sep c then [none] else []) ++ [some (lett c)]

variable {sep sepA : Γ → Bool} {lett : Γ → C}

/-- Away from the last letter the two homomorphisms agree. -/
lemma homOf_outLet_of_no_sepA {v : List Γ} (h : ∀ c ∈ v, sepA c = false) :
    homOf (outLet sep sepA lett) v = homOf (outLetF sep lett) v := by
  induction v with
  | nil => rfl
  | cons c v ih =>
      rw [homOf_cons, homOf_cons, ih (fun x hx => h x (by simp [hx])), outLet, outLetF,
        h c (by simp)]
      simp

/-- The string produced by the annotation: the blocks, followed by a final
separator if the last letter asks for one. -/
lemma homOf_outLet_eq (u : List Γ)
    (hsa : ∀ (j : ℕ) (hj : j < u.length), sepA u[j] = true → j = u.length - 1) :
    homOf (outLet sep sepA lett) u
      = homOf (outLetF sep lett) u ++ (if u.getLast?.elim false sepA then [none] else []) := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton v z ih =>
      have hv : ∀ c ∈ v, sepA c = false := by
        intro c hc
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
        by_contra hcon
        have hcon' : sepA (v ++ [z])[j] = true := by
          rw [List.getElem_append_left hj]
          simpa using hcon
        have := hsa j (by simp; omega) hcon'
        simp at this
        omega
      rw [homOf_append, homOf_append, homOf_outLet_of_no_sepA hv]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.elim]
      rw [show homOf (outLet sep sepA lett) [z] = outLet sep sepA lett z from by simp [homOf],
        show homOf (outLetF sep lett) [z] = outLetF sep lett z from by simp [homOf],
        outLet, outLetF]
      by_cases h : sepA z <;> simp [h, List.append_assoc]

/-! ## Splitting the string -/

lemma splitSep_append_none (v : List (Option C)) :
    splitSep (v ++ [none]) = splitSep v ++ [[]] := by
  induction v with
  | nil => rfl
  | cons x v ih =>
      cases x with
      | none => rw [List.cons_append, show splitSep (none :: (v ++ [none])) = [] :: splitSep
          (v ++ [none]) from rfl, ih, show splitSep (none :: v) = [] :: splitSep v from rfl]
                simp
      | some c =>
          rcases hv : splitSep v with _ | ⟨b, bs⟩
          · exact absurd hv (splitSep_ne_nil v)
          · rw [List.cons_append,
              show splitSep (some c :: (v ++ [none])) = (c :: (splitSep (v ++ [none])).headI)
                :: (splitSep (v ++ [none])).tail from by
                rw [splitSep]
                rcases h2 : splitSep (v ++ [none]) with _ | ⟨b', bs'⟩
                · exact absurd h2 (splitSep_ne_nil _)
                · rfl,
              ih, hv,
              show splitSep (some c :: v) = (c :: b) :: bs from by rw [splitSep, hv]]
            simp

/-- The blocks of the string produced by a list of blocks of the annotation. -/
lemma splitSep_homOf_outLetF_flatten (Bs : List (List Γ))
    (hB : ∀ B ∈ Bs, ∃ c B', B = c :: B' ∧ sep c = true ∧ ∀ x ∈ B', sep x = false) :
    splitSep (homOf (outLetF sep lett) Bs.flatten) = [] :: Bs.map (fun B => B.map lett) := by
  induction Bs with
  | nil => rfl
  | cons B Bs ih =>
      obtain ⟨c, B', rfl, hc, hB'⟩ := hB B (by simp)
      have hflat : ∀ (v : List Γ), (∀ x ∈ v, sep x = false) →
          homOf (outLetF sep lett) v = (v.map lett).map some := by
        intro v
        induction v with
        | nil => rfl
        | cons x v ih2 =>
            intro hv
            rw [homOf_cons, ih2 (fun y hy => hv y (by simp [hy])), outLetF, hv x (by simp)]
            simp
      rw [List.flatten_cons, List.cons_append, homOf_cons,
        show outLetF sep lett c = none :: [some (lett c)] from by rw [outLetF, hc]; rfl]
      rw [show homOf (outLetF sep lett) (B' ++ Bs.flatten)
          = homOf (outLetF sep lett) B' ++ homOf (outLetF sep lett) Bs.flatten from
        homOf_append _ _,
        hflat B' hB']
      rw [List.cons_append, List.cons_append,
        show splitSep (none :: ([some (lett c)] ++ ((B'.map lett).map some
              ++ homOf (outLetF sep lett) Bs.flatten)))
          = [] :: splitSep ([some (lett c)] ++ ((B'.map lett).map some
              ++ homOf (outLetF sep lett) Bs.flatten)) from rfl]
      rcases hrest : splitSep (homOf (outLetF sep lett) Bs.flatten) with _ | ⟨b0, bs0⟩
      · exact absurd hrest (splitSep_ne_nil _)
      · have hsplit := splitSep_map_some_append (lett c :: B'.map lett)
          (homOf (outLetF sep lett) Bs.flatten) b0 bs0 hrest
        rw [List.map_cons, List.cons_append] at hsplit
        rw [show ([some (lett c)] ++ ((B'.map lett).map some
              ++ homOf (outLetF sep lett) Bs.flatten))
            = some (lett c) :: ((B'.map lett).map some
              ++ homOf (outLetF sep lett) Bs.flatten) from rfl, ← List.cons_append,
          ← List.map_cons, hsplit]
        rw [ih (fun B hB2 => hB B (by simp [hB2]))] at hrest
        rw [show b0 = [] from by rw [hrest] at *; injection hrest,
          show bs0 = Bs.map (fun B => B.map lett) from by
            have : ([] : List C) :: Bs.map (fun B => B.map lett) = b0 :: bs0 := hrest.symm
            injection this with _ h2
            exact h2.symm]
        simp

/-! ## The blocks of the annotation -/

/-- The factors of the annotation between consecutive marked positions cover the
annotation. -/
lemma flatten_seg_range (u : List Γ) (Y : ℕ → ℕ) (hmono : ∀ m, Y m ≤ Y (m + 1)) :
    ∀ L : ℕ, ((List.range L).map (fun m => seg u (Y m) (Y (m + 1)))).flatten
      = seg u (Y 0) (Y L) := by
  intro L
  induction L with
  | zero => simp [seg_eq_nil (le_refl (Y 0))]
  | succ L ih =>
      rw [List.range_succ, List.map_append, List.flatten_append, ih]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      exact seg_append (snakeY_chain hmono 0 L (Nat.zero_le _)) (hmono L)

/-- The number of blocks of the string produced by the annotation, minus one. -/
noncomputable def nbl (sep sepA : Γ → Bool) (u : List Γ) : ℕ :=
  nsep sep u + (if u.getLast?.elim false sepA then 1 else 0)

/-- **The blocks of the string produced by the annotation** are the factors of
the annotation between consecutive marked positions, with an empty block in
front and, if the last letter carries `sepA`, an empty block at the end. -/
theorem splitSep_homOf_outLet {u : List Γ} (hne : u ≠ [])
    (h0 : ∀ hu : 0 < u.length, sep u[0] = true)
    (hsa : ∀ (j : ℕ) (hj : j < u.length), sepA u[j] = true → j = u.length - 1) :
    splitSep (homOf (outLet sep sepA lett) u)
      = (List.range (nbl sep sepA u + 1)).map
          (fun m => (seg u (bstart sep u m) (bstart sep u (m + 1))).map lett) := by
  sorry

end BlockIdx

end Transducers
