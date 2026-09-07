/-
The list deconstructor on the right is rational under string representation.  Part of the easy
direction of Theorem `thm:rational-terms` of *Transducers* (M. Bojańczyk).

`unsnoc` is the atomic function that Theorem `thm:rational-terms` adds so that the right-to-left
machines can be handled without string reversal.  It maps `[a₁,…,aₙ]` to `R ([a₁,…,aₙ₋₁], aₙ)`, so
under string representation it has to close the list *before* the representation of the last entry
and to put a comma there -- and whether a given top-level comma of the input is the last one is a
property of the suffix, not of the prefix.  A machine of `CombMach.lean`, which reads the input
once from left to right, therefore does not suffice; a *bilateral* rewriting `Transducers.biEval`
does.

The parsing is not done by the bilateral rewriting itself.  The input is first marked by the
machine `Transducers.Comb.listMarkMach` of `CombMark.lean`, which deletes the outer brackets and
replaces the top-level commas by the separator, so that the bilateral rewriting sees the blocks of
the list directly: its right-to-left automaton has two states, "a separator occurs later" and "no
separator occurs later", and its left-to-right automaton has two states, "this is the first
letter" and "it is not".  The marking of the empty list is the empty string, which is the case
`L 1` of the output; it is separated off by a case distinction over a regular language.
-/
import RequestProject.PartC.RatAtomA
import RequestProject.PartC.RatBi
import RequestProject.PartC.CombMark

namespace Transducers
namespace RatComb

open Comb

/-! ## The bilateral rewriting -/

/-- The left-to-right automaton: it only records whether a letter has already been read. -/
def unsnocMu (_ : Bool) (_ : Option Sym8) : Bool := true

/-- The right-to-left automaton: it records whether a separator occurs in the suffix. -/
def unsnocNu (s : Bool) (a : Option Sym8) : Bool := s || a.isNone

/-- The opening of the output, written at the first letter: the list is closed at once if there is
no separator at all, that is, if the input list has one entry. -/
def unsnocPre : Bool → Bool → List Sym8
  | true, _ => []
  | false, true => [Sym8.right, Sym8.lpar, Sym8.lbrack]
  | false, false => [Sym8.right, Sym8.lpar, Sym8.lbrack, Sym8.rbrack, Sym8.comma]

/-- What is written at a separator: a comma, unless it is the last separator, where the list is
closed first. -/
def unsnocSep : Bool → List Sym8
  | true => [Sym8.comma]
  | false => [Sym8.rbrack, Sym8.comma]

/-- The output function of the bilateral rewriting. -/
def unsnocPsi (p : Bool) (a : Option Sym8) (s : Bool) : List Sym8 :=
  match a with
  | none => unsnocSep s
  | some c => unsnocPre p s ++ [c]

/-- What is written after the blocks that precede the last one. -/
def unsnocSepU : List (List Sym8) → List Sym8
  | [] => []
  | _ :: _ => [Sym8.rbrack, Sym8.comma]

/-! ## The two automata on a marked string -/

private lemma revTrans_map_some (s : Bool) :
    ∀ x : List Sym8, revTrans unsnocNu (x.map some) s = s := by
  intro x
  induction x with
  | nil => rfl
  | cons c x ih => rw [List.map_cons, revTrans_cons, ih]; simp [unsnocNu]

private lemma strTrans_unsnocMu :
    ∀ (w : List (Option Sym8)) (p : Bool), strTrans unsnocMu w p = true ∨ w = [] := by
  intro w
  induction w with
  | nil => intro p; exact Or.inr rfl
  | cons a w ih =>
      intro p
      rcases ih (unsnocMu p a) with h | rfl
      · exact Or.inl (by rw [show strTrans unsnocMu (a :: w) p = strTrans unsnocMu w
          (unsnocMu p a) from rfl, h])
      · exact Or.inl rfl

private lemma strTrans_unsnocMu_cons (a : Option Sym8) (w : List (Option Sym8)) (p : Bool) :
    strTrans unsnocMu (a :: w) p = true := by
  rcases strTrans_unsnocMu (a :: w) p with h | h
  · exact h
  · exact absurd h (by simp)

private lemma strTrans_unsnocMu_map (c : Sym8) (x : List Sym8) (p : Bool) :
    strTrans unsnocMu ((c :: x).map some) p = true := by
  rw [List.map_cons]
  exact strTrans_unsnocMu_cons _ _ _

private lemma biEvalT_map_some (s : Bool) :
    ∀ (c : Sym8) (x : List Sym8) (p : Bool),
      biEvalT unsnocMu unsnocNu unsnocPsi p ((c :: x).map some) s = unsnocPre p s ++ (c :: x) := by
  intro c x
  induction x generalizing c with
  | nil =>
      intro p
      show unsnocPsi p (some c) (revTrans unsnocNu [] s) ++ _ = _
      simp [unsnocPsi]
  | cons c' x ih =>
      intro p
      rw [List.map_cons, biEvalT_cons, revTrans_map_some s (c' :: x),
        show unsnocMu p (some c) = true from rfl, ih c' true]
      simp [unsnocPsi, unsnocPre]

private lemma revTrans_optBlocks :
    ∀ (u : List (List Sym8)) (z : List Sym8),
      revTrans unsnocNu (optBlocks (u ++ [z])) false = !u.isEmpty := by
  intro u
  induction u with
  | nil => intro z; simpa using revTrans_map_some false z
  | cons x u ih =>
      intro z
      have hne : u ++ [z] ≠ [] := by simp
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne
      rw [List.cons_append, optBlocks_cons, hy, optBlocksTail_cons, ← hy, revTrans_append,
        revTrans_map_some, revTrans_cons]
      simp [unsnocNu]

/-! ## The value of the bilateral rewriting on a marked list -/

private lemma biEvalT_optBlocks :
    ∀ (u : List (List Sym8)) (z : List Sym8) (p : Bool), (∀ x ∈ u, x ≠ []) → z ≠ [] →
      biEvalT unsnocMu unsnocNu unsnocPsi p (optBlocks (u ++ [z])) false
        = unsnocPre p (!u.isEmpty) ++ (joinSep u ++ unsnocSepU u ++ z) := by
  intro u
  induction u with
  | nil =>
      intro z p _ hz
      obtain ⟨c, x, rfl⟩ := List.exists_cons_of_ne_nil hz
      simpa [unsnocSepU] using biEvalT_map_some false c x p
  | cons x u ih =>
      intro z p hx hz
      have hxne : x ≠ [] := hx x (by simp)
      obtain ⟨c, x', rfl⟩ := List.exists_cons_of_ne_nil hxne
      have hne : u ++ [z] ≠ [] := by simp
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hne
      have hopt : optBlocks ((c :: x') :: (u ++ [z]))
          = ((c :: x').map some) ++ (none :: optBlocks (u ++ [z])) := by
        rw [optBlocks_cons, hy, optBlocksTail_cons, ← hy]
      rw [List.cons_append, hopt, biEvalT_append, revTrans_cons, revTrans_optBlocks u z,
        biEvalT_map_some _ c x' p, strTrans_unsnocMu_map, biEvalT_cons,
        revTrans_optBlocks u z, show unsnocMu true none = true from rfl,
        ih z true (fun w hw => hx w (by simp [hw])) hz]
      have hs : unsnocNu (!u.isEmpty) none = true := by simp [unsnocNu]
      rw [hs]
      cases u with
      | nil =>
          simp [unsnocPsi, unsnocSep, unsnocSepU, unsnocPre, joinSep]
      | cons w u' =>
          simp only [List.isEmpty_cons, Bool.not_false]
          rw [show unsnocPsi true none true = [Sym8.comma] from rfl]
          rw [show joinSep ((c :: x') :: w :: u') = (c :: x') ++ Sym8.comma :: joinSep (w :: u')
            from joinSep_cons_cons _ _ _]
          cases p <;> simp [unsnocPre, unsnocSepU]

/-! ## The rational function -/

/-- The bilateral rewriting that turns the marking of a list into the representation of its
`unsnoc`. -/
def unsnocBi (v : List (Option Sym8)) : List Sym8 :=
  biEval unsnocMu false unsnocNu false unsnocPsi v

lemma isRationalFun_unsnocBi : IsRationalFun unsnocBi :=
  isRationalFun_biEval _ _ _ _ _

open scoped Classical in
/-- The string function of the list deconstructor on the right. -/
noncomputable def unsnocStr (A : Ty) (w : List Sym8) : List Sym8 :=
  let v := listMarkMach.run (listMarkN A) .start w
  if v ∈ emptyLang (Option Sym8) then [Sym8.left, Sym8.one] else unsnocBi v ++ [Sym8.rpar]

open scoped Classical in
lemma isRationalFun_unsnocStr (A : Ty) : IsRationalFun (unsnocStr A) :=
  isRationalFun_comp' (listMarkMach.isRationalFun_run _ _)
    (isRationalFun_ite_lang (emptyLang_isRegular (Option Sym8))
      (isRationalFun_const [Sym8.left, Sym8.one])
      (isRationalFun_comp' isRationalFun_unsnocBi (isRationalFun_appendConst [Sym8.rpar])
        (fun _ => rfl)))
    (fun _ => rfl)

/-- **The list deconstructor on the right is rational under string representation.** -/
theorem isRationalUnderRepr_unsnoc (A : Ty) :
    IsRationalUnderRepr (A := Ty.list A) (B := Ty.sum Ty.one (Ty.prod (Ty.list A) A))
      (fun l => unsnocList l) := by
  classical
  refine ⟨unsnocStr A, isRationalFun_unsnocStr A, fun l => ?_⟩
  have hmark : listMarkMach.run (listMarkN A) .start ((Ty.list A).repr l)
      = optBlocks (l.map A.repr) := listMarkMach_run A l
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩
  · show (if _ ∈ emptyLang (Option Sym8) then _ else _) = _
    rw [hmark]
    simp only [List.map_nil, optBlocks_nil]
    rw [if_pos (show ([] : List (Option Sym8)) ∈ emptyLang (Option Sym8) from rfl)]
    rfl
  · rw [List.concat_eq_append] at *
    have hz : A.repr a ≠ [] := by
      obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A a
      rw [hcw]; simp
    have hu : ∀ x ∈ l'.map A.repr, x ≠ [] := by
      intro x hx
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A b
      rw [hcw]; simp
    have hmap : (l' ++ [a]).map A.repr = l'.map A.repr ++ [A.repr a] := by simp
    have hnonempty : optBlocks ((l' ++ [a]).map A.repr) ∉ emptyLang (Option Sym8) := by
      rw [hmap]
      cases hl : l'.map A.repr with
      | nil =>
          obtain ⟨c, w, hcw, -⟩ := repr_eq_cons A a
          show ¬ (optBlocks ([] ++ [A.repr a]) = [])
          simp [hcw]
      | cons x xs =>
          show ¬ (optBlocks ((x :: xs) ++ [A.repr a]) = [])
          rw [List.cons_append, optBlocks_cons]
          have hxne : x ≠ [] := hu x (by rw [hl]; simp)
          obtain ⟨c, w, rfl⟩ := List.exists_cons_of_ne_nil hxne
          simp
    show (if _ ∈ emptyLang (Option Sym8) then _ else _) = _
    rw [hmark, if_neg hnonempty, hmap,
      show unsnocBi (optBlocks (l'.map A.repr ++ [A.repr a]))
        = biEvalT unsnocMu unsnocNu unsnocPsi false
            (optBlocks (l'.map A.repr ++ [A.repr a])) false from rfl,
      biEvalT_optBlocks (l'.map A.repr) (A.repr a) false hu hz]
    show _ = (Ty.sum Ty.one (Ty.prod (Ty.list A) A)).repr (unsnocList (l' ++ [a]))
    rw [unsnocList_append_singleton]
    show _ = Sym8.right :: ((Ty.prod (Ty.list A) A).repr (l', a))
    rw [Ty.repr_prod, Ty.repr_list]
    cases hl : l'.map A.repr with
    | nil => simp [unsnocPre, unsnocSepU]
    | cons x xs => simp [unsnocPre, unsnocSepU]

end RatComb
end Transducers
