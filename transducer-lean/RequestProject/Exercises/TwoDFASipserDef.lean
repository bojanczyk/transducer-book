/-
Exercise `exer:2dfa-loop-elimination-sipser` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk): the language of Exercise `exer:2dfa-loop-elimination` -- the inputs on
which a deterministic two-way transducer terminates -- is recognised by a deterministic two-way
automaton of *polynomial* size.

The solution of the book is the one followed here.  The configurations that reach the accepting
configuration form a tree, because the configuration graph of a deterministic machine has out-degree
at most one and no configuration on a cycle can reach an accepting one.  That tree is explored by a
depth-first search *performed by a two-way automaton*: the vertex currently visited is a
configuration, whose position is the position of the head and whose state is remembered in the state
of the searching automaton; the children of a configuration -- the configurations that lead to it in
one step -- are at distance one from it and are determined by a state and a direction, so they can
be enumerated with a bounded amount of bookkeeping; and no stack is needed to move up in the tree,
because the parent of a configuration is computed from it by the (deterministic) transition
function.  The search accepts as soon as it discovers the initial configuration.

Two points that the book passes over are dealt with here.

* The book assumes without loss of generality that the machine halts in a fixed configuration.  No
  such normalisation is performed below; instead the tree is rooted at a virtual vertex, the
  accepting answer, whose children are scanned by a left-to-right sweep over the input, and the
  search returns to that sweep whenever it finishes the subtree of one of them.
* A transition of a two-way automaton must move the head, so a step of the search that stays at the
  current position is performed by moving to a neighbour and back.  This is possible at every
  position of a non-empty input; on the empty input the automaton answers immediately, which it may
  do since its transition function is an arbitrary (here classically defined) function.

The construction is carried out for an arbitrary two-way automaton, whose acceptance is "the run
reaches the answer *true*", and produces an equivalent automaton that *terminates on every input*
(this is what makes the statement non-trivial: the automaton of Exercise `exer:2dfa-loop-elimination`
has `|Q|` states but does not terminate on the inputs it rejects).  The exercise is the special case
of the automaton `haltDFA M` of `RequestProject/Exercises/TwoDFALoop.lean`.
-/
import RequestProject.Exercises.TwoDFALoop

namespace Transducers
namespace Exercises

open Transducers

/-! ## The states of the searching automaton -/

/-- A phase of the depth-first search.  Each phase is executed with the head at a position that the
phase itself determines relative to the vertex being visited. -/
inductive Dfs (R : Type)
  /-- At position `p`: consider the configuration `(p, r)` as a child of the root. -/
  | scanCur : R → Dfs R
  /-- At position `p`: the root candidate `(p, r)` is finished, pass to the next one. -/
  | scanNext : R → Dfs R
  /-- At position `p`: start exploring the children of the vertex `(p, r)`. -/
  | desc : R → Dfs R
  /-- At position `p`: the subtree of `(p, r)` is explored, go to the parent of `(p, r)`. -/
  | up : R → Dfs R
  /-- At the position of a candidate child: check whether the candidate with state `c` is a child of
  the vertex with state `q`, which sits one position to the right (`s = true`) or to the left
  (`s = false`). -/
  | chk : R → R → Bool → Dfs R
  /-- At the position of the vertex with state `q`: the candidate child with state `c` on the side
  `s` is finished. -/
  | cont : R → R → Bool → Dfs R

/-- The state of the searching automaton: a phase, or a phase together with the direction of the
first half of a step that has to stay at the current position. -/
abbrev DfsSt (R : Type) := Dfs R ⊕ (Dfs R × Bool)

variable {A R : Type}

/-- The phases, listed as a sum of products, which is how they are counted. -/
def dfsEquiv (R : Type) :
    Dfs R ≃ ((R ⊕ R) ⊕ (R ⊕ R)) ⊕ ((R × R × Bool) ⊕ (R × R × Bool)) where
  toFun
    | Dfs.scanCur r => Sum.inl (Sum.inl (Sum.inl r))
    | Dfs.scanNext r => Sum.inl (Sum.inl (Sum.inr r))
    | Dfs.desc r => Sum.inl (Sum.inr (Sum.inl r))
    | Dfs.up r => Sum.inl (Sum.inr (Sum.inr r))
    | Dfs.chk q c s => Sum.inr (Sum.inl (q, c, s))
    | Dfs.cont q c s => Sum.inr (Sum.inr (q, c, s))
  invFun
    | Sum.inl (Sum.inl (Sum.inl r)) => Dfs.scanCur r
    | Sum.inl (Sum.inl (Sum.inr r)) => Dfs.scanNext r
    | Sum.inl (Sum.inr (Sum.inl r)) => Dfs.desc r
    | Sum.inl (Sum.inr (Sum.inr r)) => Dfs.up r
    | Sum.inr (Sum.inl (q, c, s)) => Dfs.chk q c s
    | Sum.inr (Sum.inr (q, c, s)) => Dfs.cont q c s
  left_inv := by rintro (r | r | r | r | ⟨q, c, s⟩ | ⟨q, c, s⟩) <;> rfl
  right_inv := by rintro (((r | r) | (r | r)) | (⟨q, c, s⟩ | ⟨q, c, s⟩)) <;> rfl

noncomputable instance [Fintype R] : Fintype (Dfs R) := Fintype.ofEquiv _ (dfsEquiv R).symm

lemma card_dfs [Fintype R] :
    Fintype.card (Dfs R) = 4 * Fintype.card R + 4 * Fintype.card R ^ 2 := by
  rw [Fintype.card_congr (dfsEquiv R)]
  simp [Fintype.card_sum, Fintype.card_prod, pow_two]
  ring

lemma card_dfsSt [Fintype R] :
    Fintype.card (DfsSt R) = 12 * Fintype.card R + 12 * Fintype.card R ^ 2 := by
  show Fintype.card (Dfs R ⊕ (Dfs R × Bool)) = _
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, card_dfs]
  ring

/-! ## The searching automaton -/

section Aut

open Classical in
/-- The states of the automaton, enumerated. -/
noncomputable def rIdx [Fintype R] (r : R) : ℕ := (Fintype.equivFin R r).val

open Classical in
/-- The next state in the enumeration, if there is one. -/
noncomputable def rSucc [Fintype R] (r : R) : Option R :=
  if h : rIdx r + 1 < Fintype.card R then some ((Fintype.equivFin R).symm ⟨rIdx r + 1, h⟩) else none

open Classical in
/-- The first state in the enumeration.  A state is given, so that the enumeration is not empty. -/
noncomputable def rFirst [Fintype R] (r₀ : R) : R :=
  (Fintype.equivFin R).symm ⟨0, Fintype.card_pos_iff.2 ⟨r₀⟩⟩

open Classical in
/-- A step of the search that does not move the vertex: the head moves to a neighbour and comes
back.  There is a neighbour unless the input is empty. -/
noncomputable def dfsStay (ph : Dfs R) (x : Option A) : Bool ⊕ (DfsSt R × Bool) :=
  match x with
  | some _ => Sum.inr (Sum.inr (ph, true), true)
  | none => Sum.inr (Sum.inr (ph, false), false)

open Classical in
/-- One phase of the depth-first search. -/
noncomputable def dfsPhase [Fintype R] (N : TwoDFA A R) (l : Option A) (ph : Dfs R) (x : Option A) :
    Bool ⊕ (DfsSt R × Bool) :=
  match ph with
  | Dfs.scanCur r =>
      match N.step l r x with
      | Sum.inl true =>
          if l.isNone ∧ r = N.init then Sum.inl true else dfsStay (Dfs.desc r) x
      | _ => dfsStay (Dfs.scanNext r) x
  | Dfs.scanNext r =>
      match rSucc r with
      | some r' => dfsStay (Dfs.scanCur r') x
      | none =>
          match x with
          | some _ => Sum.inr (Sum.inl (Dfs.scanCur (rFirst N.init)), true)
          | none => Sum.inl false
  | Dfs.desc r =>
      match l, x with
      | some _, _ => Sum.inr (Sum.inl (Dfs.chk r (rFirst N.init) true), false)
      | none, some _ => Sum.inr (Sum.inl (Dfs.chk r (rFirst N.init) false), true)
      | none, none => Sum.inl false
  | Dfs.chk q c s =>
      if N.step l c x = Sum.inr (q, s) then
        if l.isNone ∧ c = N.init then Sum.inl true else dfsStay (Dfs.desc c) x
      else Sum.inr (Sum.inl (Dfs.cont q c s), s)
  | Dfs.cont q c s =>
      match rSucc c with
      | some c' => Sum.inr (Sum.inl (Dfs.chk q c' s), !s)
      | none =>
          if s then
            match x with
            | some _ => Sum.inr (Sum.inl (Dfs.chk q (rFirst N.init) false), true)
            | none => dfsStay (Dfs.up q) x
          else dfsStay (Dfs.up q) x
  | Dfs.up q =>
      match N.step l q x with
      | Sum.inl true => dfsStay (Dfs.scanNext q) x
      | Sum.inl false => Sum.inl false
      | Sum.inr (q', d) => Sum.inr (Sum.inl (Dfs.cont q' q d), d)

open Classical in
/-- The transition function of the searching automaton.  On the empty input -- the only input on
which the head has no neighbour to move to -- the answer is given at once. -/
noncomputable def dfsStep [Fintype R] (N : TwoDFA A R) (l : Option A) (st : DfsSt R)
    (x : Option A) : Bool ⊕ (DfsSt R × Bool) :=
  match l, x with
  | none, none => Sum.inl (decide (N.Accepts []))
  | _, _ =>
      match st with
      | Sum.inr (ph, d) => Sum.inr (Sum.inl ph, !d)
      | Sum.inl ph => dfsPhase N l ph x

/-- The two-way automaton that searches the tree of the configurations reaching the answer *true*
of `N`, by depth-first search. -/
noncomputable def dfsAut [Fintype R] (N : TwoDFA A R) : TwoDFA A (DfsSt R) where
  init := Sum.inl (Dfs.scanCur (rFirst N.init))
  step := dfsStep N

end Aut

end Exercises
end Transducers
