/-
Part D, Section *Evaluation*, subsection *Simon trees*: factorisation trees and Simon trees.

This file formalises the definition of a *Simon tree* of *Transducers* (M. Bojańczyk).  The
definition is the `definition` environment headed *Simon tree* in `partDPolyregular/evaluation.tex`;
it carries **no `\label`** in the book, so it has no label to be referred to by and no alias in
`RequestProject/Labels.lean` (no placeholder label is invented for it).

## Factorisation trees

A *factorisation tree* for a monoid homomorphism `h : A* → M` is, in the book, a tree whose leaves
are labelled by input letters and whose inner nodes are labelled by the value of `h` on the string
in their subtree.  Since that label is determined by the tree, `Transducers.FactTree` stores only the
shape and the letters: a tree is either a leaf carrying a letter, or an inner node carrying the
(ordered) list of its children.  The label of a node `t` is recovered as `h t.yield`, where
`Transducers.FactTree.yield` is the string in the leaves of `t` (the *underlying string*).

An inner node may have any number of children.  A node with no children has the empty string as its
yield; this is the only way to give the empty string a factorisation tree, which the Factorisation
Forest Theorem (`thm:factorisation-forest`), stated for monoid homomorphisms, needs.

## Simon trees

A *Simon tree* (`Transducers.FactTree.IsSimon`) is a factorisation tree with the idempotent
property: if a node has at least three children, then all these children have the same label,
which is an idempotent of the monoid.  The label of a child that is a leaf with letter `a` is
`h a`, the value of the homomorphism on the one-letter string -- that is how the book's pictures
read the condition, and it is what makes the label of every node, leaf or not, equal to the value
of the homomorphism on its subtree.
-/
import Mathlib

namespace Transducers

universe u

/-- A **factorisation tree** over the alphabet `A`: a leaf labelled by a letter, or an inner node
with an ordered list of children.  The monoid labels of the inner nodes are not stored, since they
are determined by the tree (see `Transducers.FactTree.label`). -/
inductive FactTree (A : Type u) : Type u
  | leaf : A → FactTree A
  | node : List (FactTree A) → FactTree A

namespace FactTree

variable {A : Type u}

/-- The **underlying string** of a factorisation tree: the string in its leaves, read from left to
right. -/
def yield : FactTree A → List A
  | leaf a => [a]
  | node cs => (cs.map yield).flatten

/-- The **height** of a factorisation tree: `0` for a leaf, and one more than the maximal height of
a child for an inner node. -/
def height : FactTree A → ℕ
  | leaf _ => 0
  | node cs => (cs.map height).foldr max 0 + 1

@[simp] lemma yield_leaf (a : A) : (leaf a).yield = [a] := by rw [yield]

@[simp] lemma yield_node (cs : List (FactTree A)) :
    (node cs).yield = (cs.map yield).flatten := by
  rw [yield]

@[simp] lemma height_leaf (a : A) : (leaf a).height = 0 := by rw [height]

lemma height_node (cs : List (FactTree A)) :
    (node cs).height = (cs.map height).foldr max 0 + 1 := by
  rw [height]

/-- The label of a node of a factorisation tree for the homomorphism `h`: the value of `h` on the
string in its subtree. -/
def label {M : Type*} [Monoid M] (h : FreeMonoid A →* M) (t : FactTree A) : M :=
  h (FreeMonoid.ofList t.yield)

/-- **Simon tree** (the definition headed *Simon tree* in Section *Evaluation*; it carries no
`\label` in the book).  A factorisation tree for the monoid homomorphism `h` is a Simon tree if every
node with at least three children has all its children labelled by the same monoid element, and
that element is an idempotent. -/
inductive IsSimon {M : Type*} [Monoid M] (h : FreeMonoid A →* M) : FactTree A → Prop
  | leaf (a : A) : IsSimon h (leaf a)
  | node (cs : List (FactTree A)) :
      (∀ c ∈ cs, IsSimon h c) →
      (3 ≤ cs.length → ∃ e : M, IsIdempotentElem e ∧ ∀ c ∈ cs, label h c = e) →
      IsSimon h (node cs)

/-- `IsSubtree s t`: the tree `s` is a subtree of `t`, i.e. the subtree rooted at one of the nodes
of `t` (possibly `t` itself). -/
inductive IsSubtree : FactTree A → FactTree A → Prop
  | refl (t : FactTree A) : IsSubtree t t
  | child {s c : FactTree A} {cs : List (FactTree A)} :
      c ∈ cs → IsSubtree s c → IsSubtree s (node cs)

lemma IsSubtree.trans {s t r : FactTree A} (h₁ : IsSubtree s t) (h₂ : IsSubtree t r) :
    IsSubtree s r := by
  induction h₂ with
  | refl => exact h₁
  | child hc _ ih => exact IsSubtree.child hc ih

lemma le_foldr_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    simp only [List.foldr_cons]
    rcases hx with h | h
    · rw [h]; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma height_le_of_mem {c : FactTree A} {cs : List (FactTree A)} (hc : c ∈ cs) :
    c.height + 1 ≤ (node cs).height := by
  rw [height_node]
  have : c.height ≤ (cs.map height).foldr max 0 := le_foldr_max (List.mem_map_of_mem hc)
  omega

lemma height_node_le {cs : List (FactTree A)} {n : ℕ} (h : ∀ c ∈ cs, c.height ≤ n) :
    (node cs).height ≤ n + 1 := by
  rw [height_node]
  have : (cs.map height).foldr max 0 ≤ n := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact max_le (h c (by simp)) (ih fun d hd => h d (by simp [hd]))
  omega

end FactTree

end Transducers
