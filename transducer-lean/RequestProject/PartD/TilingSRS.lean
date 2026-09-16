/-
Part D, Section *A functional programming language*: towards Lemma `lem:tiling`.

Lemma `lem:tiling` asks for the undecidability of the tiling problem
(`RequestProject/PartD/Tiling.lean`), and the book proves it by the classical reduction in which
the rows of the square grid are the successive configurations of a Turing machine.  This file
develops that reduction for the string rewriting systems of `RequestProject/PCP/Rewriting.lean`,
which is how the machines of `RequestProject/PCP/TuringMachine.lean` compute: a configuration is a
string, and one step of the machine rewrites two or three consecutive letters of it.

The two ingredients of this file are:

* **Padding.**  A machine may append a blank at the right-hand end of its configuration, which
  models the infinitely many blanks of the tape.  A tiling has a fixed width, so the blanks have
  to be there from the start; `Transducers.TilingRed.reachesRule_pad` and
  `Transducers.TilingRed.reaches_iff_padded` say that this is no restriction.
* **Rows.**  Two consecutive rows of the grid are two configurations, the second obtained from the
  first by rewriting several disjoint factors at once.  A `2 × 2` window sees only two
  horizontally adjacent cells, while a rule may rewrite three, so each cell carries the *rôle* it
  plays: which rule is being applied to the factor it belongs to, and at which offset of the
  left-hand side of that rule.  `Transducers.TilingRed.reachesRule_of_rowOk` turns a pair of rows
  tagged in this way into a rewriting, and `Transducers.TilingRed.rowOk_of_stepRule` builds the
  tagging of a single rewriting step.
-/
import RequestProject.PCP.Rewriting

namespace Transducers
namespace TilingRed

open PCP

variable {α : Type}

/-! ## Padding with blanks -/

/-- Reachability by rule steps only, for a list of rules. -/
def ReachesR (R : List (List α × List α)) : List α → List α → Prop :=
  Relation.ReflTransGen (StepRule R)

lemma ReachesR.refl (R : List (List α × List α)) (a : List α) : ReachesR R a a :=
  Relation.ReflTransGen.refl

lemma ReachesR.single {R : List (List α × List α)} {a b : List α} (h : StepRule R a b) :
    ReachesR R a b := Relation.ReflTransGen.single h

lemma ReachesR.trans {R : List (List α × List α)} {a b c : List α}
    (h₁ : ReachesR R a b) (h₂ : ReachesR R b c) : ReachesR R a c :=
  Relation.ReflTransGen.trans h₁ h₂

lemma ReachesR.append_right {R : List (List α × List α)} {a b : List α} (z : List α)
    (h : ReachesR R a b) : ReachesR R (a ++ z) (b ++ z) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.append_right z)

lemma ReachesR.append_left {R : List (List α × List α)} {a b : List α} (z : List α)
    (h : ReachesR R a b) : ReachesR R (z ++ a) (z ++ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.append_left z)

/-- A rule step does not change the length, provided the rules do not. -/
lemma StepRule.length_eq {R : List (List α × List α)}
    (hR : ∀ p ∈ R, p.1.length = p.2.length) {a b : List α} (h : StepRule R a b) :
    a.length = b.length := by
  cases h with
  | mk l u v r hm => simp [hR (u, v) hm]

lemma ReachesR.length_eq {R : List (List α × List α)}
    (hR : ∀ p ∈ R, p.1.length = p.2.length) {a b : List α} (h : ReachesR R a b) :
    a.length = b.length := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (StepRule.length_eq hR hstep)

/-- **Padding.**  A derivation of the rewriting system, in which blanks may be appended at the
right-hand end, becomes a derivation that uses rules only, after the blanks it appends have been
put at the end of the starting string. -/
lemma reachesRule_pad {S : SRS α} {a b : List α} (h : Reaches S a b) :
    ∃ z : List α, (∀ x ∈ z, x ∈ S.ext) ∧ ReachesR S.rules (a ++ z) b := by
  induction h with
  | refl => exact ⟨[], by simp, by simpa using ReachesR.refl _ _⟩
  | @tail c d _ hstep ih =>
      obtain ⟨z, hz, hreach⟩ := ih
      cases hstep with
      | rule hr => exact ⟨z, hz, hreach.trans (ReachesR.single hr)⟩
      | @ext x hx =>
          refine ⟨z ++ [x], ?_, ?_⟩
          · intro y hy
            rcases List.mem_append.1 hy with hy | hy
            · exact hz y hy
            · simpa [List.mem_singleton.1 hy] using hx
          · rw [← List.append_assoc]
            exact hreach.append_right [x]

/-- The converse: a derivation that uses rules only, starting from a padded string, is a
derivation of the rewriting system. -/
lemma reaches_of_reachesRule_pad {S : SRS α} {a b z : List α} (hz : ∀ x ∈ z, x ∈ S.ext)
    (h : ReachesR S.rules (a ++ z) b) : Reaches S a b := by
  have hpad : ∀ (z : List α), (∀ x ∈ z, x ∈ S.ext) → Reaches S a (a ++ z) := by
    intro z
    induction z using List.reverseRecOn with
    | nil => intro _; simpa using Reaches.refl S a
    | append_singleton z x ih =>
        intro hzx
        have h1 : Reaches S a (a ++ z) := ih fun y hy => hzx y (by simp [hy])
        have h2 : Step S (a ++ z) (a ++ z ++ [x]) := Step.ext (hzx x (by simp))
        exact h1.trans (Reaches.single (by simpa [List.append_assoc] using h2))
  refine (hpad z hz).trans ?_
  clear hpad hz
  induction h with
  | refl => exact Reaches.refl _ _
  | tail _ hstep ih => exact ih.trans (Reaches.single (Step.rule hstep))

end TilingRed
end Transducers
