/-
Exercise `exer:duplication-not-rational` of *Transducers* (M. Bojańczyk): string duplication
`w ↦ ww` is not a rational function.

The author's solution is the one that is used for string reversal in
`RequestProject/Exercises/ReverseNotRational.lean`: the relation `∼` of Theorem
`thm:machine-independent-rational-functions` (`Transducers.BoundedVarRel`) has infinite index, and
in fact all strings are pairwise inequivalent.  Only the strings `falseⁿ` are needed to see this,
and the alphabet is `Bool`, which has two letters -- over a one-letter alphabet duplication is the
homomorphism `a ↦ aa`, hence rational.

The statement itself is not new to the project: it is also the second item of Exercise
`exer:non-rational`, and is `Transducers.Exercises.not_isRationalFun_duplicate` of
`RequestProject/Exercises/PartBC.lean`, proved there by the other argument the book gives -- the
range of duplication is the language of squares, which is not regular.  That declaration is the
one the label `exer:duplication-not-rational` is aliased to; the theorem of this file,
`Transducers.Exercises.not_isRationalFun_duplicate_boundedVar`, is the same statement proved by
the argument that this exercise asks for, and is the second alias of the label.
-/
import RequestProject.PartB.WeightedStatements

namespace Transducers.Exercises

open Transducers

/-- **Duplication separates `falseⁱ` from `falseʲ` for `i < j`.**  Extending both on the left by
`true^{K+1}` gives the outputs `(true^{K+1} falseⁱ)²` and `(true^{K+1} falseʲ)²`, which agree only
on the first `K + 1 + i` letters -- the next letter is the `true` opening the second copy on the
left, and a `false` of the first copy on the right -- so their left distance exceeds `K`. -/
lemma not_boundedVarRel_duplicate {i j : ℕ} (hij : i < j) :
    ¬ BoundedVarRel (fun w : List Bool => w ++ w)
      (List.replicate i false) (List.replicate j false) := by
  rintro ⟨K, hK⟩
  have h := hK (List.replicate (K + 1) true)
  set u : List Bool := List.replicate (K + 1) true ++ List.replicate i false with hu
  set v : List Bool := List.replicate (K + 1) true ++ List.replicate j false with hv
  have hulen : u.length = K + 1 + i := by simp [hu]
  have hvlen : v.length = K + 1 + j := by simp [hv]
  have hxlen : (u ++ u).length = (K + 1 + i) + (K + 1 + i) := by simp [hulen]
  have hpre : (u ++ u).take (K + 1 + i + 1) <+: v ++ v :=
    prefix_take_of_leftDist h (by omega)
  have hyi : (v ++ v)[K + 1 + i]? = ((u ++ u).take (K + 1 + i + 1))[K + 1 + i]? :=
    getElem?_of_prefix hpre (by simp; omega)
  have hxp : (u ++ u)[K + 1 + i]? = ((u ++ u).take (K + 1 + i + 1))[K + 1 + i]? :=
    getElem?_of_prefix (List.take_prefix _ _) (by simp; omega)
  rw [← hxp] at hyi
  have hxi : (u ++ u)[K + 1 + i]? = some true := by
    rw [List.getElem?_append_right (by omega)]
    simp only [hulen, Nat.sub_self]
    rw [hu, List.getElem?_append_left (by simp)]
    simp
  have hyj : (v ++ v)[K + 1 + i]? = some false := by
    rw [List.getElem?_append_left (by omega), hv,
      List.getElem?_append_right (by simp)]
    simp [hij]
  rw [hxi, hyj] at hyi
  simp at hyi

/-- **Exercise `exer:duplication-not-rational`.**  String duplication over a two-letter alphabet
is not a rational function.

The author's argument for this exercise: by Theorem `thm:machine-independent-rational-functions` a
rational function has finitely many classes of the relation `BoundedVarRel`, and for duplication
the strings `falseⁿ` are pairwise inequivalent (`not_boundedVarRel_duplicate`), so there are
infinitely many classes.

The same statement is `Transducers.Exercises.not_isRationalFun_duplicate`
(`RequestProject/Exercises/PartBC.lean`), the second item of Exercise `exer:non-rational`, proved
there by the range argument. -/
theorem not_isRationalFun_duplicate_boundedVar :
    ¬ IsRationalFun (fun w : List Bool => w ++ w) := by
  intro hrat
  obtain ⟨-, hfin⟩ := (isRationalFun_iff (fun w : List Bool => w ++ w)).1 hrat
  refine hfin.not_infinite ?_
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ =>
      {w₂ | BoundedVarRel (fun w : List Bool => w ++ w) (List.replicate n false) w₂}) ?_ ?_
  · intro i j hEq
    by_contra hne
    rcases Nat.lt_or_ge i j with hij | hij
    · exact not_boundedVarRel_duplicate hij
        ((Set.ext_iff.1 hEq (List.replicate j false)).2
          (BoundedVarRel.refl (f := fun w : List Bool => w ++ w) _))
    · exact not_boundedVarRel_duplicate (show j < i by omega)
        ((Set.ext_iff.1 hEq (List.replicate i false)).1
          (BoundedVarRel.refl (f := fun w : List Bool => w ++ w) _))
  · intro n
    exact ⟨List.replicate n false, rfl⟩

end Transducers.Exercises
