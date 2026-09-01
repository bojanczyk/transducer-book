/-
String reversal is not a rational function.

This is Example `ex:string-reversal-not-rational` of the main text of
*Transducers* (M. Bojańczyk).  Two exercises of the book -- Exercise
`exer:function-that-is-not-rational` and Exercise `exer:not-semiring-continuous` --
use it, and used to take it as an explicit hypothesis, because the example is not
one of the numbered results of the book.  It is proved here, by the author's own
argument, so that both exercises are unconditional.

The argument is the one the book gives: by Theorem
`thm:machine-independent-rational-functions` (`Transducers.isRationalFun_iff`) a
rational function is continuous and its relation `BoundedVarRel` has finite
index, and for reversal no two distinct strings are related, so the index is
infinite.  Only the strings `falseⁿ` are needed to see this, and the alphabet is
`Bool`, which has the two letters the example asks for (over a one-letter
alphabet reversal is the identity, hence rational).
-/
import RequestProject.PartB.WeightedStatements

namespace Transducers.Exercises

open Transducers

/-- **Reversal separates `falseⁱ` from `falseʲ` for `i < j`.**  Extending both on the left by
`true^{K+1}` gives the outputs `falseⁱ true^{K+1}` and `falseʲ true^{K+1}`, which agree only on
the first `i` letters, so their left distance exceeds `K`. -/
lemma not_boundedVarRel_reverse {i j : ℕ} (hij : i < j) :
    ¬ BoundedVarRel (List.reverse : List Bool → List Bool)
      (List.replicate i false) (List.replicate j false) := by
  rintro ⟨K, hK⟩
  have h := hK (List.replicate (K + 1) true)
  set x := (List.replicate (K + 1) true ++ List.replicate i false).reverse with hx
  set y := (List.replicate (K + 1) true ++ List.replicate j false).reverse with hy
  have hxe : x = List.replicate i false ++ List.replicate (K + 1) true := by
    simp [hx, List.reverse_append]
  have hye : y = List.replicate j false ++ List.replicate (K + 1) true := by
    simp [hy, List.reverse_append]
  have hlen : x.length = i + (K + 1) := by simp [hxe]
  have hpre : x.take (i + 1) <+: y := prefix_take_of_leftDist h (by omega)
  have hyi : y[i]? = (x.take (i + 1))[i]? := getElem?_of_prefix hpre (by simp; omega)
  have hxp : x[i]? = (x.take (i + 1))[i]? :=
    getElem?_of_prefix (List.take_prefix _ _) (by simp; omega)
  rw [← hxp] at hyi
  have hxi : x[i]? = some true := by
    rw [hxe, List.getElem?_append_right (by simp)]
    simp
  have hyj : y[i]? = some false := by
    rw [hye, List.getElem?_append_left (by simp; omega)]
    simp [hij]
  rw [hxi, hyj] at hyi
  simp at hyi

/-- **Example `ex:string-reversal-not-rational`.**  String reversal over a two-letter alphabet is
not a rational function.

The author's argument: by Theorem `thm:machine-independent-rational-functions` a rational function
has finitely many classes of the relation `BoundedVarRel`, and for reversal the strings `falseⁿ`
are pairwise inequivalent (`not_boundedVarRel_reverse`), so there are infinitely many classes. -/
theorem not_isRationalFun_reverse :
    ¬ IsRationalFun (List.reverse : List Bool → List Bool) := by
  intro hrat
  obtain ⟨-, hfin⟩ := (isRationalFun_iff (List.reverse : List Bool → List Bool)).1 hrat
  refine hfin.not_infinite ?_
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ =>
      {w₂ | BoundedVarRel (List.reverse : List Bool → List Bool)
        (List.replicate n false) w₂}) ?_ ?_
  · intro i j hEq
    by_contra hne
    rcases Nat.lt_or_ge i j with hij | hij
    · exact not_boundedVarRel_reverse hij
        ((Set.ext_iff.1 hEq (List.replicate j false)).2 (BoundedVarRel.refl _))
    · exact not_boundedVarRel_reverse (show j < i by omega)
        ((Set.ext_iff.1 hEq (List.replicate i false)).1 (BoundedVarRel.refl _))
  · intro n
    exact ⟨List.replicate n false, rfl⟩

end Transducers.Exercises
