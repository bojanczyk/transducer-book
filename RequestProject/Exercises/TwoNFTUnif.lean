/-
Exercise `exer:2nft-uniformise` of the chapter *Two-way transducers* (`2dfa.tex`) of
*Transducers* (M. Bojańczyk).

The exercise asks to show that both nondeterministic models of Exercise `exer:2nft` can be
uniformised by deterministic two-way transducers: a *total* relation recognised by one of the two
models contains a function computed by a deterministic two-way transducer.

This file has the second model, the one whose nondeterminism is a labelling of the input by an
auxiliary alphabet subject to a regular condition.  The solution of the book is followed:

* the pairs `(input string, a valid labelling of it)` form a rational relation, because the valid
  labellings form a regular language (Lemma `lem:guess-and-check`, here in the form
  `Transducers.isRationalRel_of_regular_proj`);
* one further conjunct is added to the regular condition, namely that the deterministic two-way
  transducer of the model *halts* on the labelling -- a regular condition by Exercise
  `exer:2dfa-loop-elimination` (`Transducers.Exercises.halts_isRegular`).  This is what makes the
  relation total: a labelling witnessing `R w v` does make the transducer halt;
* Lemma `lem:uniformisation` (`Transducers.exists_rationalFun_of_total_rel`) turns the total
  rational relation into a rational function choosing one valid labelling for each input;
* the deterministic two-way transducer of the model is applied to the result.  It halts on every
  chosen labelling, so its halting completion (`Transducers.TwoWay.exists_regularFun_of_twoWay`)
  computes the same thing there and is a *total* regular function; regular functions are closed
  under composition and contain the rational ones.

The first model is not treated here; see `EXERCISES.md`.
-/
import RequestProject.Exercises.TwoNFT
import RequestProject.Exercises.TwoDFALoop
import RequestProject.PartD.TwoWayTotal
import RequestProject.PartB.GuessCheck
import RequestProject.PartB.UniformFun

namespace Transducers.Exercises

open Transducers

/-- Reading the first component of each letter is the homomorphism `homOf` of the map that sends a
letter to the one-letter string of its first component. -/
private lemma homOf_fst {A C : Type} (z : List (A × C)) :
    homOf (fun p : A × C => [p.1]) z = z.map Prod.fst := by
  induction z with
  | nil => rfl
  | cons p z ih =>
      rw [homOf, List.map_cons, List.flatten_cons, ← homOf, ih, List.singleton_append,
        List.map_cons]

/-- **Exercise `exer:2nft-uniformise`, second model.**  A total relation recognised by the second
nondeterministic model contains the graph of a regular function -- that is, of a function computed
by a deterministic two-way transducer.  (Over finite alphabets `IsRegularFun` and `IsTwoWay` are
the same thing, by `Transducers.twoWay_iff_regular`.) -/
theorem exists_isRegularFun_uniformising_isTwoNFT₂ {A B : Type} [Finite A] [Finite B]
    {R : List A → List B → Prop} (hR : IsTwoNFT₂ R) (htot : ∀ w, ∃ v, R w v) :
    ∃ f : List A → List B, IsRegularFun f ∧ ∀ w, R w (f w) := by
  classical
  obtain ⟨C, hC, Q, hQ, M, L, hL, hRM⟩ := hR
  haveI : Finite C := hC
  haveI : Finite Q := hQ
  -- the labellings that satisfy the regular condition and on which `M` halts
  have hL' : Language.IsRegular {z : List (A × C) | z ∈ L ∧ z ∈ {z | Halts M z}} :=
    RegAut.isRegular_and hL (halts_isRegular M)
  have hrat : IsRationalRel (fun (w : List A) (z : List (A × C)) =>
      z ∈ {z : List (A × C) | z ∈ L ∧ z ∈ {z | Halts M z}} ∧
        homOf (fun p : A × C => [p.1]) z = w) :=
    isRationalRel_of_regular_proj _ hL'
  have htotal : ∀ w : List A, ∃ z : List (A × C),
      z ∈ {z : List (A × C) | z ∈ L ∧ z ∈ {z | Halts M z}} ∧
        homOf (fun p : A × C => [p.1]) z = w := by
    intro w
    obtain ⟨v, hv⟩ := htot w
    obtain ⟨z, hzw, hzL, hzM⟩ := (hRM w v).1 hv
    exact ⟨z, ⟨hzL, ⟨v, hzM⟩⟩, by rw [homOf_fst, hzw]⟩
  obtain ⟨g, hgrat, hg⟩ := exists_rationalFun_of_total_rel hrat htotal
  obtain ⟨F, hFreg, hF⟩ := TwoWay.exists_regularFun_of_twoWay M
  refine ⟨fun w => F (g w), (IsRegularFun.of_rational hgrat).comp hFreg, fun w => ?_⟩
  obtain ⟨⟨hgL, v, hv⟩, hgw⟩ := hg w
  refine (hRM w (F (g w))).2 ⟨g w, ?_, hgL, ?_⟩
  · rw [← homOf_fst, hgw]
  · rw [hF _ _ hv]
    exact hv

end Transducers.Exercises
