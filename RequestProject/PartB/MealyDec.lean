/-
Theorem B.4.2 of *Transducers* (M. Bojańczyk): one can decide whether a rational
function is computed by a Mealy machine.

By Theorem B.4.1 a function is computed by a Mealy machine exactly when it is
continuous, prefix preserving and length preserving, and a rational function is
automatically continuous (Theorem B.1.5, used through Theorem B.2.7 in
`RequestProject/PartB/CodeRat.lean`).  Length preservation is decided by
Lemma B.4.3 (`RequestProject/PartB/LenDec.lean`), and prefix preservation of a
length preserving function is the equality

  `dropLast (f w) = f (dropLast w)`

of two rational functions, for which `RequestProject/PartB/PrefixCodes.lean`
builds codes; the equality is decided by Theorem B.3.4.
-/
import RequestProject.PartB.CodeRat
import RequestProject.PartB.RatEqDec

namespace Transducers
namespace MealyDec

open PrefixCodes CodeRat

/-- The decision procedure for Theorem B.4.2, built from a decision procedure
`D` for equivalence of coded rational functions (Theorem B.3.4). -/
def mealyDecB (D : RelCode × RelCode → Bool) (c : RelCode) : Bool :=
  LenDec.lenDec c && D (dropCode c, shiftCode c)

lemma mealyDecB_iff {D : RelCode × RelCode → Bool}
    (hD : ∀ p : RelCode × RelCode, CodeFunctional p.1 → CodeFunctional p.2 →
      (D p = true ↔ codeRel p.1 = codeRel p.2))
    {c : RelCode} (hc : CodeFunctional c) :
    mealyDecB D c = true ↔
      (∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) := by
  rw [mealyProperty_iff hc, isMealy_codeFun_iff hc, mealyDecB, Bool.and_eq_true,
    LenDec.lenDec_iff]
  constructor
  · rintro ⟨hlen, hd⟩
    exact ⟨hlen, (prefixCrit_iff hc hlen).2
      (hD _ (codeFunctional_dropCode hc) (codeFunctional_shiftCode hc) |>.1 hd)⟩
  · rintro ⟨hlen, hpre⟩
    refine ⟨hlen, ?_⟩
    exact (hD _ (codeFunctional_dropCode hc) (codeFunctional_shiftCode hc)).2
      ((prefixCrit_iff hc hlen).1 hpre)

lemma computable_mealyDecB {D : RelCode × RelCode → Bool} (hD : Computable D) :
    Computable (mealyDecB D) := by
  have h1 : Computable (fun c : RelCode => LenDec.lenDec c) := LenDec.computable_lenDec
  have h2 : Computable (fun c : RelCode => D (dropCode c, shiftCode c)) :=
    hD.comp (Computable.pair primrec_dropCode.to_comp primrec_shiftCode.to_comp)
  exact (Primrec.and.to_comp.comp h1 h2).of_eq (fun _ => rfl)

end MealyDec

/-- **Theorem B.4.2** from the effectivity hypotheses of
`RequestProject/PartB/Effective.lean`: one can decide whether a rational
function is computed by a Mealy machine. -/
theorem rationalFun_isMealy_decidable_aux
    (hEval : EffectiveWeightedEvalEq) (hBound : EffectiveWeightedBound) :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) := by
  obtain ⟨D, hDcomp, hD⟩ := rationalFun_equivalence_decidable_aux hEval hBound
  exact ⟨MealyDec.mealyDecB D, MealyDec.computable_mealyDecB hDcomp,
    fun c hc => MealyDec.mealyDecB_iff (fun p hp₁ hp₂ => hD p ⟨hp₁, hp₂⟩) hc⟩

end Transducers
