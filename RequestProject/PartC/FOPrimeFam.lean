/-
The family of prime first-order regular functions (Theorem C.4.17).

The definition `Transducers.FORegularFam` was originally stated in
`RequestProject/PartC/MSOOpen.lean`, next to Theorem C.4.17; it has been moved
here, unchanged, so that the proof of the easy inclusion of Theorem C.4.17
(compositions of primes are first-order transductions) can be developed before
the statement of the theorem.  `RequestProject/PartC/MSOOpen.lean` imports this
file, so the name `Transducers.FORegularFam` is unchanged.
-/
import RequestProject.PartC.MSODef

namespace Transducers

/-- The family of prime first-order regular functions: first-order rational
functions (equivalently, first-order relabellings), map reverse and map
duplicate. -/
def FORegularFam : ∀ (A B : Type), (List A → List B) → Prop := fun A B f =>
  IsFORelabelling f ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapReverse A₀ (w.map e)).map e'.symm) ∨
  (∃ (A₀ : Type) (e : A ≃ Option A₀) (e' : B ≃ Option A₀),
      ∀ w, f w = (mapDuplicate A₀ (w.map e)).map e'.symm)

end Transducers
