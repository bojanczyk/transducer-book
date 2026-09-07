/-
Expressive completeness of the rational terms for string-to-string functions, the string-to-string
half of the converse direction of Theorem `thm:rational-terms` of *Transducers* (M. Bojańczyk).

`Transducers.IsRationalFun` is the closure under composition of the prime rational functions, and
the rational terms are closed under composition, so all that has to be done is to collect the
primes.  The book's list (Theorem `thm:rational-primes`) contains the *right-to-left* variants of
the prime Mealy machines, and the regular case disposes of those by string reversal -- which is
not available here.  Exercise `exer:no-reverse-reversible`, formalised in
`RequestProject/Exercises/NoReverseReversible.lean`, is exactly what is needed: it shows that the
right-to-left *reversible* machines may be dropped from the list, and the right-to-left flip-flop
machines are handled directly by `Transducers.rat_terms_define_flip_flop_rtl`.
-/
import RequestProject.PartC.RatMealyRev
import RequestProject.Exercises.NoReverseReversible

namespace Transducers

/-- Every prime of the shortened list of Exercise `exer:no-reverse-reversible` is definable by a
rational term. -/
theorem ratTermStrFun_of_primeRatNoRevRev {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : Exercises.PrimeRatNoRevRevFam X Y g) : RatTermStrFun g := by
  haveI := hX
  haveI := hY
  rcases h with hm | hff | ⟨phi, rfl⟩ | ⟨e, rfl⟩
  · rcases hm with hrev | hff
    · exact rat_terms_define_reversible hX hY hrev
    · exact rat_terms_define_flip_flop hX hY hff
  · exact rat_terms_define_flip_flop_rtl hX hY hff
  · exact ratTermStrFun_homOf phi
  · exact ratTermStrFun_sep e

/-- **Every rational string-to-string function is definable by a rational term.** -/
theorem ratTermStrFun_of_isRationalFun {X Y : Type} {g : List X → List Y} (hX : Finite X)
    (hY : Finite Y) (h : IsRationalFun g) : RatTermStrFun g := by
  haveI := hX
  haveI := hY
  exact ratTermStrFun_of_compClosure (P := Exercises.PrimeRatNoRevRevFam)
    (fun hX' hY' hp => ratTermStrFun_of_primeRatNoRevRev hX' hY' hp)
    ((Exercises.rational_primes_no_reverse_reversible g).1 h) hX hY

end Transducers
