/-
Expressive completeness of the regular terms for string-to-string functions, from Section
*Combinators* of *Transducers* (M. Bojańczyk).

This is the half of the converse direction of Theorem `thm:regular-terms` that the book states as
"all prime regular string-to-string functions are definable by terms, and hence all regular
string-to-string functions are definable by terms".  `Transducers.IsRegularFun` is by definition
the closure of `Transducers.RegularFam` under composition, and terms are closed under composition,
so all that has to be done is to collect the primes:

* the rational ones, which by Theorem `thm:rational-primes` are compositions of the primes of
  `Transducers.PrimeRationalFam` -- flip-flop Mealy machines (Lemma `lem:terms-define-flip-flop`),
  reversible Mealy machines (Lemma `lem:terms-define-reversible`), their right-to-left variants
  (which the book resolves by string reversal), string homomorphisms (Lemma
  `lem:terms-define-string-homomorphisms`) and the end-marker (Lemma
  `lem:terms-define-append-hash`);
* map reverse and map duplicate (Lemma `lem:terms-define-map-reverse-duplicate`).
-/
import RequestProject.PartC.CombMealyRev
import RequestProject.PartC.CombMapRev
import RequestProject.PartC.RegularDef
import RequestProject.PartB.PrimeRat

namespace Transducers

/-- Every prime rational function is definable by terms. -/
theorem termStrFun_of_primeRational {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : PrimeRationalFam X Y g) : TermStrFun g := by
  haveI := hX
  haveI := hY
  rcases h with hm | hrm | ⟨phi, rfl⟩ | ⟨e, rfl⟩
  · rcases hm with hrev | hff
    · exact terms_define_reversible hX hY hrev
    · exact terms_define_flip_flop hX hY hff
  · have hh : TermStrFun (fun w : List X => (g w.reverse).reverse) := by
      rcases hrm with hrev | hff
      · exact terms_define_reversible hX hY hrev
      · exact terms_define_flip_flop hX hY hff
    refine (((termStrFun_reverse X).comp hh).comp (termStrFun_reverse Y)).congr ?_
    intro w
    simp
  · exact termStrFun_homOf phi
  · exact termStrFun_sep e

/-- Every rational function is definable by terms. -/
theorem termStrFun_of_rational {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : IsRationalFun g) : TermStrFun g := by
  haveI := hX
  haveI := hY
  exact termStrFun_of_compClosure (P := PrimeRationalFam)
    (fun hX' hY' hp => termStrFun_of_primeRational hX' hY' hp)
    ((rational_iff_prime_composition g).1 h) hX hY

/-- Every prime regular function is definable by terms. -/
theorem termStrFun_of_regularFam {X Y : Type} (hX : Finite X) (hY : Finite Y)
    {g : List X → List Y} (h : RegularFam X Y g) : TermStrFun g := by
  rcases h with hrat | ⟨A₀, e, e', hg⟩ | ⟨A₀, e, e', hg⟩
  · exact termStrFun_of_rational hX hY hrat
  · exact termStrFun_of_mapLiftPrime hX e e' (fun _ => List.reverse) (fun _ => rfl)
      (fun k u => by simp) (fun T => tfun_reverse T) hg
  · exact termStrFun_of_mapLiftPrime hX e e' (fun _ => fun u => u ++ u) (fun _ => rfl)
      (fun k u => by simp)
      (fun T => ((tfun_id (.list T)).pair (tfun_id (.list T))).comp (tfun_append T)) hg

/-- **Every regular string-to-string function is definable by a regular term.**  This is the
string-to-string case of the converse direction of Theorem `thm:regular-terms`. -/
theorem termStrFun_of_isRegularFun {X Y : Type} {g : List X → List Y} (h : IsRegularFun g)
    (hX : Finite X) (hY : Finite Y) : TermStrFun g :=
  termStrFun_of_compClosure (P := RegularFam)
    (fun hX' hY' hp => termStrFun_of_regularFam hX' hY' hp) h hX hY

end Transducers
