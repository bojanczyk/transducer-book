/-
From `Ω(n^k)` outputs to the sorted-identity function: the second step of the author's solution to
Exercise `exer:polynomial-ideals` of *Transducers* (M. Bojańczyk).
-/
import RequestProject.Exercises.SortedPattern
import RequestProject.Exercises.PartBC

/-!
# From `Ω(n^k)` outputs to the sorted identity

If a rational function `f` has `Ω(n^k)` outputs then `sortedFun k` is a rational pre-composition
and post-composition of `f`.  This is the second step of the author's solution to Exercise
`exer:polynomial-ideals`, and it is proved here from the loop analysis:

* by `Transducers.Exercises.rationalFun_chain_words`, either the identity of `{0,1}*` is already a
  rational pre- and post-composition of `f` — and then so is `sortedFun k`, because an arbitrary
  finite alphabet is encoded by blocks over `{0,1}` — or the range of `f` contains a `k`-pattern,
  the words `us 0 · (xs 0)^{c_1} · us 1 ⋯ us k`;
* in the second case, `Transducers.Exercises.patEmit` is a rational function that turns a sorted
  word `a_1^{c_1} ⋯ a_k^{c_k}` into the word of the pattern with those exponents, and it is
  injective on the sorted words; a rational section of it (the Uniformisation Lemma
  `lem:uniformisation`, through `Transducers.Exercises.exists_rationalFun_section`), followed by
  `sortedFun k`, reads the sorted word back.
-/

namespace Transducers.Exercises

open Transducers

/-- **From `Ω(n^k)` outputs to the sorted identity.**  If a rational function `f` has `Ω(n^k)`
outputs then `sortedFun k` is a rational pre-composition and post-composition of `f`. -/
theorem exists_rational_sorted_of_omega {A B : Type} [Finite A] [Finite B] {f : List A → List B}
    (hf : IsRationalFun f) (k : ℕ) {c N : ℕ} (hc : 0 < c)
    (hΩ : ∀ n, N ≤ n → (n + 1) ^ k ≤ c * (f '' {w : List A | w.length ≤ n}).ncard) :
    ∃ (g : List (Fin k) → List A) (h : List B → List (Fin k)),
      IsRationalFun g ∧ IsRationalFun h ∧ ∀ u : List (Fin k), h (f (g u)) = sortedFun k u := by
  classical
  rcases rationalFun_chain_words hf hc hΩ with ⟨g₀, h₀, hg₀, hh₀, hid⟩ | ⟨us, xs, -, hmem, hinj⟩
  · -- the identity of `{0,1}*` is already there: encode `Fin k` by blocks over `{0,1}`
    have hdec : IsRationalFun
        (fun b : List Bool => sortedFun k (TwoLetter.decBlock (Fin k) b)) :=
      isRationalFun_comp TwoLetter.isRationalFun_decBlock (isRationalFun_sortedFun k)
    refine ⟨fun u => g₀ (homOf TwoLetter.code u),
      fun v => sortedFun k (TwoLetter.decBlock (Fin k) (h₀ v)),
      isRationalFun_comp (isRationalFun_homOf TwoLetter.code) hg₀,
      isRationalFun_comp (f := h₀)
        (g := fun b : List Bool => sortedFun k (TwoLetter.decBlock (Fin k) b)) hh₀ hdec,
      fun u => ?_⟩
    show sortedFun k (TwoLetter.decBlock (Fin k) (h₀ (f (g₀ (homOf TwoLetter.code u)))))
        = sortedFun k u
    rw [hid (homOf TwoLetter.code u), TwoLetter.decBlock_homOf_code]
  · -- the range of `f` contains a `k`-pattern
    set enc : List (Fin k) → List B := fun u => patEmit us xs k (sortedFun k u) with henc
    have hencrat : IsRationalFun enc :=
      isRationalFun_comp (isRationalFun_sortedFun k) (isRationalFun_patEmit us xs k)
    have hencmem : ∀ u : List (Fin k), ∃ w : List A, f w = enc u := by
      intro u
      rw [henc]
      simp only
      rw [patEmit_sorted us xs k (sortedFun_sorted u)]
      exact hmem _
    obtain ⟨sec, hsecrat, hsec⟩ := exists_rationalFun_section hf
    obtain ⟨d, hdrat, hd⟩ := exists_rationalFun_section hencrat
    refine ⟨fun u => sec (enc u), fun v => sortedFun k (d v),
      isRationalFun_comp hencrat hsecrat,
      isRationalFun_comp hdrat (isRationalFun_sortedFun k), fun u => ?_⟩
    have hfg : f (sec (enc u)) = enc u := hsec _ ((hencmem u).imp fun _ h => h.symm)
    rw [hfg]
    have hdu : enc (d (enc u)) = enc u := hd _ ⟨u, rfl⟩
    rw [henc] at hdu
    simp only at hdu
    exact patEmit_injOn_sorted us xs k hinj (sortedFun_sorted _) (sortedFun_sorted u) hdu

end Transducers.Exercises
