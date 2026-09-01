/-
Exercise `exer:rational-composition-finiteness-undecidable` of the chapter on
rational functions (`rational-functions.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.PartB.Codes

/-!
# Finiteness of the iterates of a rational function is undecidable

Exercise `exer:rational-composition-finiteness-undecidable` asks to show that it
is undecidable whether a rational function `f : A* → A*` generates finitely many
functions under composition, that is whether `{fⁿ : n ∈ ℕ}` is finite.

The solution has three steps.

1. The set of iterates is finite if and only if `fⁿ = fⁿ⁺ᵏ` for some `n` and
   some `k ≥ 1`.  This is proved here in full and for an arbitrary function, as
   `Transducers.Exercises.iterates_finite_iff`.
2. The function that maps a configuration of a fixed Turing machine to the next
   one is rational, and its `n`-th iterate maps a configuration to the
   configuration after `n` steps.
3. The halting problem reduces to finiteness of the set of iterates, through the
   machine which simulates a given machine on a tape of a given length and halts
   as soon as the simulation runs out of space.

Steps 2 and 3 together are a reduction from the halting problem to the problem
of the exercise, carried out on Turing machines; they are taken here as the
single explicit hypothesis `Transducers.Exercises.IteratesReduction`, which says
that some undecidable set reduces computably to the problem.  The undecidability
of the problem then follows in one step
(`Transducers.Exercises.iterates_finiteness_undecidable`), and step 1 — the
mathematical content of the solution — is proved.

As everywhere in this project, the decision problem is stated for *codes* of
automata (`Transducers.RelCode`, `Transducers.DecidableUnderPromise`).  A code
describes a function only on the strings over its own alphabet
(`Transducers.CodeWord`), so a code can be iterated exactly when its outputs are
again strings over that alphabet; this is the promise
`Transducers.Exercises.CodeSelfMap`, and the function that is iterated is the
induced map on the strings over the alphabet of the code.
-/

namespace Transducers.Exercises

open Transducers

/-! ## Finitely many iterates -/

/-- The set of iterates of a function. -/
def iterates {X : Type} (f : X → X) : Set (X → X) := {g | ∃ n, g = f^[n]}

/-- **Step 1 of the solution.**  A function generates finitely many functions under composition
exactly when two of its iterates coincide, that is when its sequence of iterates is eventually
periodic. -/
theorem iterates_finite_iff {X : Type} (f : X → X) :
    (iterates f).Finite ↔ ∃ n k : ℕ, 1 ≤ k ∧ f^[n] = f^[n + k] := by
  constructor
  · intro hfin
    haveI : Finite (iterates f) := hfin.to_subtype
    obtain ⟨n, m, hnm, heq⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨f^[n], ⟨n, rfl⟩⟩ : iterates f))
    have heq' : f^[n] = f^[m] := congrArg Subtype.val heq
    rcases lt_or_gt_of_ne hnm with h | h
    · refine ⟨n, m - n, by omega, ?_⟩
      rw [heq']
      congr 1
      omega
    · refine ⟨m, n - m, by omega, ?_⟩
      rw [← heq']
      congr 1
      omega
  · rintro ⟨n, k, hk, heq⟩
    have key : ∀ m : ℕ, ∃ i < n + k, f^[m] = f^[i] := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
          by_cases hm : m < n + k
          · exact ⟨m, hm, rfl⟩
          · have e1 : f^[m] = f^[m - k - n] ∘ f^[n + k] := by
              rw [← Function.iterate_add]
              congr 1
              omega
            have e2 : f^[m - k] = f^[m - k - n] ∘ f^[n] := by
              rw [← Function.iterate_add]
              congr 1
              omega
            have h1 : f^[m] = f^[m - k] := by rw [e1, e2, heq]
            obtain ⟨i, hi, hii⟩ := ih (m - k) (by omega)
            exact ⟨i, hi, by rw [h1, hii]⟩
    refine Set.Finite.subset (Set.finite_range (fun i : Fin (n + k) => f^[(i : ℕ)])) ?_
    rintro g ⟨m, rfl⟩
    obtain ⟨i, hi, hii⟩ := key m
    exact ⟨⟨i, hi⟩, hii.symm⟩

/-! ## Iterating a coded function -/

/-- A code can be iterated: it describes a function on the strings over its alphabet, and the
outputs are again strings over its alphabet. -/
def CodeSelfMap (c : RelCode) : Prop :=
  CodeFunctional c ∧ ∀ w v, CodeWord c w → codeRel c w v → CodeWord c v

/-- The function that a code describes on the strings over its alphabet. -/
noncomputable def codeSelfFun {c : RelCode} (h : CodeSelfMap c)
    (w : {w : List ℕ // CodeWord c w}) : {w : List ℕ // CodeWord c w} :=
  ⟨(h.1 w.1 w.2).choose, h.2 w.1 _ w.2 (h.1 w.1 w.2).choose_spec.1⟩

/-- The problem of the exercise: the function described by a code generates finitely many
functions under composition. -/
def CodeIteratesFinite (c : RelCode) : Prop :=
  ∀ h : CodeSelfMap c, (iterates (codeSelfFun h)).Finite

/-- **Assumed: the reduction from the halting problem.**

Some undecidable set of natural numbers reduces computably to the problem of the exercise: there
is a computable map from natural numbers to codes, all of them iterable, such that the set of
iterates of the coded function is finite exactly for the elements of that set.

*Why this is true.*  This is steps 2 and 3 of the solution of
`exer:rational-composition-finiteness-undecidable`.  A configuration of a Turing machine is
encoded as the contents of the tape with the state inserted at the position of the head; for a
fixed machine, the map taking a configuration to the next one is computed by a bimachine, which
copies the input except at the two positions next to the state, and leaves unchanged the strings
that do not encode a configuration.  Its `n`-th iterate maps a configuration to the configuration
after `n` steps, so by step 1 the set of iterates is finite exactly when the behaviour of the
machine on *every* configuration becomes periodic after a bounded number of steps — for a machine
that stays in its halting configuration and never repeats a configuration, exactly when every
configuration halts within a bounded number of steps.  Given a machine `M` and an input `x`, the
machine which simulates `M` on `x` on a tape of length `m` and halts as soon as the simulation
would need more than `m` cells has that property if and only if `M` halts on `x`: if `M` halts,
the bound does not depend on `m`, and if it does not, the number of steps before the simulation
runs out of space grows with `m`.  The undecidable set is the halting set, and the map from
`(M, x)` to the code of the corresponding bimachine is computable.

*Why it is not available here.*  Carrying this out means formalising Turing machines, their
configurations, the space-bounded simulation and the undecidability of halting, and turning the
bimachine of step 2 into a code with a `Computable` proof.  None of this is in the project; as
with the other undecidability results of the book, which take the undecidability of the Post
correspondence problem as an explicit hypothesis, the reduction is assumed and everything on this
side of it — step 1 and the transport of undecidability along the reduction — is proved. -/
def IteratesReduction : Prop :=
  ∃ (H : Set ℕ) (red : ℕ → RelCode),
    (¬ ∃ D : ℕ → Bool, Computable D ∧ ∀ e, (D e = true ↔ e ∈ H)) ∧
    Computable red ∧ ∀ e, CodeSelfMap (red e) ∧ (CodeIteratesFinite (red e) ↔ e ∈ H)

/-- **Exercise `exer:rational-composition-finiteness-undecidable`.**  It is undecidable whether a
rational function generates finitely many functions under composition: there is no computable
procedure which, given a code that can be iterated, decides whether the set of iterates of the
coded function is finite.

The hypothesis is `IteratesReduction`, the reduction from the halting problem of the book; see
its docstring.  The mathematical step of the solution, that the set of iterates is finite exactly
when two iterates coincide, is proved as `iterates_finite_iff`. -/
theorem iterates_finiteness_undecidable (hred : IteratesReduction) :
    ¬ DecidableUnderPromise CodeSelfMap CodeIteratesFinite := by
  rintro ⟨D, hDcomp, hD⟩
  obtain ⟨H, red, hH, hredComp, hspec⟩ := hred
  refine hH ⟨fun e => D (red e), hDcomp.comp hredComp, fun e => ?_⟩
  rw [hD (red e) (hspec e).1]
  exact (hspec e).2

end Transducers.Exercises
