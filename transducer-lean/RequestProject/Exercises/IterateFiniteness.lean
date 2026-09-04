/-
Exercise `exer:rational-composition-finiteness-undecidable` of the chapter on
rational functions (`rational-functions.tex`) of *Transducers* (M. Bojańczyk).
-/
import RequestProject.PartB.Codes
import RequestProject.Acceptance.Basic

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

/-- The pointwise form of `iterates_finite_iff`: what finiteness of the set of iterates asks for
is that two iterates agree *at every point*, with the two exponents `n` and `n + k` chosen
once and for all — a bound on the length of the orbit of every point that is uniform in the
point. -/
theorem iterates_finite_iff_forall {X : Type} (f : X → X) :
    (iterates f).Finite ↔ ∃ n k : ℕ, 1 ≤ k ∧ ∀ x, f^[n] x = f^[n + k] x := by
  rw [iterates_finite_iff]
  constructor
  · rintro ⟨n, k, hk, h⟩
    exact ⟨n, k, hk, fun x => by rw [h]⟩
  · rintro ⟨n, k, hk, h⟩
    exact ⟨n, k, hk, funext h⟩

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

/-- The problem of the exercise, spelled out: the orbit of *every* string over the alphabet of
the code becomes periodic, after a number of steps and with a period that do not depend on the
string.  It is this uniformity over all strings — not merely over the strings reachable from
some distinguished one — that the reduction of the exercise has to produce; see the docstring
of `IteratesReduction`. -/
theorem codeIteratesFinite_iff_uniform {c : RelCode} (h : CodeSelfMap c) :
    CodeIteratesFinite c ↔ ∃ n k : ℕ, 1 ≤ k ∧ ∀ w : {w : List ℕ // CodeWord c w},
      (codeSelfFun h)^[n] w = (codeSelfFun h)^[n + k] w := by
  rw [← iterates_finite_iff_forall]
  exact ⟨fun H => H h, fun H _ => H⟩

/-- **A sufficient condition for the answer to be yes.**  If the outputs of a code that can be
iterated are bounded in length, then the set of iterates is finite: after one step everything
lies in the finite set of strings over the alphabet of the code of length at most the bound, and
the iterates of a map of a finite set into itself are eventually periodic.

So a code whose set of iterates is infinite must have outputs of unbounded length: the dynamics
of the exercise can only be nontrivial on strings of unbounded length. -/
theorem codeIteratesFinite_of_output_length_le {c : RelCode} (h : CodeSelfMap c) (B : ℕ)
    (hB : ∀ w : {w : List ℕ // CodeWord c w}, (codeSelfFun h w).1.length ≤ B) :
    CodeIteratesFinite c := by
  classical
  intro h'
  -- the strings over the alphabet of the code of length at most `B` form a finite set
  have hT : {l : List ℕ | (∀ x ∈ l, x ∈ codeAlphabet c) ∧ l.length ≤ B}.Finite := by
    have hfin : {L : List {x // x ∈ codeAlphabet c} | L.length ≤ B}.Finite :=
      List.finite_length_le _ _
    refine Set.Finite.subset (hfin.image (fun L => L.map Subtype.val)) ?_
    rintro l ⟨hl, hlen⟩
    exact ⟨l.attach.map (fun p => ⟨p.1, hl p.1 p.2⟩), by simpa using hlen, by simp⟩
  have hS : {w : {w : List ℕ // CodeWord c w} | w.1.length ≤ B}.Finite := by
    refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    refine hT.subset ?_
    rintro l ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  haveI : Finite {w : {w : List ℕ // CodeWord c w} // w.1.length ≤ B} := hS.to_subtype
  -- the map induced on that finite set
  set F : {w : {w : List ℕ // CodeWord c w} // w.1.length ≤ B} →
      {w : {w : List ℕ // CodeWord c w} // w.1.length ≤ B} :=
    fun w => ⟨codeSelfFun h w.1, hB w.1⟩ with hF
  have hiter : ∀ (n : ℕ) (w : {w : {w : List ℕ // CodeWord c w} // w.1.length ≤ B}),
      (F^[n] w).1 = (codeSelfFun h)^[n] w.1 := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
        intro w
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
  obtain ⟨n, m, hnm, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => F^[n])
  have key : ∀ n m : ℕ, F^[n] = F^[m] →
      (codeSelfFun h)^[n + 1] = (codeSelfFun h)^[m + 1] := by
    intro n m hnm
    funext w
    have h1 : (codeSelfFun h)^[n + 1] w
        = (F^[n] ⟨codeSelfFun h w, hB w⟩).1 := by
      rw [hiter]
      rw [Function.iterate_succ_apply]
    have h2 : (codeSelfFun h)^[m + 1] w
        = (F^[m] ⟨codeSelfFun h w, hB w⟩).1 := by
      rw [hiter]
      rw [Function.iterate_succ_apply]
    rw [h1, h2, hnm]
  rw [iterates_finite_iff]
  rcases lt_or_gt_of_ne hnm with hlt | hlt
  · refine ⟨n + 1, m - n, by omega, ?_⟩
    rw [key n m heq]
    congr 1
    omega
  · refine ⟨m + 1, n - m, by omega, ?_⟩
    rw [key m n heq.symm]
    congr 1
    omega

/-- **Assumed: the reduction from the halting problem.**

Some undecidable set of natural numbers reduces computably to the problem of the exercise: there
is a computable map from natural numbers to codes, all of them iterable, such that the set of
iterates of the coded function is finite exactly for the elements of that set.

*What the reduction has to produce.*  This is steps 2 and 3 of the solution of
`exer:rational-composition-finiteness-undecidable`.  A configuration of a Turing machine is
encoded as the contents of the tape with the state inserted at the position of the head; for a
fixed machine, the map taking a configuration to the next one is computed by a bimachine, which
copies the input except at the two positions next to the state, and leaves unchanged the strings
that do not encode a configuration.  Its `n`-th iterate maps a configuration to the configuration
after `n` steps, so by step 1 the set of iterates is finite exactly when the behaviour of the
machine becomes periodic after a bounded number of steps.

*The point at which the usual sketch is incomplete.*  A code describes a function on **all**
strings over its alphabet, so `codeSelfFun` is iterated on all of `A*` and, by
`codeIteratesFinite_iff_uniform`, finiteness of the set of iterates asks for one pair `n`, `k`
that works for *every* string at once.  Every string encodes some configuration, whether or not
it is reachable from the initial one, and there is no way for a rational function to tell the
two apart: the set of strings that are still alive after `t` steps is regular, and a regular
set of "alive" strings cannot single out the reachable configurations.  So what a reduction has
to deliver is not that the machine halts on the runs that start from an initial configuration,
but that it halts on *every* configuration within a bound that does not depend on the length of
the tape — uniform mortality.  In particular the reduction has to go in the direction "machine
halts ↦ iterates finite": finiteness of the set of iterates is a `∃`-statement over the pairs
`n`, `k` (equality of two rational functions being decidable, by Theorem
`thm:equivalence-rational-functions`), hence semi-decidable, so the undecidable set that reduces
to it must be a semi-decidable one such as `Acceptance.ATM`, not its complement.

The sketch of the solution — simulate `M` on `x` on a tape of length `m` and halt when the
simulation runs out of space — bounds only the runs that start from the initial configuration on
a tape of length `m`.  A configuration in which the tape carries arbitrary contents and the head
sits in an arbitrary place is not on such a run, and its own run can be long: the number of steps
before it repeats or halts is bounded only by the number of configurations of a tape of length
`m`, which grows with `m`.  So the sketch does not give the uniform bound that
`codeIteratesFinite_iff_uniform` asks for, and restricting the strings that are kept alive does
not repair it: the strings alive after `t` steps always form a regular set, the configurations
reachable from a fixed one are not a regular set, so any such restriction still keeps alive
configurations that are not reachable — whose orbits then have to be bounded as well, which is
the same uniform mortality requirement over again.

Uniform mortality of a machine over *all* its configurations, being equivalent to halting, is the
subject of Hooper's immortality theorem, and the known constructions of families of uniformly
mortal machines go through aperiodic tilings and the undecidability of the domino problem.  The
same is true of the corresponding question for length-preserving invertible transducers, the
order problem for automaton groups.  Nothing of that machinery is in this project, and building
it is a project of its own; that, and not the absence of an undecidable set, is why the reduction
is still assumed.  The set is available: `Acceptance.ATM` is undecidable outright
(`Acceptance.atm_not_turingDecidable`), and in the form in which this hypothesis needs it, it is
`atm_no_bool_decider` below.  What remains is exactly the computable map `red`, by
`iteratesReduction_of_atm_reduction`, and nothing about codes is missing for it:
`RequestProject/Exercises/SequentialCodes.lean` builds the code of an arbitrary sequential
transducer, proves the promise for it and identifies its iterates, so that
`iteratesReduction_of_seq_family` reduces this hypothesis to a statement about a primitive
recursive family of finite transition tables. -/
def IteratesReduction : Prop :=
  ∃ (H : Set ℕ) (red : ℕ → RelCode),
    (¬ ∃ D : ℕ → Bool, Computable D ∧ ∀ e, (D e = true ↔ e ∈ H)) ∧
    Computable red ∧ ∀ e, CodeSelfMap (red e) ∧ (CodeIteratesFinite (red e) ↔ e ∈ H)

/-- The undecidable set that the reduction is meant to use, in the form in which
`IteratesReduction` asks for it: no computable `Bool`-valued function decides membership in the
acceptance problem `Acceptance.ATM`.  This is `Acceptance.atm_not_turingDecidable` read through
`Acceptance.turingDecidable_iff_computablePred`. -/
theorem atm_no_bool_decider :
    ¬ ∃ D : ℕ → Bool, Computable D ∧ ∀ e, (D e = true ↔ e ∈ Acceptance.ATM) := by
  rintro ⟨D, hD, hDspec⟩
  refine Acceptance.atm_not_turingDecidable ?_
  rw [Acceptance.turingDecidable_iff_computablePred, ComputablePred.computable_iff]
  exact ⟨D, hD, funext fun e => propext (hDspec e).symm⟩

/-- Everything in `IteratesReduction` except the construction of the codes: a computable map from
natural numbers to iterable codes whose iterates are finite exactly on the acceptance problem
`Acceptance.ATM` gives the hypothesis.  This isolates what is missing — the map `red` — from what
is proved: the undecidability of the set, and the transport of it along the reduction. -/
theorem iteratesReduction_of_atm_reduction (red : ℕ → RelCode) (hcomp : Computable red)
    (hspec : ∀ e, CodeSelfMap (red e) ∧ (CodeIteratesFinite (red e) ↔ e ∈ Acceptance.ATM)) :
    IteratesReduction :=
  ⟨Acceptance.ATM, red, atm_no_bool_decider, hcomp, hspec⟩

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
