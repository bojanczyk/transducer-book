# B-effectivity-conditional — COMPLETE

task: 33aa71ea-a67e-4c0a-be30-cc2bbc4a901a
created: 2026-08-21 13:30:43.602592

Picking up from the previous state of `transducer-lean`, where Theorems B.3.3, B.3.4, B.3.7 and B.4.2 were proved from **two** effectivity hypotheses, I removed one of the two: the effective Schützenberger bound is now a theorem, so those four results assume only the computability of comparing the values of two coded weighted automata.

**What is now proved outright (new in this session)**

* `Transducers.effectiveWeightedBound` (in the new `RequestProject/PartB/WeightedBound.lean`) — an effective Schützenberger bound: there is a *primitive recursive* function of two codes of weighted automata over ℚ such that two valid coded automata agreeing on all strings up to that length compute the same function. The explicit bound is `wcodeBound c = 1 + (number of initial states) + Σ over the transitions of 2·(|input| + 1)`.

  The proof: `linRep_eq_of_short` (factored out of `WeightedZero.lean`) gives Schützenberger's criterion with the explicit bound `d₁ + d₂`, the dimensions of two linear representations; the representation produced by the normal-form machinery has one dimension per useful state of `atom (initCopy M)`, and a useful state is either an initial state or the target of a transition, so all of them occur in an explicit list (`coverList`) built from the initial states, the extra state `phi`, and the states `cfg t x` for `t` a lifted or copied transition and `x` a suffix of its input string. `exists_linRep_bounded` packages this as a linear representation of explicitly bounded dimension; since the bound involves no arithmetic on the weights, it is primitive recursive in the code. (`initCopy` was generalised so that it no longer requires a finite state type, which lets the machinery be applied to a coded automaton over ℕ directly.)

**Status of the four numbered results**

* **B.3.3** `weighted_equivalence_decidable`, **B.3.4** `rationalFun_equivalence_decidable`, **B.3.7** `weighted_zeroness_decidable`, **B.4.2** `rationalFun_isMealy_decidable` — each proved from the single explicit hypothesis `EffectiveWeightedEvalEq` of `RequestProject/PartB/Effective.lean` (a computable test of whether two coded weighted automata over ℚ take the same value on a given string), in the style of Theorem B.1.6. Everything else — the bound and now also its effective form, the reduction of equivalence of rational functions to weighted automata, B.3.4 from B.3.3, and the code constructions for prefix preservation in B.4.2 — is discharged in full, with no `sorry` in any dependency. B.4.2 remains relativised to the strings over the alphabet of the code, as documented earlier; the unconditional statements are still kept as commented-out originals with explanatory notes.
* The remaining hypothesis is true in the ordinary mathematical sense (the value is a finite sum of products of rational weights read off the code) but is not derivable inside Mathlib, whose `Primrec`/`Computable` API has no arithmetic on ℤ or ℚ; I did not develop that API, as instructed.

**Verification.** `lake build` succeeds over the whole project (8110 jobs, 0 errors). No file of Part A or Part B contains a `sorry` outside comments. `#print axioms` on `effectiveWeightedBound`, on all four results above, and on B.1.6 and B.4.3 reports only `propext`, `Classical.choice`, `Quot.sound`.

**Still open** (unchanged, faithful statements left as `sorry`): Part C — C.1.4, C.2.5, C.2.8–C.2.11, C.3.2 and most of Section C.4; Part D — D.1.1, D.1.3, D.1.4, D.2.1, D.2.4.

`THEOREMS.md` records all of this: the status column of the four results, the new file, the rewritten subsection on the conditional results (now one hypothesis, with the bound proved), and the `## Status` section. All work is committed and pushed.
