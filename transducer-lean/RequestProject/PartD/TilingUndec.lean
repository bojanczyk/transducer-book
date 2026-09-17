/-
Part D, Section *A functional programming language*: Lemma `lem:tiling` and Theorem
`thm:undecidability-higher-order`.

The two halves of the reduction of the acceptance problem to the tiling problem are proved in
`RequestProject/PartD/TilingSound.lean` (a solution gives an accepting computation) and
`RequestProject/PartD/TilingComplete.lean` (an accepting computation gives a solution), and
`RequestProject/PartD/TilingPrimrec.lean` shows that the instance
`Transducers.TilingRed.inst M w` is a primitive recursive function of the machine and the input
word.  Putting the three together gives Lemma `lem:tiling`: the tiling problem is undecidable.

Composing that with the reduction of Lemma `lem:tiling-checker`
(`Transducers.HOTile.checkTerm_eq_falseTerm_iff`: the term that checks a solution has the same
semantics as the constant `false` term exactly when the instance has no solution) gives Theorem
`thm:undecidability-higher-order`.

Two points about the second statement are recorded in `THEOREMS.md` as well.

* **What the decision procedure reads.**  The terms of Definition `def:higher-order-terms` are
  intrinsically typed (`Transducers.HTerm`), and the project has no encoding of them as a piece of
  data; so the equivalence problem cannot be stated here as a predicate on *codes of terms*.  It is
  stated instead on the data from which the two terms are built: the instance `I` of the tiling
  problem determines the pair of closed terms `Transducers.HOTile.checkTerm I` and
  `Transducers.HOTile.falseTerm I.maxTile` of the common type
  `1* × ((1* × 1*) → T) → (1 + 1)`, and no algorithm decides, reading `I`, whether the two have
  the same semantics.  A decision procedure reading a code of the two terms would give one
  reading `I`, for any encoding of the terms under which the map `I ↦ (code, code)` is computable;
  the statement below is the one that can be made without fixing such an encoding.
* **Well-formedness.**  `Transducers.HOTile.checkTerm_eq_falseTerm_iff` assumes the instance well
  formed (`Transducers.Tiling.Instance.WF`), and the instances produced by the reduction are
  (`Transducers.TilingRed.wf_inst`), so the reduction goes through.
-/
import RequestProject.PartD.TilingPrimrec
import RequestProject.PartD.TilingSound
import RequestProject.PartD.TilingComplete
import RequestProject.PartD.HOTiling
import RequestProject.Acceptance.Bridge

open PCP

namespace Transducers
namespace TilingRed

variable (M : _root_.PCP.TM) (w : List ℕ)

/-! ## The instance of the reduction is well formed -/

/-- The tile of the corner `(0,0)` is a cell of the machine. -/
lemma validB_startTile : validB M w (startTile M) = true := by
  apply validB_intro <;> simp [startTile, TM.states]

/-- The tile of the corner `(n,n)` is a cell of the machine. -/
lemma validB_finalTile : validB M w finalTile = true := by
  apply validB_intro <;> simp [finalTile, M.blank_mem_tapeSyms]

private lemma inst_maxTile : (inst M w).maxTile = maxCode M w := by rw [inst]

private lemma inst_s : (inst M w).s = Encodable.encode (startTile M) := by rw [inst]

private lemma inst_t : (inst M w).t = Encodable.encode finalTile := by rw [inst]

/-- **The instance built from a machine and an input word is well formed**: its two corner tiles
and all the tiles of its local constraint are tiles of the instance. -/
lemma wf_inst : (inst M w).WF where
  s_le := by
    rw [inst_s, inst_maxTile]
    exact le_maxCode (mem_allCells (validB_startTile M w))
  t_le := by
    rw [inst_t, inst_maxTile]
    exact le_maxCode (mem_allCells (validB_finalTile M w))
  constraint_le := by
    intro c hc
    rw [inst] at hc
    simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hc
    obtain ⟨a, ha, b, hb, c', hc', d, ⟨hd, -⟩, rfl⟩ := hc
    rw [inst_maxTile]
    exact ⟨le_maxCode ha, le_maxCode hb, le_maxCode hc', le_maxCode hd⟩

/-! ## The tiling problem is undecidable -/

/-- The instance of the tiling problem has a solution exactly when the machine accepts the input
word. -/
theorem solvable_inst_iff : Tiling.Solvable (inst M w) ↔ M.Accepts w :=
  ⟨accepts_of_solvable, solvable_of_accepts M w⟩

end TilingRed

/-- **Lemma `lem:tiling`.**  The tiling problem is undecidable: no algorithm decides whether an
instance has a solution.

The reduction is the classical one, and is the book's: the rows of the square grid are the
successive configurations of a Turing machine, and the corner `(n,n)` represents acceptance.  The
machines are the tape machines of `RequestProject/PCP/TuringMachine.lean`, whose acceptance
problem is undecidable (`Acceptance.tm_acceptance_not_computablyDecidable`). -/
theorem tiling_undecidable : ¬ ComputablePred Tiling.Solvable := by
  intro h
  rw [ComputablePred.computable_iff] at h
  obtain ⟨g, hg, hgspec⟩ := h
  refine Acceptance.tm_acceptance_not_computablyDecidable
    ⟨fun p => g (TilingRed.inst p.1 p.2), hg.comp TilingRed.primrec_inst.to_comp, fun p => ?_⟩
  exact (Iff.of_eq (congrFun hgspec (TilingRed.inst p.1 p.2))).symm.trans
    (TilingRed.solvable_inst_iff p.1 p.2)

/-- **Theorem `thm:undecidability-higher-order`.**  The equivalence problem for higher-order
polyregular terms is undecidable.

For an instance `I` of the tiling problem, `Transducers.HOTile.checkTerm I` and
`Transducers.HOTile.falseTerm I.maxTile` are two closed higher-order polyregular terms of the same
type `1* × ((1* × 1*) → T) → (1 + 1)`, built uniformly from `I`; by Lemma `lem:tiling-checker` they
have the same semantics exactly when `I` has no solution.  The theorem says that no algorithm
decides, given `I`, whether the two terms are equivalent -- so equivalence is undecidable already
for terms of this shape, which input a function and are therefore not covered by Open problem
`open:polyregular-equivalence`.

The decision problem is stated on the data `I` from which the two terms are built rather than on
codes for the terms themselves, because the terms of Definition `def:higher-order-terms` are
intrinsically typed here and the project has no encoding of them as data; see the header of
`RequestProject/PartD/TilingUndec.lean` and `THEOREMS.md`. -/
theorem undecidability_higherOrder :
    ¬ ComputablePred fun I : Tiling.Instance =>
      (HOTile.checkTerm I).eval HEnv.nil = (HOTile.falseTerm I.maxTile).eval HEnv.nil := by
  intro h
  rw [ComputablePred.computable_iff] at h
  obtain ⟨g, hg, hgspec⟩ := h
  refine Acceptance.tm_acceptance_not_computablyDecidable
    ⟨fun p => !g (TilingRed.inst p.1 p.2),
      (Primrec.dom_bool (fun b => !b)).to_comp.comp (hg.comp TilingRed.primrec_inst.to_comp),
      fun p => ?_⟩
  have h1 : g (TilingRed.inst p.1 p.2) = true ↔ ¬ Tiling.Solvable (TilingRed.inst p.1 p.2) :=
    (Iff.of_eq (congrFun hgspec (TilingRed.inst p.1 p.2))).symm.trans
      (HOTile.checkTerm_eq_falseTerm_iff _ (TilingRed.wf_inst p.1 p.2))
  have h2 : ((!g (TilingRed.inst p.1 p.2)) = true) ↔ ¬ (g (TilingRed.inst p.1 p.2) = true) := by
    cases hb : g (TilingRed.inst p.1 p.2) <;> simp
  rw [h2, h1, not_not]
  exact TilingRed.solvable_inst_iff p.1 p.2

end Transducers
