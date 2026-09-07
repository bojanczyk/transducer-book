# Campaign ledger

Opened 2026-09-07. One row per submission; the *next leaf* column is what the
next session or subagent picks up. Keep this file short and current.

| id | folder | concepts | proofs | state (2026-09-07, 15:15) | next leaf |
|---|---|---|---|---|---|
| lax-251941 | `pcp-undecidability` | 9 | 6, all discharged | **draft on the archive with content** (9680c6e), replay green | none |
| lax-765601 | `mealy-machines` | 22 | 13, all discharged | **draft on the archive with content** (cf8ade7), replay green | none |
| lax-132576 | `rational-functions` | 42 | 29, all discharged; Source = 63 modules | **draft on the archive with content** (972ebef), replay green | none |
| lax-916827 | `regular-functions` | 29, archive concept check green | Source = 136 modules, `lake build` green; Bridge/Results pending; pins A @ cf8ade7, B @ 972ebef | **concepts-only draft on the archive** (a0fb09b); Source port committed | (1) Bridge + Results (23 theorems; the two `TwoDFA`-free continuity ones and the code-based decidability need the `Primcodable` transport as in S2); (2) `lax build --replay`, commit, resubmit; then S4/S5 pin it |
| lax-314295 | `mso-transductions` | 25 drafted, not yet built | – | empty draft | after S3's draft: pin Lax765601, Lax132576, Lax916827 into concepts; proofs require Lax916827Proofs as well; port the closure of `PartC/MSO` minus S3's ported.txt — 44 modules, 12k lines |
| lax-709149 | `regular-combinators` | 4 drafted, not yet built | – | empty draft | after S3's draft: pin Lax132576, Lax916827; port the closure of `PartC/CombStatements` minus S3 — 15 modules, 3.7k lines (needs nothing from S4) |
| lax-194892 | `polyregular-functions` | 20 drafted, not yet built | – | empty draft | after S4's draft: pin Lax765601, Lax916827, Lax314295 (concepts: `Continuity` from A, `RegularFunctions` from S3; MSO is not used by the concepts); proofs require S3Proofs and S4Proofs; port the closure of `PartD/{Statements,PebReach,ChildGraphFor,CGFor,ChildExample}` minus S3/S4 — 78 modules, 23k lines, of which 7 are `PartC/*` pulled in only through the roll-up import `RequestProject.PartC` in some Part D file: replace that import by the specific modules |
| lax-157538 | `transducers-book` | none (umbrella) | none | empty draft | paper folder + markers, after all seven are drafts; lakefiles require all seven concept and proof packages |

## Source edits (against the epoch mathlib)

- S0: `Source/PCP/TuringMachine.lean` — `Sym` aliased to the concept's type
  (abbrev + `@[match_pattern]` constructors); `Source/PartB/PCPRed.lean` is
  a hand-written stub with the index-form PCP definitions.
- S1: none. (Warnings: `push_neg` deprecated in `Common/Aux`, `PartA/StateTrans`,
  `PartA/StateTransAperiodic`.)
- S2 (`rational-functions`, Part B, 62 modules + stub `Source/PCP/Index.lean`,
  which takes `Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable`
  as `Transducers.PCP.solvable_not_computablePred`; the two `Solvable`s are
  defeq, `exact` works):
  `Common/PrimrecList.lean:43,60,63,87,98` and `PartB/WCodePrimrec.lean:65` —
  `list_drop`/`list_take` renamed `list_drop'`/`list_take'` (mathlib now has
  them, flipped argument order);
  `Common/PrimrecArith.lean:251-255` (`decode_rat`) — `rw [decode_ofEquiv,
  decode_ratSig]` → `simp only`, and the `obtain ⟨h1, h2⟩ := h` (goal depends
  on `h`) → `revert h; rintro ⟨h1, h2⟩`;
  `PartB/SubseqAlpha.lean:53` — `rwa [heq] at h` → `exact heq ▸ h` (the
  set-builder in `h` no longer matches syntactically);
  `PartB/CodeRat.lean:146,172-173,268,278,335,362` — `rw`/`simp` with
  `List.map_append`/`List.map_cons` on `List (InA c)`/`List (OutA c)` → `erw`
  (`List.map` now elaborates at the unfolded subtype while the list is at the
  `def` `InA c`, so reducible matching fails; `simp` normalises to `unattach`
  and gets stuck the same way);
  `PartB/PairWeighted.lean:143,146` — auto-bound `K` made an explicit
  `{K : ℕ}` binder in `init_pairW`/`final_pairW`.
  `tools/port.py` fixed: it inserted `open <dep>` into Mathlib-only files
  (unknown namespace) and `open <dep>` alone does not make a bare `Mealy`,
  `PrefixPreserving`, … of the dependency resolve — it now inserts
  `open <dep> <dep>.Transducers` only in files whose import closure reaches the
  dependency. (Warnings: `push_neg` deprecated, 32 sites.)
- S3 (`regular-functions`, Part C §1–3, 136 modules = `Common/HankelRank` +
  135 `PartC/*`; `lake build` green 2026-09-07 15:10, subagent):
  `port.py` mis-resolution (Part B's `ported.txt` lists Part A's modules
  too, so `--dep Lax132576Proofs` claimed them) — eight Part A imports
  rewritten to `Lax765601Proofs.Source.*` (`PartC/KTypes.lean:13`,
  `RegAut.lean:21`, `SSTDef.lean:11`, `MapLiftAux.lean:12`,
  `SSTMealyFF.lean:13`, `SSTMealyRev.lean:13`, `SSTNorm.lean:25`,
  `TwoWayPrecomp.lean:27`) and the inserted `open` line now names every
  dependency package the file's import closure reaches (`tools/port.py`
  fixed: first `--dep` in chain order wins, opens for the whole chain up to
  the furthest package reached);
  cross-package dot notation (`h.congr`, `a.comp b` on Part B's types with
  lemmas declared here) made explicit — `PartC/RatTools.lean:35,193`,
  `ConfGraphReg.lean:170` (`IsRationalRel.congr`), `Statements.lean:73-81`
  (`Continuous.comp`);
  `Set.mem_setOf_eq` no longer rewrites `Language` membership
  (`Language.instMembershipList` ≠ `Set.instMembership`) — `rw [..,
  Set.mem_setOf_eq, ..]` → `change <unfolded membership>` + remaining
  rewrites at `ConfGraphAnnot.lean:182` (the "known ahead" `MultiDFA:59`
  site), `SnakeBase.lean:330,335,522,529`, `MarkStr.lean:217,219`,
  `RunMark.lean:183,329`, `SnakeForall.lean:89`, `SnakeChkMain.lean:164`;
  `rw [if_pos (show u ∈ {v | …} from h)]` → `refine (if_pos h).trans ?_`
  at `SnakeRegTools.lean:48-51`, `SnakeReg.lean:143-145`;
  `TwoWayRat.lean:66` `simpa [filterMap_homOf_padHom] using hb` → `simp
  only [..] at hb; exact hb` (`id` unfolded too early);
  `SnakeChkMain.lean:36` auto-bound `K` → `variable {K : ℕ}`.
  (Warnings: `push_neg` 66 sites, `List.Sublist.cons₂` deprecated in
  `SSTNorm.lean:145`.) No statement changed.
- Known ahead (from the port probe of the whole tree, 2026-09-07):
  `Common/PrimrecList.lean` rename `list_drop`/`list_take` to primed names;
  `Common/PrimrecArith.lean:251` `rw` → `simp only` then a `generalize`
  breaks; `PartB/SubseqAlpha.lean:52` set-builder `rwa`; `PartC/MultiDFA.lean:59`
  `Set.mem_setOf_eq` rewrite; `PartB/CodeRat.lean` (`unattach` normal forms,
  ~7 sites); `PartB/PairWeighted.lean:143,146` auto-bound `K`.

- S2 (archive namespace rule): the source's root-level `namespace Primrec`
  in `Common/PrimrecList.lean`, `Common/PrimrecArith.lean` became
  `Lax132576Proofs.Primrec` (every declaration must carry the package prefix),
  with `open Primrec` placed *before* the namespace so that mathlib's `Primrec`
  is still open; `PartB/WCodePrimrec.lean` got a top-level `open Primrec` for
  the same reason (an `open Primrec` inside the package namespace now finds
  only the package's copy). `tools/port.py` now prefixes every root-level
  namespace, not only `Transducers`/`PCP`/`PCPIndex`/`Acceptance`.
  Second round (replay, 2026-09-07 14:00): the two root-level instances
  `Int.primcodable` (`PrimrecArith.lean:87`) and `_root_.Rat.primcodable`
  (`:292`) became `Lax132576Proofs.Int.primcodable` /
  `Lax132576Proofs.Rat.primcodable` (instances resolve by type, nothing
  names them).

## Decisions log

- 2026-09-07 Jan: seven part submissions + umbrella paper; split only the
  headline iffs; exercises deferred; concepts only for what is formalised;
  authors Bojańczyk + Aristotle; Apache 2.0 for the book text; epoch
  environment; commit/push/submit from this repo authorised.
