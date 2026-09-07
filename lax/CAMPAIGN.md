# Campaign ledger

Opened 2026-09-07. One row per submission; the *next leaf* column is what the
next session or subagent picks up. Keep this file short and current.

| id | folder | concepts | proofs | state (2026-09-07, 13:00) | next leaf |
|---|---|---|---|---|---|
| lax-251941 | `pcp-undecidability` | 9 | 6, all discharged | **`lax build --replay` green**; committed cf8ade7; content submit running | none — watch the submit result at https://laxarchive.org/lax-251941/ |
| lax-765601 | `mealy-machines` | 22 | 13, all discharged | **`lax build --replay` green**; committed a2e2a89; content submit running | none — watch https://laxarchive.org/lax-765601/ |
| lax-132576 | `rational-functions` | 42 drafted (13 definitions, 29 theorems), **not yet built** | – | empty draft | (1) after the Part A content draft is on the archive: `lax pull-db`, add `[[require]] Lax765601` (git = https://github.com/bojanczyk/transducer-book, rev = record commit, subDir = lax/mealy-machines/concepts) to `concepts/lakefile.toml`, `lax build --only concepts`, fix whatever the drafts get wrong; (2) port `PartB/*` (59 files) + `Common/{PrimrecArith,PrimrecList,PrimrecList2,RegularAux}` with `--dep Lax765601Proofs=mealy-machines/proofs`; the proof package requires Lax765601, Lax765601Proofs, Lax251941 (concepts, for the PCP statement) — `RationalStatements.lean` must lose its import of `PCP.Index` and take `Lax251941.PostCorrespondenceIndexUndecidable.not_computablePred_solvable` through a bridge instead; (3) Bridge + Results (29 theorems; `RelCode`/`WCode` are named structures here, tuples in the source — bridge through `relCodeEquiv`/`wcodeEquiv`, and `DecidableUnderPromise` transports along the `Primrec` equiv) |
| lax-916827 | `regular-functions` | 29 drafted (6 definitions, 23 theorems), not yet built | – | empty draft | pin Lax765601 and Lax132576 (once Part B's draft carries its concepts) into `concepts/lakefile.toml`, build, fix; then Source port of `PartC/*` minus the logic files (`MSO*`, `Mark*`, `FO*`, `Walk*`, `KTypes`, `MultiDFA`, `SortedEnum`, `RegAut`, `TransEnum`, `RunProbe`, `RunMark`, `FlatIndex`, `RunElts`, `TwoWayMSO`) and minus `Comb*` — check each file against THEOREMS.md's table; `PartC/Statements.lean` imports `PartB.WeightedStatements`, so the proof package requires Lax132576Proofs; `Common/HankelRank` goes here |
| lax-314295 | `mso-transductions` | 25 drafted (4 definitions, 21 theorems), not yet built | – | empty draft | after S3's draft: pin Lax765601, Lax132576, Lax916827; build; Source port of the logic files listed under S3 (they import `PartC.Statements`, so the proof package requires Lax916827Proofs) |
| lax-709149 | `regular-combinators` | – | – | empty draft | after S3 |
| lax-194892 | `polyregular-functions` | – | – | empty draft | after S4 |
| lax-157538 | `transducers-book` | none (umbrella) | none | empty draft | paper folder + markers, after all seven are drafts; its lakefiles require all seven concept packages and all seven proof packages |

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
- Known ahead (from the port probe of the whole tree, 2026-09-07):
  `Common/PrimrecList.lean` rename `list_drop`/`list_take` to primed names;
  `Common/PrimrecArith.lean:251` `rw` → `simp only` then a `generalize`
  breaks; `PartB/SubseqAlpha.lean:52` set-builder `rwa`; `PartC/MultiDFA.lean:59`
  `Set.mem_setOf_eq` rewrite; `PartB/CodeRat.lean` (`unattach` normal forms,
  ~7 sites); `PartB/PairWeighted.lean:143,146` auto-bound `K`.

## Decisions log

- 2026-09-07 Jan: seven part submissions + umbrella paper; split only the
  headline iffs; exercises deferred; concepts only for what is formalised;
  authors Bojańczyk + Aristotle; Apache 2.0 for the book text; epoch
  environment; commit/push/submit from this repo authorised.
