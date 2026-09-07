# Campaign ledger

Opened 2026-09-07. One row per submission; the *next leaf* column is what the
next session or subagent picks up. Keep this file short and current.

| id | folder | concepts | proofs | state (2026-09-07) | next leaf |
|---|---|---|---|---|---|
| lax-251941 | `pcp-undecidability` | 9 written, build | Source ported (24 modules, builds); Bridge/Results being written | empty draft on the archive | Bridge + Results, `lax build --replay`, commit, resubmit |
| lax-765601 | `mealy-machines` | 22 | 13, all discharged | **`lax build --replay` green; committed a2e2a89; empty draft on the archive, content not yet resubmitted** | resubmit once the empty-scaffold submit loop has finished |
| lax-132576 | `rational-functions` | – | – | empty draft | concepts (PLAN §3 S2), Source port of `PartB/*` + `Common/{PrimrecArith,PrimrecList,PrimrecList2,RegularAux}`, requires lax-765601 and lax-251941 |
| lax-916827 | `regular-functions` | – | – | empty draft | after S2 |
| lax-314295 | `mso-transductions` | – | – | empty draft | after S3 |
| lax-709149 | `regular-combinators` | – | – | empty draft | after S3 |
| lax-194892 | `polyregular-functions` | – | – | empty draft | after S4 |
| lax-157538 | `transducers-book` | none (umbrella) | none | empty draft | paper folder + markers, after all seven are drafts |

## Source edits (against the epoch mathlib)

- S0: `Source/PCP/TuringMachine.lean` — `Sym` aliased to the concept's type
  (abbrev + `@[match_pattern]` constructors); `Source/PartB/PCPRed.lean` is
  a hand-written stub with the index-form PCP definitions.
- S1: none. (Warnings: `push_neg` deprecated in `Common/Aux`, `PartA/StateTrans`,
  `PartA/StateTransAperiodic`.)
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
