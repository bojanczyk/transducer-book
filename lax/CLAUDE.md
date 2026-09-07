# lax/ — the book *Transducers* as Lax submissions

Read `PLAN.md` (what is being built, Jan's decisions) and `CAMPAIGN.md` (where
each submission stands, the next leaf) before doing anything. This file is
the working method; it applies to every session and every subagent.

## The shape

One folder per submission (eight: `pcp-undecidability`, `mealy-machines`,
`rational-functions`, `regular-functions`, `mso-transductions`,
`regular-combinators`, `polyregular-functions`, `transducers-book`), each a
`lax init` scaffold with its id bound to an archive issue. Ids stay as they
are (six-digit); the package names embed them (`Lax765601`, `Lax765601Proofs`).

- `concepts/LaxN/*.lean` — written fresh, one module per reviewable idea, in
  the register of the archive's flagship submissions (`~/git/lax-submissions/README.md`
  §4): paper-level description, `# Formalization notes`, docstring on every
  declaration, zero axioms in a definition-concept, exactly one in a
  theorem-concept. Everything declared lives under `LaxN.<Module>`.
- `proofs/LaxNProofs/Source/<Part>/<File>.lean` — the source development
  `../transducer-lean/RequestProject/` copied **verbatim** by `tools/port.py`
  (imports and root namespaces rewritten; `Transducers` → `LaxNProofs.Transducers`).
  Never hand-edit a Source file except to fix a compile error against the
  epoch mathlib, and record every such edit in `CAMPAIGN.md`.
- `proofs/LaxNProofs/Bridge.lean` — each concept definition proved equal or
  equivalent to its source counterpart (`toSrc`/`ofSrc` for structures,
  `compClosure_iff` for the inductive closure, `Iff.rfl` where definitions
  unfold identically).
- `proofs/LaxNProofs/Results.lean` — the numbered results, one `theorem` per
  concept axiom with `conclusion:` frontmatter, a summary, `# Proof strategy`
  and `# Attribution` (book section + Aristotle), each a few lines through the
  bridge. A headline biconditional is glued from its two half-concepts *as
  assumptions* (see `aperiodic_iff_compClosure_flipFlop`).
- Root modules list every module of the package, one import per line, nothing
  else (regenerate with `find`, see the commands below).

`../transducer-lean/` is a read-only mirror of Aristotle's server. Never edit
it.

## Commands

    cd <submission>/concepts && lake build          # fast iteration
    cd <submission>/proofs   && lake build
    lax build --replay <submission>                 # the archive's checks, incl. kernel replay
    lax submit <submission> --allow-dirty           # submits committed, pushed HEAD as a draft

`lake` is `~/.elan/bin/lake`; builds read mathlib from the warm store, nothing
is downloaded. Porting a part:

    python3 tools/port.py --pkg LaxNProofs --dest <submission>/proofs \
        --dep LaxMProofs=<dep-submission>/proofs  <Part>/<File> ...

`--dep` resolves `import RequestProject.X` against the dependency's
`ported.txt` (at the submission root); `--provided X/Y` declares a module you wrote by hand
(`Source/PartB/PCPRed.lean` in S0 is the pattern: the few definitions a file
needs from a later part, copied on their own).

Regenerate a root module:

    (cd LaxNProofs && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort | sed 's/^/import LaxNProofs./') > LaxNProofs.lean

## Cross-submission requires

Concept packages of later parts require the concept packages of earlier parts;
proof packages require the earlier proof packages too (the source development
of Part B uses the Mealy API of Part A). A require pins `(git, rev, subDir)` of
the dependency's **current archive record** (`lax pull-db`; `~/.lax/lax-database/lax-N/record.json`),
so a dependency is submitted as a draft before a dependent pins it, and every
re-submission of a dependency means repinning and resubmitting the dependents.
For the local loop, `~/git/lax-submissions/.claude/sibling-overrides.sh` shows
how to redirect pins to sibling folders with Lake package overrides; adapt it
here when the chain is long enough to hurt.

## Gotchas met so far

- The archive builds with `autoImplicit = false`; the source relied on it in a
  few Part B files (`PairWeighted.lean`: `K`). Add the binders.
- mathlib drift at the epoch: `Primrec.list_take`/`list_drop` now exist with
  flipped argument order (rename ours to `list_take'`/`list_drop'`), some
  `rw` on set-builder terms need the `Language A` ascription or `change`,
  `List.map Subtype.val` vs `List.unattach` normal forms in `CodeRat.lean`,
  a `generalize` in `PrimrecArith.lean` after `decode_ratSig`. `push_neg` is
  deprecated (warning only).
- Dot notation on a concept type does not work from a proof module (the prefix
  rule forbids declaring into `LaxN.*`), which is why Source keeps its own
  copies of the types and the bridge transports.
- A shared inductive type (S0's `Sym`) can be aliased in Source as an
  `abbrev` plus `@[match_pattern] abbrev` constructors, so that the source's
  pattern matches keep working on the concept's type.
- Disk is tight on this machine (~10 GB). Build one submission at a time;
  `.lake/build` of a full part is 1–3 GB.

## Working rhythm

Land at every boundary: commit the submission folder (never `build-output.json`,
`lake-manifest.json`, `.lake/`), push, `lax submit --allow-dirty`, update
`CAMPAIGN.md`. Subagents get one coherent leaf (one part's Source port, or one
part's concepts, or one bridge), narrow file ownership, and the gate that
decides it: `lake build` green, or `lax build --replay` green. The supervisor
reviews the concrete result before landing.
