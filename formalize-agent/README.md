# formalize-agent

Drives Aristotle through the remaining numbered results of *Transducers*, one
task at a time, unattended, for as long as it takes.

## The idea

The proving happens on Harmonic's servers, not on your laptop. So this is not a
daemon that must stay alive — it is a **state machine that takes one step per
invocation**. `launchd` invokes it every 15 minutes and once at login. Close the
lid, reboot, go away for a week: Aristotle keeps working, and the next tick after
you come back picks up exactly where things stood. The only thing a shutdown
costs is the delay until the finished task is noticed and the next one submitted.

Each tick does at most one thing:

| situation | what the tick does |
| --- | --- |
| a task is still `IN_PROGRESS` | logs a heartbeat and exits |
| a task returned `COMPLETE` | downloads, syncs, commits; checks whether the target's theorems are really free of `sorry`; re-prompts if not, otherwise moves on |
| a task returned `OUT_OF_BUDGET` | downloads, commits, and submits a *continuation* of the same target (up to `max_continues`) |
| a task `FAILED` | retries it (up to `max_retries_on_failure`) |
| a task was `CANCELED` by hand | pauses the whole run, so the driver never fights you |
| nothing outstanding | submits the next target in the queue |
| someone else started a task | adopts it and waits, rather than interrupting it |

State lives in `state.json`, written atomically, so a power cut cannot corrupt
it. A `flock` means a manual run and a launchd run can never overlap.

Two things keep a fixed plan from going stale over a run of days:

* **Every prompt is prefixed with the real state of the repository** at the
  moment it is sent — which of the task's results are still open, and whether
  the results it *assumes* (its `depends_on`) actually landed, with an explicit
  warning when they did not. Without this, a prompt written on day one would
  cheerfully tell Aristotle that "C.2.9 should already be available" when C.2.9
  had in fact been abandoned two targets earlier.
* **Findings go to an inbox, not a log file.** `REVIEW.md` collects audit
  reports, targets that ended with theorems still unproved, exhausted budgets,
  server failures, and targets that left more `sorry`s than they found. The run
  keeps going; `driver.py status` shows a banner until you clear it with
  `driver.py reviewed`. Only the conditions in `pause_on` (default: `failed`)
  halt the queue, because a run that stops at the first surprise and waits to be
  noticed is no use while you are away.

## Files

```
USAGE.md       start here if you just want to run the thing
queue.json     the plan: one entry per group of book results, its prompt, and what it depends on
config.json    project id, retry limits, pause_on, and the standing rules appended to every prompt
driver.py      the state machine
state.json     progress (generated)
REVIEW.md      the inbox: things worth a human look (generated; cleared by `driver.py reviewed`)
logs/          driver.log, launchd.out/err, and summaries/<task-id>.md for every task
```

## Using it

```sh
./install.sh              # schedule it
./driver.py status        # where things stand
./driver.py pause "why"   # stop submitting new work
./driver.py resume
./driver.py skip   <target-id>    # give up on one target
./driver.py requeue <target-id>   # send one back for another go
./driver.py sync          # pull the server state without submitting anything
./uninstall.sh            # unschedule; state and sources untouched
tail -f logs/driver.log
```

`driver.py status` also prints the current `sorry` count and the last few
commits. Every harvest is a commit in `../transducer-lean`, with Aristotle's own
summary as the commit body, so `git log` there is the narrative of the run.

## The standing rules

`config.json` holds `standing_instructions`, appended to *every* prompt. They are
the guardrails that matter for a run nobody is watching — most importantly:
never weaken a statement to make it provable, never close a goal with `sorry`,
a new `axiom` or `native_decide`, keep `lake build` green, and report `#print
axioms` for anything claimed as proved. If the book turns out to be wrong
somewhere, Aristotle is told to keep the faithful statement, add the corrected
one beside it, and document the divergence — as it already did for
Definition A.2.7, for the derivative in Lemma A.2.10, and for Theorem B.4.6.

Two audit targets (`audit-C`, `audit-final`) do nothing but check those claims
against `#print axioms` and against the book's LaTeX sources, and report
divergences.

## macOS permissions (read this before moving anything)

`~/Documents` is TCC-protected, and a launchd job gets none of your Terminal's
access to it. The job therefore **invokes the pipx Python binary directly**:

```xml
<string>…/pipx/venvs/aristotlelib/bin/python</string>
<string>…/formalize-agent/driver.py</string>
```

Routing it through `/bin/sh run-tick.sh` instead does **not** work — launchd
cannot even `getcwd` or exec inside `~/Documents`, and every tick dies with

```
/bin/sh: …/run-tick.sh: Operation not permitted
```

silently, 96 times a day. If you ever edit the plist, keep the interpreter as
`ProgramArguments[0]`. `run-tick.sh` remains the right way to invoke the driver
*by hand* from a Terminal, where it resolves the interpreter for you.

If a future macOS tightens this further, the fallbacks are, in order: grant Full
Disk Access to that Python binary in System Settings → Privacy & Security; or
run `./tick-loop.sh` in a Terminal window, which inherits Terminal's access and
needs no grant at all.

## Adding work

Append an entry to `queue.json` — `id`, `title`, `results`, `lean_names`,
`prompt` — and the next tick picks it up. `lean_names` is what the driver greps
to decide whether a target is genuinely finished, so keep it accurate.

## Caveats

* The driver's "is it proved?" check is a `sorry`-grep of the declaration body.
  It cannot see a `sorry` in a *dependency*; that is what the audit targets and
  `#print axioms` are for.
* There is no local Lean toolchain on this machine, so nothing is verified
  locally — `lake build` runs on Aristotle's side. Install `elan` if you want an
  independent check.
* The book's `.tex` sources are never written to. If Aristotle's copy of them
  drifts from yours, the driver says so in the log and leaves them alone.
