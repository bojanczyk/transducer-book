# How to use this

## The short version

You don't. It is already running, and it will keep running for days or weeks
without you. There is no daily command to type, nothing to restart after a
reboot, and nothing that breaks if you close the laptop.

The one thing worth doing is checking in every few days:

```sh
/Users/bojan/Documents/ksiazki/transducer-book-lean/formalize-agent/run-tick.sh status
```

That is the whole user interface. Everything below is for the rarer moments when
you want to change what it is doing.

Worth adding to `~/.zshrc` so you can type `formalize` from anywhere:

```sh
alias formalize='/Users/bojan/Documents/ksiazki/transducer-book-lean/formalize-agent/run-tick.sh'
```

Then it is `formalize status`, `formalize pause`, and so on.

## What is actually happening

Aristotle does the proving on Harmonic's servers. This machine only wakes up
every 15 minutes, asks "is the current task finished?", and if it is, downloads
the result, commits it, and sends the next piece of work. That is why the laptop
being off does not matter: the servers keep going, and when you open the lid the
next check-in notices what happened while you were away.

The work is a queue of 14 tasks covering the ~26 numbered results that are still
open — Part B's conditional versions first, then Part C, then Part D, with two
audit tasks that check the results rather than proving anything new.

## Reading the status output

```
 ▶ B-effectivity-conditional    running  attempts=1
     B.3.3, B.3.4, B.3.7, B.4.2
 · C2-composition               pending
```

| symbol | meaning |
| --- | --- |
| `▶` | being worked on right now |
| `·` | waiting its turn |
| `✓` | done — Aristotle finished and no `sorry` was left in those theorems |
| `~` | partial — it ran out of budget after several continuations; something is still open |
| `✗` | failed on the server side after retries |
| `-` | skipped, because you told it to |

At the bottom you get the current `sorry` count and the last few commits. Do not
read too much into that count from one day to the next: Aristotle regularly adds
scaffolding full of fresh `sorry`s and then closes it, so it goes up as well as
down. What matters is the trend across a finished target. If it has not moved in
a week, something is stuck.

If anything wants your attention you will also see a banner:

```
  ⚠  2 item(s) want your attention — see REVIEW.md
```

## The review inbox

Some things need a human eye, but stopping the whole run until you notice would
waste days. So they are collected in `REVIEW.md` instead, and the run carries on.
An item is filed when:

* an **audit task finishes** — audits exist to find divergences between your book
  and the Lean statements, and results whose "proved" status does not survive
  `#print axioms`. The full report is copied into the inbox;
* a target **ends with its theorems still unproved**, after the driver has already
  sent it back for another attempt;
* a target **runs out of budget** for good, after its continuations are used up;
* a target **fails** on the server — this one also pauses the run;
* a target leaves **more `sorry`s than it found**, which is usually harmless
  scaffolding but occasionally means a result was split into pieces and
  abandoned.

Read it, then clear it:

```sh
formalize reviewed        # archives the text into REVIEW-archive.md
```

You also get a macOS notification as each item is filed. Which conditions halt
the queue outright, rather than just filing an item, is the `pause_on` list in
`config.json` — by default only `failed`.

## Watching it in more detail

```sh
formalize status                       # the summary above
tail -f .../formalize-agent/logs/driver.log      # every check-in, live
git -C .../transducer-lean log         # what has actually been proved, with Aristotle's own write-up in each commit message
```

The commit messages are the real record. Each one contains Aristotle's full
account of what it did, so `git log` in `transducer-lean` reads as the story of
the formalisation.

Each task's write-up is also saved separately in `logs/summaries/`.

## When you might want to step in

**You want it to stop for a while** (e.g. the budget is getting alarming):

```sh
formalize pause "waiting for next month's budget"
formalize resume
```

Pausing stops it submitting anything new. A task already running on the server
keeps going — pausing does not cancel it, and does not lose anything.

**You want it to stop for good:**

```sh
.../formalize-agent/uninstall.sh
```

This unschedules the 15-minute check-in. Your Lean files, the git history and
the queue state are all left alone, and `./install.sh` starts it again from
where it stopped.

**One task is going nowhere** and you would rather move on:

```sh
formalize skip C3-sst
```

**You want it to have another go** at something it gave up on:

```sh
formalize requeue C3-sst
```

**You want to change the plan.** The queue is `queue.json`: a list of tasks, each
with an `id`, the book results it covers, and the prompt sent to Aristotle. Edit
it, add entries, reorder them — the next check-in picks up the change. Anything
already marked done stays done. `lean_names` in each entry is what the script
greps to decide whether a task really finished, so keep those accurate.

**You started a task yourself** in the Aristotle web interface or CLI. That is
fine — the script notices someone else is working, waits for that task to
finish, and carries on afterwards. It will not interrupt you. And if you cancel
a task by hand, it treats that as a signal from you and pauses itself rather
than resubmitting.

## What it will not do

Every prompt carries standing rules, which matter because nobody is watching:
it must not weaken or delete the statement of a theorem to make it provable, and
must not close a proof with `sorry`, a new `axiom`, or `native_decide`. If a
statement in the book turns out to need a correction, it keeps a faithful
version, adds the corrected one next to it, and writes down why — the way it
already did for Definition A.2.7 and Theorem B.4.6.

When a task claims success, the script independently greps those theorems for
`sorry` and sends it back for another attempt if the claim does not hold up.

It also refuses to let a stale plan mislead Aristotle. The prompts in
`queue.json` were written before the run began and say things like "Theorem
C.2.9 should already be available". If that turned out not to happen, the prompt
would be stating a falsehood. So every prompt is prefixed, at the moment it is
sent, with the real state of the repository: which of the task's own results are
still open, which of the results it depends on are actually available, and a
blunt warning when one of them is not, telling Aristotle to prove what it needs
or declare itself blocked. The dependencies are the `depends_on` field of each
queue entry, so if you add a task, list what it assumes.

Two caveats. That grep only sees the theorem's own body, not a `sorry` hiding in
something it depends on — the audit tasks exist for that, and use
`#print axioms`, which is the real check. And there is no Lean toolchain on this
machine, so `lake build` only ever runs on Aristotle's side; install `elan` if
you want to verify independently rather than take its word.

## If something looks wrong

Check when it last ran:

```sh
tail -3 .../formalize-agent/logs/driver.log
```

If the newest line is more than about 20 minutes old, the scheduled job is not
running. Reinstall it with `./install.sh`. If that fails, run
`./tick-loop.sh` in a Terminal window you leave open — it does the same thing
and needs no permissions, but stops when the window closes.

One macOS trap is documented in `README.md`: the scheduled job must invoke the
Python interpreter directly. Routed through a shell it fails silently every 15
minutes, because background jobs are not allowed into `~/Documents`.
