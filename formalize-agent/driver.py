#!/usr/bin/env python3
"""Autonomous driver for the Lean formalisation of *Transducers* (M. Bojanczyk).

The proving happens on Harmonic's servers, so this script is deliberately not a
long-running process: every invocation performs one idempotent *tick* of a state
machine and exits.  Turning the laptop off merely delays the next tick.

One tick does at most one of:

  * nothing, because a task is still running server-side;
  * integrate a finished run (download, merge into the Lean directory, commit);
  * submit the next target, which creates a project for it.

The local repository is the authoritative copy. Each run gets a project of its
own, created from the working tree as it then stands, so the agent always reads
the current book and the current Lean; and because the project has a known base
commit, what comes back is merged rather than written over. Work done here while
a run is in flight therefore survives it.

Run `driver.py status` for a human-readable view.
"""

from __future__ import annotations

import argparse
import fcntl
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CONFIG_PATH = HERE / "config.json"
QUEUE_PATH = HERE / "queue.json"
STATE_PATH = HERE / "state.json"
LOG_DIR = HERE / "logs"
SUMMARY_DIR = LOG_DIR / "summaries"
LOG_FILE = LOG_DIR / "driver.log"
LOCK_PATH = HERE / ".lock"
REVIEW_PATH = HERE / "REVIEW.md"

TERMINAL_OK = {"COMPLETE"}
TERMINAL_PARTIAL = {"COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET"}
TERMINAL_BAD = {"FAILED"}
TERMINAL_STOP = {"CANCELED"}
RUNNING = {"QUEUED", "IN_PROGRESS"}


# --------------------------------------------------------------------------
# basics
# --------------------------------------------------------------------------

def now() -> datetime:
    return datetime.now(timezone.utc)


def ts() -> str:
    return now().strftime("%Y-%m-%d %H:%M:%SZ")


def log(msg: str, echo: bool = True) -> None:
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    line = f"[{ts()}] {msg}"
    with LOG_FILE.open("a") as fh:
        fh.write(line + "\n")
    if echo:
        print(line, flush=True)


def load_json(path: Path, default=None):
    if not path.exists():
        return default
    with path.open() as fh:
        return json.load(fh)


def save_json(path: Path, data) -> None:
    """Atomic write, so a crash or a power cut cannot truncate the state."""
    tmp = path.with_suffix(path.suffix + ".tmp")
    with tmp.open("w") as fh:
        json.dump(data, fh, indent=2, ensure_ascii=False)
        fh.write("\n")
        fh.flush()
        os.fsync(fh.fileno())
    os.replace(tmp, path)


def config() -> dict:
    cfg = load_json(CONFIG_PATH)
    if cfg is None:
        sys.exit(f"missing {CONFIG_PATH}")
    return cfg


def queue() -> list:
    q = load_json(QUEUE_PATH)
    if not q:
        sys.exit(f"missing or empty {QUEUE_PATH}")
    return q


def lean_dir(cfg: dict) -> Path:
    return (HERE / cfg["lean_dir"]).resolve()


def notify(cfg: dict, title: str, message: str) -> None:
    if not cfg.get("notify"):
        return
    try:
        subprocess.run(
            ["osascript", "-e",
             f'display notification {json.dumps(message)} with title {json.dumps(title)}'],
            check=False, capture_output=True, timeout=10,
        )
    except Exception:
        pass


# --------------------------------------------------------------------------
# api key + sdk
# --------------------------------------------------------------------------

def review(cfg: dict, st: dict, title: str, body: str) -> None:
    """Add an item to REVIEW.md — the inbox for things a human should look at.

    Deliberately an inbox rather than a hard stop: a run that halts on the first
    surprise and waits for someone to notice is not much use over days away.
    """
    with REVIEW_PATH.open("a") as fh:
        fh.write(f"\n## {ts()} — {title}\n\n{body.rstrip()}\n")
    st["review_pending"] = st.get("review_pending", 0) + 1
    log(f"REVIEW: {title}")
    notify(cfg, "Formalisation: something to look at", title)


def note_sorry_delta(cfg: dict, st: dict, rec: dict, target: dict) -> None:
    """Flag a target that left the project with more `sorry`s than it found.

    Aristotle routinely adds scaffolding with fresh `sorry`s and closes it again,
    so this is only meaningful once a whole target is finished.
    """
    before = rec.get("sorries_at_start")
    if before is None:
        return
    after = sorry_count(lean_dir(cfg))
    if after > before:
        review(cfg, st, f"{target['id']} left more `sorry`s than it found",
               f"{before} before, {after} after. That can be legitimate — new scaffolding "
               f"for later work — but it can also mean a result was restated into pieces "
               f"that were never finished. Worth a look at:\n\n"
               f"    git -C ../transducer-lean log -p --since='2 days ago' -- '*.lean'")


def maybe_pause(cfg: dict, st: dict, condition: str, reason: str) -> None:
    if condition in cfg.get("pause_on", ["failed"]):
        st["paused"] = True
        st["pause_reason"] = reason
        log(f"paused: {reason}")
        notify(cfg, "Formalisation paused", reason)


def ensure_api_key() -> None:
    """launchd does not read ~/.zshrc, so recover the key from there if needed.

    The key is never copied into this directory: it is read at run time.
    """
    if os.environ.get("ARISTOTLE_API_KEY"):
        return
    for rc in (Path.home() / ".zshrc", Path.home() / ".zprofile", Path.home() / ".bash_profile"):
        if not rc.exists():
            continue
        m = re.search(r'^\s*export\s+ARISTOTLE_API_KEY\s*=\s*["\']?([^"\'\s]+)',
                      rc.read_text(errors="ignore"), re.M)
        if m:
            os.environ["ARISTOTLE_API_KEY"] = m.group(1)
            return
    sys.exit("ARISTOTLE_API_KEY not set and not found in ~/.zshrc")


def run_async(coro):
    import asyncio
    return asyncio.run(coro)


def project_by_id(pid: str):
    from aristotlelib.project import Project
    return run_async(Project.from_id(pid))


def get_project(cfg: dict):
    """The project named in config.json — only the older, shared one now."""
    return project_by_id(cfg["project_id"])


def get_task(task_id: str):
    from aristotlelib.agent_task import AgentTask
    return run_async(AgentTask.from_id(task_id))


def status_name(obj) -> str:
    s = getattr(obj, "status", None)
    return getattr(s, "name", str(s))


# --------------------------------------------------------------------------
# state
# --------------------------------------------------------------------------

def fresh_state(q: list) -> dict:
    return {
        "version": 1,
        "created_at": ts(),
        "order": [t["id"] for t in q],
        "targets": {
            t["id"]: {"status": "pending", "attempts": 0, "continues": 0,
                      "reattempts": 0, "task_ids": [], "started_at": None,
                      "finished_at": None, "note": None}
            for t in q
        },
        "current": None,
        "paused": False,
        "pause_reason": None,
        "finished_at": None,
        "ticks": 0,
        "last_tick": None,
    }


def load_state(q: list) -> dict:
    st = load_json(STATE_PATH)
    if st is None:
        st = fresh_state(q)
        save_json(STATE_PATH, st)
        log(f"initialised state with {len(q)} targets")
        return st
    # absorb targets added to the queue after the run started
    for t in q:
        if t["id"] not in st["targets"]:
            st["targets"][t["id"]] = {"status": "pending", "attempts": 0, "continues": 0,
                                      "reattempts": 0, "task_ids": [], "started_at": None,
                                      "finished_at": None, "note": None}
            st["order"].append(t["id"])
            log(f"queue grew: added target {t['id']}")
    return st


def target_by_id(q: list, tid: str) -> dict | None:
    return next((t for t in q if t["id"] == tid), None)


def next_pending(st: dict, q: list) -> dict | None:
    for tid in st["order"]:
        if st["targets"].get(tid, {}).get("status") == "pending":
            return target_by_id(q, tid)
    return None


# --------------------------------------------------------------------------
# lean inspection (a progress signal only; `#print axioms` is the real check)
# --------------------------------------------------------------------------

DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                     r"(theorem|lemma|def|instance|abbrev|example)\s+([A-Za-z_][A-Za-z0-9_'.]*)")


def declaration_bodies(path: Path) -> dict[str, str]:
    """Map declaration name -> its source text, up to the next declaration.

    Read from the comment-free view of the file, not the raw one: a declaration
    that has been commented out is not a declaration, and slicing the raw text
    first would hand each chunk to `strip_comments` without the `/-` that opened
    the block it sits in, so the comment would look like code.
    """
    out: dict[str, str] = {}
    name, buf = None, []
    for line in strip_comments(path.read_text(errors="ignore")).splitlines():
        m = DECL_RE.match(line)
        if m and not line.startswith(" "):
            if name:
                out[name] = "\n".join(buf)
            name, buf = m.group(2), [line]
        elif name:
            buf.append(line)
    if name:
        out[name] = "\n".join(buf)
    return out


def strip_comments(text: str) -> str:
    """Comments blanked to spaces, character for character.

    Lean's block comments nest, and a withdrawn result is left in the sources
    commented out -- `/- ... /-- **Theorem C.4.17.** ... -/ ... -/`. A
    non-nesting `/-.*?-/` stops at the first `-/`, which is the docstring's,
    and everything after it reads as live code: a commented-out `sorry` then
    counts, and `open_results` calls a finished result unproved and burns a
    reattempt on it. Length and newlines are preserved so offsets still line up.
    """
    out, i, n = list(text), 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = n
        else:
            i += 1
            continue
        for k in range(i, j):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


def collect_bodies(ld: Path) -> dict[str, str]:
    bodies: dict[str, str] = {}
    for f in ld.rglob("*.lean"):
        if ".lake" in f.parts:
            continue
        bodies.update(declaration_bodies(f))
    return bodies


def dependency_graph(ld: Path) -> tuple[dict[str, str], dict[str, set[str]]]:
    """Comment-free declaration bodies, plus the declarations each one mentions."""
    bodies = {k: strip_comments(v) for k, v in collect_bodies(ld).items()}
    index: dict[str, str] = {}
    for name in bodies:
        index.setdefault(name, name)
        index.setdefault(name.split(".")[-1], name)
    edges: dict[str, set[str]] = {}
    for name, body in bodies.items():
        deps: set[str] = set()
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body):
            hit = index.get(tok) or index.get(tok.split(".")[-1])
            if hit is not None and hit != name:
                deps.add(hit)
        edges[name] = deps
    return bodies, edges


def sorry_witnesses(ld: Path) -> tuple[dict[str, str], dict[str, str]]:
    """Bodies, and a map: declaration -> the `sorry` declaration it rests on.

    A declaration is tainted if its own body has a `sorry`, or if it mentions a
    tainted one.  This is an approximation of `#print axioms` from the sources
    alone, and it errs towards over-reporting, since it counts every mention of
    a name.  That is the safe direction: the failure it exists to prevent is a
    result being recorded as done while it still rests on an unproved lemma.
    """
    bodies, edges = dependency_graph(ld)
    rev: dict[str, set[str]] = {}
    for name, deps in edges.items():
        for d in deps:
            rev.setdefault(d, set()).add(name)
    witness: dict[str, str] = {}
    pending: list[str] = []
    for name, body in bodies.items():
        if re.search(r"\bsorry\b", body):
            witness[name] = name
            pending.append(name)
    while pending:
        cur = pending.pop()
        for up in rev.get(cur, ()):
            if up not in witness:
                witness[up] = witness[cur]
                pending.append(up)
    return bodies, witness


def classify(ld: Path, pairs: list[tuple[str, str]]) -> list[tuple[str, str, str, str | None]]:
    """Classify (book number, lean name) pairs as clean / open / blocked / missing.

    The fourth component names the `sorry` a blocked result rests on.
    """
    bodies, witness = sorry_witnesses(ld)
    out = []
    for num, name in pairs:
        short = name.split(".")[-1]
        key = short if short in bodies else next(
            (k for k in bodies if k.split(".")[-1] == short), None)
        if key is None:
            out.append((num, short, "missing", None))
            continue
        w = witness.get(key)
        if w is None:
            out.append((num, short, "clean", None))
        elif w == key:
            out.append((num, short, "open", None))
        else:
            out.append((num, short, "blocked", w))
    return out


def live_hypotheses(ld: Path, names: list[str]) -> list[str]:
    """Which of these `Prop`s is still taken as an argument by some declaration.

    The goal of a `hyp-*` target is not "no `sorry`" but "this assumption is gone
    from the statements", so `open_results` cannot see whether it is finished. A
    run that has already discharged its hypotheses will happily spend another
    continuation restating what it did -- that is how hyp-fo-non-elementary came
    to be continued after `FirstStringOfOrderDefinable` was already a theorem.

    Deliberately a stopping heuristic and not an oracle: it only ever ends a
    target early, and files a review item saying so, so a false positive costs a
    `requeue` and a false negative costs nothing beyond the old behaviour.
    """
    if not names:
        return []
    live: set[str] = set()
    for f in ld.rglob("*.lean"):
        if ".lake" in f.parts:
            continue
        try:
            txt = f.read_text(errors="ignore")
        except OSError:
            continue
        txt = re.sub(r"/-[-!]?[\s\S]*?-/", "", txt)
        txt = "\n".join(l for l in txt.split("\n") if not l.lstrip().startswith("--"))
        for n in names:
            if n in live:
                continue
            # a binder `(h : Name)` / `{h : Name}` / `[h : Name]`, the only way a
            # hypothesis of this kind is ever taken
            if re.search(r"[(\{\[]\s*[A-Za-z_][A-Za-z0-9_'\u2080-\u2089]*\s*:\s*"
                         + re.escape(n) + r"\s*[)\}\]]", txt):
                live.add(n)
    return [n for n in names if n in live]


def open_results(ld: Path, names: list[str]) -> list[str]:
    """Which of these declarations are not yet fully proved.

    A declaration whose own body is clean can still be unproved, because what it
    calls may not be: that is how C.2.9, C.3.2 and C.4.8 came to be recorded as
    done while they all rested on `boundedWidth_isRegular_step`.  `#print axioms`,
    which the standing instructions require, remains the authority; this is the
    cheap check the driver can run for itself.
    """
    if not names:
        return []
    still: list[str] = []
    for _, short, state, w in classify(ld, [("", n) for n in names]):
        if state == "missing":
            still.append(f"{short} (not found)")
        elif state == "open":
            still.append(short)
        elif state == "blocked":
            still.append(f"{short} (rests on {w})")
    return still


STATE_DESC = {
    "clean": "no `sorry` of its own and none in what it rests on",
    "open": "STILL CONTAINS `sorry`",
    "blocked": "its own proof is finished, but it RESTS ON an unproved result",
    "missing": "NOT FOUND in the sources",
}


def build_preamble(target: dict, ld: Path) -> str:
    """Describe the repository as it actually is, at the moment of submission.

    The prompts in queue.json were written before the run began and say things
    like "C.2.9 should already be available". If that turned out false, the
    prompt would mislead Aristotle. This preamble states the facts instead.
    """
    own = list(zip(target.get("results", []), target.get("lean_names", [])))
    deps = list(target.get("depends_on", {}).items())
    if not own and not deps:
        return ""

    lines = [f"--- State of the repository, generated automatically at {ts()}. "
             f"Where it contradicts the instructions below, trust this. ---", ""]

    if own:
        lines.append("The results this task is meant to close:")
        for num, short, state, w in classify(ld, own):
            rests = f" ({w})" if w else ""
            lines.append(f"  * {num} ({short}) — {STATE_DESC[state]}{rests}")
        lines.append("")

    stale = []
    if deps:
        lines.append("Results that the instructions below assume are already available:")
        for num, short, state, w in classify(ld, deps):
            rests = f" ({w})" if w else ""
            lines.append(f"  * {num} ({short}) — {STATE_DESC[state]}{rests}")
            if state != "clean":
                stale.append(num)
        lines.append("")

    if stale:
        many = len(stale) > 1
        lines += [
            f"WARNING: the instructions below were written before this run started, and "
            f"assume {', '.join(stale)} {'are' if many else 'is'} available. That is not "
            f"the case now. Do not rely on {'them' if many else 'it'}: either prove what "
            f"you need yourself, or say plainly in your summary that this task is blocked "
            f"and on what.", ""]

    lines += [
        f"`sorry` occurrences in the project right now: {sorry_count(ld)}.",
        "(This check reads the sources and follows each declaration through the "
        "results it mentions, so it sees a finished proof that rests on an unproved "
        "lemma. It is still only a source-level approximation: `#print axioms` is "
        "the authority, and you are asked to run it.)",
        "--- end of generated state ---", "", ""]
    return "\n".join(lines)


def sorry_count(ld: Path) -> int:
    total = 0
    for f in ld.rglob("*.lean"):
        if ".lake" in f.parts:
            continue
        total += len(re.findall(r"\bsorry\b", strip_comments(f.read_text(errors="ignore"))))
    return total


# --------------------------------------------------------------------------
# harvesting
# --------------------------------------------------------------------------

def locate_lean_project(root: Path, subdir: str) -> Path | None:
    """Find the Lean project inside an extracted archive.

    The archive holds the whole workspace (book sources plus the Lean project),
    so prefer the configured subdirectory and fall back to a search.
    """
    candidates = list(root.glob(f"*/{subdir}")) + list(root.glob(subdir))
    for c in candidates:
        if (c / "RequestProject.lean").exists():
            return c
    for c in root.rglob("RequestProject.lean"):
        if ".lake" not in c.parts:
            return c.parent
    return None


def git(ld: Path, *args: str, **kw) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(ld), *args],
                          capture_output=True, text=True, **kw)


GITIGNORE = ".lake/\n*.olean\n*.olean.tmp\n.DS_Store\n__pycache__/\n*.pyc\n"


# The Lean project used to be a repository of its own; it is now a directory of
# the book's repository, so that one push backs up the book and its
# formalisation together. Nothing here hard-codes either arrangement: the two
# helpers below ask git where the Lean sources sit, and every operation that
# used to assume "the Lean project is the repository root" is scoped through
# them. Without that scoping the rsync in `integrate` would delete the book:
# its `--delete` is relative to the worktree root, which under the old
# assumption *was* the Lean tree and is now the whole book.

def repo_root(ld: Path) -> Path:
    """The top of the repository the Lean sources live in."""
    out = git(ld, "rev-parse", "--show-toplevel").stdout.strip()
    return Path(out) if out else ld


def lean_prefix(ld: Path) -> str:
    """Where the Lean project sits inside that repository.

    `''` when it is the repository root, `'transducer-lean/'` when it is a
    directory of the book's repository. Git reports paths relative to the root,
    so this is also the prefix every path in a `git diff` carries.
    """
    return git(ld, "rev-parse", "--show-prefix").stdout.strip()


def ensure_gitignore(ld: Path) -> None:
    """Keep .lake (hundreds of MB of dependencies) out of the repository.

    Must be re-asserted after every rsync: the archive carries no .gitignore.
    """
    gi = ld / ".gitignore"
    have = gi.read_text(errors="ignore") if gi.exists() else ""
    missing = [l for l in GITIGNORE.split() if l not in have]
    if missing:
        gi.write_text(have.rstrip("\n") + "\n" + "\n".join(missing) + "\n" if have
                      else GITIGNORE)


def ensure_git(ld: Path) -> None:
    # A directory inside the book's repository is already under version
    # control; `.git` does not exist there, and `git init` would make a nested
    # repository that silently shadows the real one.
    if git(ld, "rev-parse", "--is-inside-work-tree").stdout.strip() == "true":
        return
    ensure_gitignore(ld)
    git(ld, "init", "-q")
    git(ld, "add", "-A")
    git(ld, "commit", "-q", "-m",
        "snapshot before the autonomous formalisation run\n\n"
        "State as downloaded from Aristotle before the driver took over.")
    log(f"initialised git repository in {ld}")


def commit(ld: Path, message: str) -> bool:
    # `-- .` keeps this to the directory it was given. Unscoped, a commit made
    # from the Lean directory would sweep in whatever the author had left
    # uncommitted in the book's LaTeX.
    git(ld, "add", "-A", "--", ".")
    if not git(ld, "diff", "--cached", "--quiet", "--", ".").returncode:
        return False  # nothing staged
    r = subprocess.run(["git", "-C", str(ld), "commit", "-q", "-F", "-", "--", "."],
                       input=message, text=True, capture_output=True)
    if r.returncode:
        log(f"git commit failed: {r.stderr.strip()[:300]}")
        return False
    return True


def stage_workspace(cfg: dict) -> Path:
    """A copy of the workspace to hand to Aristotle: the book and the Lean sources.

    Everything Aristotle should read, and nothing it should not. `.lake` is the
    Mathlib build — some gigabytes, and rebuilt on the other side anyway — and
    `.git` is our history, not theirs. The book's sources go up too, and that is
    the point of creating a project per run: under the old arrangement the
    project kept whatever copy of the book it was made with, which drifted from
    the author's within days and had the agent inventing labels for results
    whose real ones it could not see.
    """
    ld = lean_dir(cfg)
    book = ld.parent
    stage = Path(tempfile.mkdtemp(prefix="aristotle-stage-"))
    for pat in ("*.tex", "*.sty", "*.bib", "main.aux", "main.bbl"):
        for f in book.glob(pat):
            if f.is_file():
                shutil.copy2(f, stage / f.name)
    subprocess.run(["rsync", "-a", "--exclude", ".lake/", "--exclude", ".git/",
                    str(ld), f"{stage}/"], check=True, capture_output=True)
    return stage


def new_project(cfg: dict, prompt: str):
    """Create a project from the current workspace and return it."""
    from aristotlelib.project import Project
    stage = stage_workspace(cfg)
    try:
        return run_async(Project.create_from_directory(prompt, stage))
    finally:
        shutil.rmtree(stage, ignore_errors=True)


# Files every run rewrites in full because they index the whole project: an
# import list, a status table. Two runs that each add their own section collide
# on them every single time, and the collision is never interesting — both
# sections belong. Anything outside this list that conflicts is a real
# disagreement about the same content and stops the run for a human.
#
# THEOREMS.md belongs here for exactly the reason EXERCISES.md does — it is the
# same status table for the numbered results, and ten of the last eleven runs
# rewrote it. Leaving it out meant any local edit to it collided with the next
# run and stopped the queue. The cost of including it: two runs that disagree
# about the *same* table row are union-resolved into two rows rather than
# stopping for a human, so a status table that suddenly lists a result twice is
# worth reading as a disagreement rather than a typo. A conflict in any file
# outside this list still stops the run, even if these conflicted too.
AGGREGATE_FILES = ("EXERCISES.md", "THEOREMS.md", "RequestProject/Exercises.lean")


def resolve_aggregates(root: Path, pre: str = "") -> bool:
    """Union-resolve conflicts in the index files. False if any others remain.

    `root` is the repository root and `pre` the Lean project's prefix inside it,
    because git reports conflicted paths from the root: the index files are
    `transducer-lean/EXERCISES.md` now, not `EXERCISES.md`.
    """
    out = git(root, "diff", "--diff-filter=U", "--name-only").stdout.split()
    names = tuple(pre + f for f in AGGREGATE_FILES)
    if not out or any(f not in names for f in out):
        return False
    for name in out:
        f = root / name
        text = f.read_text(errors="ignore")
        # keep both sides of every region, then drop what that duplicates
        text = re.sub(r"<<<<<<< [^\n]*\n(.*?)=======\n(.*?)>>>>>>> [^\n]*\n",
                      lambda m: (m.group(1) if m.group(1).strip() == m.group(2).strip()
                                 else m.group(1).rstrip("\n") + "\n" + m.group(2)),
                      text, flags=re.S)
        lines, seen, skip, keep = text.splitlines(), set(), False, []
        for line in lines:
            if line.startswith("import "):
                if line in seen:
                    continue
                seen.add(line)
            elif line.startswith("### "):
                skip = line in seen
                seen.add(line)
            elif line.startswith("## "):
                skip = False
            if not skip:
                keep.append(line)
        f.write_text("\n".join(keep).rstrip() + "\n")
        git(root, "add", name)
    log(f"union-resolved {', '.join(out)}")
    return True


def integrate(cfg: dict, st: dict, src: Path, base: str, branch: str,
              message: str) -> str:
    """Merge a returned tree into the local one. Returns 'merged', 'conflict'…

    The local repository is the authoritative copy, so a result is merged into
    it rather than written over it. Because the project was created *from* a
    commit, what comes back is a descendant of a known base — so this is an
    ordinary three-way merge, and an edit made here while the task was running
    survives it. Under the old arrangement the same step was `rsync --delete`,
    which silently discarded local work; every correction made here had to be
    repeated inside a prompt to survive the next harvest.
    """
    ld = lean_dir(cfg)
    pre = lean_prefix(ld)
    if git(ld, "status", "--porcelain", "--", ".").stdout.strip():
        commit(ld, "local edits, committed before integrating a run\n\n"
                   "Made in the working tree while a task was running.")
    work = Path(tempfile.mkdtemp(prefix="aristotle-merge-"))
    tree = work / "t"
    try:
        r = git(ld, "worktree", "add", "--detach", str(tree), base)
        if r.returncode:
            log(f"worktree failed: {r.stderr.strip()[:200]}")
            return "error"
        git(tree, "checkout", "-b", branch)
        # into the Lean directory of the worktree, not over the whole worktree
        dest = tree / pre if pre else tree
        dest.mkdir(parents=True, exist_ok=True)
        subprocess.run(["rsync", "-a", "--delete", "--exclude", ".lake/",
                        "--exclude", ".git", "--exclude", ".gitignore",
                        f"{src}/", f"{dest}/"], check=True, capture_output=True)
        if not commit(tree, message):
            return "empty"          # the run changed nothing
        m = git(ld, "merge", "--no-edit", branch)
        if m.returncode:
            if resolve_aggregates(repo_root(ld), pre):
                c = git(ld, "commit", "--no-edit")
                if not c.returncode:
                    return "merged"
            git(ld, "merge", "--abort")
            return "conflict"
        return "merged"
    finally:
        git(ld, "worktree", "remove", "--force", str(tree))
        shutil.rmtree(work, ignore_errors=True)


def harvest(cfg: dict, st: dict, project, task, target: dict | None,
            base: str | None = None) -> bool:
    """Download a run's files and merge them in. False if it could not be done.

    A false return means the tick must stop: the result is not in the tree, so
    finishing the target or starting the next one would record work that is not
    there and leave the run stranded on its branch.
    """
    ld = lean_dir(cfg)
    tid = target["id"] if target else "external"
    label = status_name(task)

    summary = task.output_summary or task.description or ""
    if summary:
        SUMMARY_DIR.mkdir(parents=True, exist_ok=True)
        (SUMMARY_DIR / f"{task.agent_task_id}.md").write_text(
            f"# {tid} — {label}\n\ntask: {task.agent_task_id}\n"
            f"created: {task.created_at}\n\n{summary}\n")

    with tempfile.TemporaryDirectory() as td:
        arc = Path(td) / "snapshot.tar.gz"
        try:
            run_async(project.get_files(str(arc)))
        except Exception as e:
            log(f"download failed: {e!r}")
            return False
        ex = Path(td) / "x"
        ex.mkdir()
        try:
            try:
                with tarfile.open(arc) as t:
                    t.extractall(ex, filter="data")
            except TypeError:  # python < 3.12
                with tarfile.open(arc) as t:
                    t.extractall(ex)
        except Exception as e:
            log(f"extract failed: {e!r}")
            return False

        src = locate_lean_project(ex, cfg.get("archive_subdir", "transducer-lean"))
        if src is None:
            log("harvest aborted: no Lean project found in the archive")
            return False
        n_lean = len([p for p in src.rglob("*.lean") if ".lake" not in p.parts])
        if n_lean < 20:
            log(f"harvest aborted: archive looks truncated ({n_lean} lean files)")
            return False

        ensure_git(ld)
        ensure_gitignore(ld)
        before = sorry_count(ld)

        if target and target.get("title"):
            head = target["title"]
        elif task.description:
            head = task.description.strip().splitlines()[0]
        else:  # summaries open with a markdown heading, a poor subject line
            head = next((l.strip(" #*") for l in summary.splitlines()
                         if l.strip(" #*")), "(no summary)")
        msg = (f"{tid}: {head[:72]}\n\n"
               f"Aristotle task {task.agent_task_id} ({label}).\n\n"
               f"{summary.strip()}\n\n"
               f"Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>\n")

        base = base or (st.get("current") or {}).get("base") or "HEAD"
        branch = f"aristotle/{task.agent_task_id[:8]}"
        outcome = integrate(cfg, st, src, base, branch, msg)
        if outcome == "conflict":
            review(cfg, st, f"{tid} conflicts with local work",
                   f"The run started from {base[:8]} and its result does not merge "
                   f"cleanly into what the repository holds now — the same files "
                   f"were changed on both sides. Nothing has been lost: the run is "
                   f"on branch `aristotle/{task.agent_task_id[:8]}`.\n\n"
                   f"    git -C {ld} merge aristotle/{task.agent_task_id[:8]}")
            st["paused"] = True
            st["pause_reason"] = f"{tid} needs a merge by hand"
            log("merge conflict — paused")
            return False
        # Did the run touch the sources at all?  Compared against the base the
        # run started from, not against local HEAD, so an edit made here while
        # it was running is not mistaken for its work.  A continuation that
        # writes only prose has nothing left to do and must not be continued
        # again: that is how hyp-polynomial-ideals burned three continuations
        # re-reporting a result it had already finished.
        touched = git(ld, "diff", "--name-only", f"{base}..{branch}").stdout.split()
        lean_touched = any(f.endswith(".lean") for f in touched)
        if target:
            trec = st["targets"].get(target["id"])
            if trec is not None:
                if lean_touched:
                    trec["idle_continues"] = 0
                elif (st.get("current") or {}).get("kind") == "continue":
                    trec["idle_continues"] = trec.get("idle_continues", 0) + 1
        if outcome == "merged":
            log(f"merged {n_lean} lean files from {task.agent_task_id[:8]}; "
                f"sorries {before} -> {sorry_count(ld)}"
                f"{'' if lean_touched else '; no .lean change'}")
        else:
            log(f"integration: {outcome}")
    return True


# --------------------------------------------------------------------------
# submitting
# --------------------------------------------------------------------------

def submit(cfg: dict, st: dict, target: dict, kind: str, extra: str = "") -> bool:
    """Start a run: a project of its own, made from the repository as it stands.

    One project per run rather than one for the whole series. It costs a few
    seconds and about four megabytes, and it buys two things: the agent always
    reads the author's current book and current Lean, and what comes back has a
    known base commit, so it can be merged rather than written over.
    """
    ld = lean_dir(cfg)
    prompt = (build_preamble(target, ld)
              + (extra or target["prompt"])
              + cfg.get("standing_instructions", ""))
    base = git(ld, "rev-parse", "HEAD").stdout.strip()
    if not base:
        log(f"submit refused for {target['id']}: {ld} is not a git repository")
        return False
    try:
        project = new_project(cfg, prompt)
        tasks, _ = run_async(project.get_tasks(limit=1))
        task = tasks[0]
    except Exception as e:
        log(f"submit failed for {target['id']}: {e!r}")
        return False
    rec = st["targets"][target["id"]]
    if kind == "initial":
        rec["sorries_at_start"] = sorry_count(lean_dir(cfg))
    rec["status"] = "running"
    rec["attempts"] += 1
    rec["task_ids"].append(task.agent_task_id)
    # on the target as well as in `current`: `current` holds only the run in
    # flight, so if it is cleared or overwritten the project the run lives in
    # would otherwise be unrecoverable from here
    rec.setdefault("runs", []).append(
        {"task_id": task.agent_task_id, "project_id": str(project.object_id),
         "base": base, "kind": kind, "at": ts()})
    rec["started_at"] = rec["started_at"] or ts()
    st["current"] = {"target_id": target["id"], "task_id": task.agent_task_id,
                     "project_id": str(project.object_id), "base": base,
                     "submitted_at": ts(), "kind": kind}
    log(f"submitted [{kind}] {target['id']} -> task {task.agent_task_id} "
        f"in a new project, from {base[:8]}")
    return True


def finish_target(st: dict, tid: str, status: str, note: str | None = None) -> None:
    rec = st["targets"][tid]
    rec["status"] = status
    rec["finished_at"] = ts()
    if note:
        rec["note"] = note
    st["current"] = None
    log(f"target {tid}: {status}" + (f" — {note}" if note else ""))


# --------------------------------------------------------------------------
# the tick
# --------------------------------------------------------------------------

def tick(cfg: dict, q: list, st: dict) -> None:
    st["ticks"] += 1
    st["last_tick"] = ts()

    if st.get("paused"):
        log(f"paused ({st.get('pause_reason')}) — nothing to do")
        return
    if st.get("finished_at"):
        return

    ensure_api_key()
    cur = st.get("current")

    # ---- 1. a task of ours is outstanding -------------------------------
    if cur:
        try:
            task = get_task(cur["task_id"])
        except Exception as e:
            log(f"could not fetch task {cur['task_id']}: {e!r} — will retry next tick")
            return
        state = status_name(task)
        target = target_by_id(q, cur["target_id"])

        if state in RUNNING:
            started = datetime.fromisoformat(cur["submitted_at"].replace("Z", "+00:00"))
            hours = (now() - started).total_seconds() / 3600
            pct = getattr(task, "percent_complete", None)
            log(f"{cur['target_id']} still {state}"
                + (f" ({pct}%)" if pct is not None else "")
                + f", {hours:.1f}h elapsed", echo=False)
            if hours > cfg.get("stall_warning_hours", 30) and not cur.get("stall_warned"):
                cur["stall_warned"] = True
                log(f"WARNING: task {cur['task_id']} has been running {hours:.0f}h")
                notify(cfg, "Formalisation stalled?",
                       f"{cur['target_id']} running for {hours:.0f}h")
            return

        # terminal — harvest whatever was produced, then decide
        log(f"{cur['target_id']} finished with {state}")
        # No falling back to the project named in config.json. A run of ours
        # always records the project it created; an entry without one is a
        # leftover from the old shared-project design, and integrating that
        # project would merge its whole file state — which is how commit
        # b0a312d silently reverted a week of label corrections.
        pid = cur.get("project_id")
        if not pid:
            review(cfg, st, f"{cur['target_id']} has no project recorded",
                   "This entry predates the per-run projects, so there is no way to "
                   "tell what it was working from. Integrating the shared project "
                   "instead would merge its entire file state over yours. Clear it "
                   "with `driver.py skip` or integrate by hand if you know the "
                   "project:\n\n    driver.py integrate <project-id> --base <commit>")
            st["current"] = None
            log("current has no project id — cleared, nothing integrated")
            return
        try:
            run_project = project_by_id(pid)
        except Exception as e:
            log(f"could not reach the run's project: {e!r} — will retry next tick")
            return
        if not harvest(cfg, st, run_project, task, target):
            return          # nothing was integrated; do not act as though it was
        rec = st["targets"][cur["target_id"]] if target else None

        if state in TERMINAL_STOP:
            # Cancelling used to pause the whole run, on the theory that if you
            # cancelled something you wanted to take over. In practice you
            # cancel this driver's run *because* you have started your own, and
            # pausing then strands both: this one waits, and yours is never
            # integrated because it lives in a project of its own. So note it
            # and carry on to the next target instead.
            tid = cur["target_id"]
            if target:
                finish_target(st, tid, "partial", "canceled by hand")
            st["current"] = None
            review(cfg, st, f"{tid} was canceled",
                   f"Task {cur['task_id']} was canceled, so nothing was integrated for "
                   f"{tid} and the run has moved on to the next target.\n\n"
                   f"If you cancelled it because you were doing the work yourself, that "
                   f"run is in a project of its own and this driver cannot see it. "
                   f"Bring it in with:\n\n"
                   f"    driver.py integrate <project-id> --base <commit>\n\n"
                   f"and then `driver.py requeue {tid}` if more is still wanted from it.")
            notify(cfg, "Formalisation: a task was canceled",
                   f"{tid} — moved on; integrate your own run by hand if there is one")
            log(f"{tid} was canceled — noted, moving on")

        if state in TERMINAL_OK and target:
            still = open_results(lean_dir(cfg), target.get("lean_names", []))
            max_reattempts = target.get("max_reattempts",
                                       cfg.get("max_reattempts_per_target", 2))
            if still and rec["reattempts"] < max_reattempts:
                rec["reattempts"] += 1
                left = ", ".join(still)
                extra = (f"You reported this task as complete, but these declarations still "
                         f"contain `sorry`: {left}.\n\nPlease finish them now. The original "
                         f"instructions were:\n\n{target['prompt']}")
                st["current"] = None
                if submit(cfg, st, target, "reattempt", extra):
                    return
            summary = task.output_summary or ""
            if target["id"].startswith("audit"):
                # an audit exists to be read: its whole point is the findings
                review(cfg, st, f"audit finished: {target['id']}",
                       f"Aristotle's audit report follows. Divergences from the book and "
                       f"status corrections are what to look for.\n\n{summary}")
            elif still:
                review(cfg, st, f"{target['id']} ended with results still open",
                       f"Aristotle reported the task complete and the driver re-prompted it "
                       f"{rec['reattempts']} time(s), but these still contain `sorry`:\n\n"
                       f"  {', '.join(still)}\n\nThe run has moved on to the next target.\n\n"
                       f"Its closing summary:\n\n{summary}")
            note_sorry_delta(cfg, st, rec, target)
            finish_target(st, target["id"], "done",
                          f"still open: {', '.join(still)}" if still else None)

        elif state in TERMINAL_PARTIAL and target:
            # A partial status means the budget ran out, not that work is left:
            # Aristotle reports COMPLETE_WITH_ERRORS for a pass that found
            # nothing to repair just as it does for one cut off mid-proof.  So
            # spend a continuation only when the last one actually changed the
            # sources.  Without this the driver re-submits a finished target
            # until its whole budget is gone.
            wanted = target.get("discharges", [])
            live = live_hypotheses(lean_dir(cfg), wanted)
            idle_cap = cfg.get("stop_after_idle_continues", 1)
            idle = rec.get("idle_continues", 0)
            if wanted and not live:
                review(cfg, st, f"{target['id']} finished: its hypotheses are discharged",
                       f"None of {', '.join(wanted)} is taken as an argument any more, so "
                       f"the target is done and the driver stopped rather than spend the "
                       f"remaining "
                       f"{target.get('max_continues', cfg.get('max_continues', 3)) - rec['continues']} "
                       f"continuation(s) on it.\n\nIts last summary:\n\n"
                       f"{task.output_summary or ''}")
                note_sorry_delta(cfg, st, rec, target)
                finish_target(st, target["id"], "done",
                              f"discharged: {', '.join(wanted)}")
            elif idle >= idle_cap:
                review(cfg, st, f"{target['id']} stopped: nothing left to do",
                       f"The last {idle} continuation(s) changed no `.lean` file — only "
                       f"prose — so the driver stopped rather than spend the remaining "
                       f"{target.get('max_continues', cfg.get('max_continues', 3)) - rec['continues']} "
                       f"continuation(s) on a finished target.\n\nIf you think there was "
                       f"more to do:\n\n    formalize requeue {target['id']}\n\n"
                       f"Its last summary:\n\n{task.output_summary or ''}")
                note_sorry_delta(cfg, st, rec, target)
                finish_target(st, target["id"], "done",
                              f"stopped after {idle} continuation(s) with no .lean change")
            else:
                if rec["continues"] < target.get("max_continues",
                                                 cfg.get("max_continues", 3)):
                    rec["continues"] += 1
                    extra = (f"Please continue exactly where you left off on the following "
                             f"task, picking up from the state of the repository and your "
                             f"own last summary.\n\nThe task was:\n\n{target['prompt']}")
                    st["current"] = None
                    if submit(cfg, st, target, "continue", extra):
                        return
                still = open_results(lean_dir(cfg), target.get("lean_names", []))
                review(cfg, st, f"{target['id']} ran out of budget",
                       f"Budget exhausted after {rec['continues']} continuation(s). Still "
                       f"containing `sorry`: {', '.join(still) if still else 'none detected'}."
                       f"\n\nThe run has moved on. To give this another go:\n"
                       f"    formalize requeue {target['id']}\n\n"
                       f"Its last summary:\n\n{task.output_summary or ''}")
                note_sorry_delta(cfg, st, rec, target)
                finish_target(st, target["id"], "partial",
                              f"budget exhausted after {rec['continues']} continuations; "
                              f"still open: {', '.join(still) if still else 'none detected'}")
                maybe_pause(cfg, st, "partial", f"{target['id']} ran out of budget")

        elif state in TERMINAL_BAD and target:
            if rec["attempts"] <= cfg.get("max_retries_on_failure", 2):
                st["current"] = None
                if submit(cfg, st, target, "retry"):
                    return
            finish_target(st, target["id"], "failed", "server-side failure")
            review(cfg, st, f"{target['id']} failed on the server",
                   f"The task failed {rec['attempts']} time(s) with a server-side error, so "
                   f"the driver gave up on it. This usually means something went wrong at "
                   f"Harmonic's end rather than in the mathematics; retrying later is "
                   f"often enough:\n\n    formalize requeue {target['id']}")
            maybe_pause(cfg, st, "failed", f"{target['id']} failed on the server")

        elif state in TERMINAL_STOP:
            pass          # already dealt with above; not an unhandled status
        else:
            log(f"unhandled status {state}; clearing current task")
            st["current"] = None

    # ---- 2. nothing outstanding: start the next target -------------------
    if st.get("current"):
        return
    if not cfg.get("auto_start_next", True):
        log("auto_start_next is off — not submitting")
        return

    # A run started by hand now lives in a project of its own, so there is
    # nothing here to collide with and nothing to adopt: this driver's runs and
    # yours no longer share a queue. Bring one of yours in with
    #     driver.py integrate <project-id>
    # which merges it the same way, against the commit it was created from.

    nxt = next_pending(st, q)
    if nxt is None:
        st["finished_at"] = ts()
        done = sum(1 for r in st["targets"].values() if r["status"] == "done")
        log(f"queue exhausted: {done}/{len(q)} targets done. Nothing left to submit.")
        notify(cfg, "Formalisation run finished",
               f"{done}/{len(q)} targets done. See driver.py status.")
        return
    submit(cfg, st, nxt, "initial")


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------

def cmd_tick(args) -> None:
    cfg, q = config(), queue()
    st = load_state(q)
    try:
        tick(cfg, q, st)
    finally:
        save_json(STATE_PATH, st)


def cmd_status(args) -> None:
    cfg, q = config(), queue()
    st = load_json(STATE_PATH)
    if st is None:
        print("not started yet — run: driver.py tick")
        return
    ld = lean_dir(cfg)
    icon = {"done": "✓", "partial": "~", "failed": "✗", "running": "▶",
            "pending": "·", "skipped": "-"}
    print(f"project   {cfg['project_id']}")
    print(f"lean dir  {ld}")
    print(f"ticks     {st['ticks']}   last: {st['last_tick']}")
    if st.get("paused"):
        print(f"PAUSED    {st.get('pause_reason')}")
    if st.get("finished_at"):
        print(f"FINISHED  {st['finished_at']}")
    pending = st.get("review_pending", 0)
    if pending:
        print()
        print(f"  ⚠  {pending} item(s) want your attention — see {REVIEW_PATH.name}")
        print(f"     clear with: driver.py reviewed")
    print()
    for tid in st["order"]:
        rec = st["targets"][tid]
        t = target_by_id(q, tid)
        line = f" {icon.get(rec['status'], '?')} {tid:<28} {rec['status']:<8}"
        if rec["attempts"]:
            line += f" attempts={rec['attempts']}"
        if rec["continues"]:
            line += f" continues={rec['continues']}"
        print(line)
        if rec.get("note"):
            print(f"     note: {rec['note']}")
        if t and t.get("results"):
            print(f"     {', '.join(t['results'])}")
    cur = st.get("current")
    print()
    if cur:
        print(f"running: {cur['target_id']} (task {cur['task_id']}, {cur['kind']}, "
              f"since {cur['submitted_at']})")
    if ld.exists():
        print(f"sorries in the Lean sources: {sorry_count(ld)}")
        # `-- .` so this stays the Lean history, not the book's LaTeX commits
        r = git(ld, "log", "--oneline", "-5", "--", ".")
        if r.returncode == 0 and r.stdout.strip():
            print("\nrecent commits:")
            for l in r.stdout.strip().splitlines():
                print(f"  {l}")


def cmd_sync(args) -> None:
    """Harvest the current server state without submitting anything."""
    cfg, q = config(), queue()
    st = load_state(q)
    ensure_api_key()
    project = get_project(cfg)
    tasks, _ = run_async(project.get_tasks(limit=1))
    if not tasks:
        log("no tasks to sync")
        return
    harvest(cfg, st, project, tasks[0], None)
    save_json(STATE_PATH, st)


def cmd_integrate(args) -> None:
    """Merge a project's result into the local repository.

    For runs started by hand: point it at the project and, if the project was
    not made from the current HEAD, at the commit it *was* made from, so the
    merge has the right base.
    """
    cfg, q = config(), queue()
    st = load_state(q)
    ensure_api_key()
    project = project_by_id(args.project)
    tasks, _ = run_async(project.get_tasks(limit=1))
    if not tasks:
        sys.exit("that project has no tasks")
    task = tasks[0]
    state = status_name(task)
    if state in RUNNING:
        sys.exit(f"that task is still {state} — wait for it to finish")
    ld = lean_dir(cfg)
    base = args.base or git(ld, "rev-parse", "HEAD").stdout.strip()
    log(f"integrating {args.project[:8]} ({state}) onto {base[:8]}")
    harvest(cfg, st, project, task, None, base=base)
    save_json(STATE_PATH, st)


def cmd_pause(args) -> None:
    q = queue()
    st = load_state(q)
    st["paused"] = True
    st["pause_reason"] = args.reason or "paused by hand"
    save_json(STATE_PATH, st)
    log(f"paused: {st['pause_reason']}")


def cmd_reviewed(args) -> None:
    """Mark the review inbox as read (REVIEW.md itself is kept as a record)."""
    q = queue()
    st = load_state(q)
    n = st.get("review_pending", 0)
    st["review_pending"] = 0
    save_json(STATE_PATH, st)
    if REVIEW_PATH.exists():
        seen = REVIEW_PATH.with_name("REVIEW-archive.md")
        with seen.open("a") as fh:
            fh.write(REVIEW_PATH.read_text())
        REVIEW_PATH.unlink()
    log(f"cleared {n} review item(s); kept the text in REVIEW-archive.md")


def cmd_resume(args) -> None:
    q = queue()
    st = load_state(q)
    st["paused"] = False
    st["pause_reason"] = None
    st["finished_at"] = None
    save_json(STATE_PATH, st)
    log("resumed")


def cmd_skip(args) -> None:
    q = queue()
    st = load_state(q)
    if args.target not in st["targets"]:
        sys.exit(f"unknown target {args.target}")
    st["targets"][args.target]["status"] = "skipped"
    if (st.get("current") or {}).get("target_id") == args.target:
        st["current"] = None
    save_json(STATE_PATH, st)
    log(f"skipped {args.target}")


def cmd_requeue(args) -> None:
    q = queue()
    st = load_state(q)
    if args.target not in st["targets"]:
        sys.exit(f"unknown target {args.target}")
    rec = st["targets"][args.target]
    rec.update(status="pending", continues=0, reattempts=0, finished_at=None, note=None)
    st["finished_at"] = None
    save_json(STATE_PATH, st)
    log(f"requeued {args.target}")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("tick", help="one step of the state machine (what launchd runs)").set_defaults(f=cmd_tick)
    sub.add_parser("status", help="human-readable progress").set_defaults(f=cmd_status)
    sub.add_parser("sync", help="download the server state without submitting").set_defaults(f=cmd_sync)
    ip = sub.add_parser("integrate", help="merge a hand-started project's result")
    ip.add_argument("project")
    ip.add_argument("--base", help="commit the project was created from (default: HEAD)")
    ip.set_defaults(f=cmd_integrate)
    pp = sub.add_parser("pause", help="stop submitting new tasks")
    pp.add_argument("reason", nargs="?")
    pp.set_defaults(f=cmd_pause)
    sub.add_parser("resume", help="undo pause").set_defaults(f=cmd_resume)
    sub.add_parser("reviewed", help="mark the review inbox as read").set_defaults(f=cmd_reviewed)
    sp = sub.add_parser("skip", help="mark a target as skipped")
    sp.add_argument("target")
    sp.set_defaults(f=cmd_skip)
    rp = sub.add_parser("requeue", help="put a finished target back in the queue")
    rp.add_argument("target")
    rp.set_defaults(f=cmd_requeue)
    args = p.parse_args()

    # one tick at a time, whatever launchd and the user do concurrently
    LOCK_PATH.touch()
    with LOCK_PATH.open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("a tick is already in progress (the scheduled one, most likely); exiting. This says nothing about whether a task is running on Aristotle — see `driver.py status` for that.")
            return
        args.f(args)


if __name__ == "__main__":
    main()
