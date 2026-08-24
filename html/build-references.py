#!/usr/bin/env python3
"""Validate the label set and compute per-chapter counter resets.

Each chapter is compiled in isolation (one reflowtex block per content/*.md
page, \\input-ing the book's own ../*.tex chapter body — see any content/*.md
for the pattern) rather than as part of one continuous document, so three
counters that the continuous main.tex build accumulates for free need an
explicit \\setcounter at the top of each chapter's block:

  mypart, section  — structural, and static: which part/section a chapter
                     opens in. Hardcoded below (CHAPTERS) since that almost
                     never changes.
  ourexamplecounter — macros.sty's numbered-example counter. Unlike
                     section-scoped theorem/lemma/etc. (aliased to `theorem`,
                     which amsthm already resets every section on its own),
                     this one counts \\begin{myexample} continuously across
                     the *entire* book with no reset — so its correct
                     starting value for a chapter depends on exactly how many
                     examples every earlier chapter contains, and drifts
                     whenever any chapter's example count changes.

This script computes that value by walking CHAPTERS in book order and
counting \\begin{myexample} in each one's source, then cross-checks the result
against ../main.aux — the continuous PDF build's own record of what number
each \\label inside a myexample actually resolved to —
so a mismatch here means either CHAPTERS' reading order or a chapter's source
has drifted, not just that this script disagrees with itself.

Run it after editing any chapter's source:

    python3 build-references.py           # report; exit 1 if content/ has drifted
    python3 build-references.py --write   # …and rewrite the \\setcounter lines

rebuild.sh passes --write, so the counters follow the sources by themselves;
running it bare is the read-only check.
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent   # html/
BODY = ROOT.parent                       # the book repo root — html/ lives inside it,
AUX = BODY / "main.aux"                  # so the sources are simply one level up
CONTENT = ROOT / "content"
SETCOUNTER_RE = re.compile(r"(\\setcounter\{ourexamplecounter\}\{)(\d+)(\})")

# (page slug, source, mypart counter, section counter before source is input)
CHAPTERS = [
    ("01-introduction", "intro.tex", 0, 0),
    ("02-mealy-machines-introduction", "mealy-intro.tex", 1, 0),
    ("03-mealy-machines", "mealy.tex", 1, 0),
    ("04-krohn-rhodes", "krohn-rhodes.tex", 1, 1),
    ("05-rational-functions-introduction", "rational-intro.tex", 2, 0),
    ("06-rational-relations", "rational-relations.tex", 2, 0),
    ("07-rational-functions", "rational-functions.tex", 2, 1),
    ("08-weighted-automata", "weighted.tex", 2, 2),
    ("09-machine-independent", "myhill-nerode.tex", 2, 3),
    ("10-regular-functions-introduction", "regular-intro.tex", 3, 0),
    ("11-prime-regular-functions", "regular-primes.tex", 3, 0),
    ("12-two-way-transducers", "2dfa.tex", 3, 1),
    ("13-streaming-string-transducers", "sst.tex", 3, 2),
    ("14-logic", "logic.tex", 3, 3),
    ("15-polyregular-functions-introduction", "polyregular-intro.tex", 4, 0),
    ("16-for-transducers", "polyregular-for.tex", 4, 0),
    ("17-pebble-transducers", "polyregular-pebble.tex", 4, 1),
]

MYEXAMPLE_RE = re.compile(r"\\begin\{myexample\}(?:\[[^\]]*\])?\s*(?:\\label\{([^}]+)\})?")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:ref|eqref|pageref)\{([^}]+)\}")
# \newlabel{name}{{number}{page}{context}{counter-type.something}{}} — context
# is the visible section-heading-like text hyperref stores for backrefs, which
# can itself contain braces (e.g. "...variable {\tt q}..."), so a regex can't
# reliably skip over it to reach the counter-type field. Only number/page (the
# first two bracket groups, never containing braces) are parsed structurally;
# which \newcounter a label's number came from is instead a plain substring
# check below — "{counter-name" can only occur in that field.
NEWLABEL_RE = re.compile(r"^\\newlabel\{([^@][^}]*)\}\{\{([^{}]*)\}\{([^{}]*)\}")


def strip_comments(text: str) -> str:
    return "\n".join(re.sub(r"(?<!\\)%.*$", "", line) for line in text.splitlines())


def main(write: bool = False) -> None:
    sources = {slug: strip_comments((BODY / source).read_text(encoding="utf-8"))
               for slug, source, _, _ in CHAPTERS}

    aux = {}
    for line in AUX.read_text(encoding="utf-8", errors="replace").splitlines():
        m = NEWLABEL_RE.match(line)
        if m:
            is_example = "{ourexamplecounter" in line
            aux[m.group(1)] = {"number": m.group(2), "page": m.group(3),
                                "is_example": is_example}

    # ── \ref/\eqref/\pageref targets must all resolve in the full book ───────
    referenced = set()
    for text in sources.values():
        referenced.update(REF_RE.findall(text))
    missing_aux = sorted(referenced - aux.keys())
    if missing_aux:
        raise SystemExit(f"references absent from main.aux: {missing_aux}")

    # ── ourexamplecounter: compute each chapter's starting value, and cross- ──
    # check every myexample \label's computed number against what the
    # continuous PDF build actually recorded for it.
    print("ourexamplecounter starting values (\\setcounter in each chapter's block):")
    running = 0
    starts = {}
    mismatches = []
    for slug, source, _, _ in CHAPTERS:
        starts[slug] = running
        print(f"  {slug:42s} {source:28s} {running}")
        n = running
        for m in MYEXAMPLE_RE.finditer(sources[slug]):
            n += 1
            label = m.group(1)
            if not label:
                continue
            recorded = aux.get(label)
            if recorded is None:
                mismatches.append(f"{label}: no \\newlabel in main.aux")
            elif not recorded["is_example"]:
                mismatches.append(f"{label}: main.aux doesn't have it on "
                                   f"ourexamplecounter")
            elif int(recorded["number"]) != n:
                mismatches.append(f"{label}: computed Example {n}, "
                                   f"main.aux says {recorded['number']}")
        running = n

    if mismatches:
        print("\nourexamplecounter MISMATCHES (fix CHAPTERS' order or check for a source "
              "edit that changed an example count upstream of this one):", file=sys.stderr)
        for msg in mismatches:
            print(f"  {msg}", file=sys.stderr)
        raise SystemExit(1)

    print(f"\nOK — {len(referenced)} referenced label(s) resolve, and every myexample "
          f"\\label's computed number matches main.aux.")

    sync_content(starts, write)


def sync_content(starts: dict[str, int], write: bool) -> None:
    """Carry the computed starting values into each chapter's \\setcounter line.

    The numbers above are only correct as long as every content/*.md agrees
    with them, and they shift whenever an example is added or removed anywhere
    earlier in the book — so this writes them out rather than leaving 17 files
    to be hand-edited from the printout.
    """
    stale = []
    for slug, want in starts.items():
        page = CONTENT / f"{slug}.md"
        text = page.read_text(encoding="utf-8")
        m = SETCOUNTER_RE.search(text)
        if m is None:
            stale.append(f"{page.name}: no \\setcounter{{ourexamplecounter}} line")
            continue
        if int(m.group(2)) == want:
            continue
        stale.append(f"{page.name}: {m.group(2)} → {want}")
        if write:
            page.write_text(SETCOUNTER_RE.sub(rf"\g<1>{want}\g<3>", text, count=1),
                            encoding="utf-8")

    if not stale:
        print("content/*.md \\setcounter lines already in step.")
    elif write:
        print("updated content/*.md \\setcounter lines:")
        for msg in stale:
            print(f"  {msg}")
    else:
        print("\ncontent/*.md \\setcounter lines are out of date "
              "(re-run with --write to fix):", file=sys.stderr)
        for msg in stale:
            print(f"  {msg}", file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true",
                        help="rewrite content/*.md's \\setcounter{ourexamplecounter} lines")
    main(parser.parse_args().write)
