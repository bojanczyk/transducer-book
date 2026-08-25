#!/usr/bin/env python3
"""Make each compiled block depend on the sources it actually reads.

reflowtex caches a compiled block under a key that is the hash of the block's
own text plus its preamble (see src/encode/pipeline.py's content_key), and
prebuild.py skips any block whose key it already has. That is exactly right for
a block that *contains* its LaTeX. Ours do not: a chapter's block is three
\\setcounter lines and

    \\input{../../../intro.tex}

so its text — and therefore its key, and therefore what the reader sees — does
not move when the chapter itself is rewritten. Editing intro.tex changed
nothing on the site until someone thought to pass --force, which is a silent
wrong answer: the worst kind.

Rather than copy the chapters into content/ to be hashed (there is deliberately
one copy of the book's LaTeX, and it is the one the PDF builds from), this
writes a stamp of each source's hash into the block that inputs it. The stamp
is a LaTeX comment, so it changes the key and nothing else.

Two kinds of dependency, in two places:

  per chapter   `% source stamp intro.tex:8a3f2b1c` inside the chapter's block,
                so that editing that chapter recompiles that chapter.
  shared        one stamp in latex-preambles/book.tex, which is part of *every*
                block's key by construction, covering what every block reads
                through the preamble: macros.sty, knowledges.tex, the picture
                file — and the numbers in ../main.aux, since a \\ref renders as
                whatever number the continuous build gave it, and a chapter
                showing last week's numbering is stale in the same silent way.

Only the numbers are taken from main.aux, not the whole file: page numbers move
whenever anything above them grows, and recompiling the entire book because a
paragraph got longer would make every build a cold one.

    python3 build-source-stamps.py           # report; exit 1 if a stamp is stale
    python3 build-source-stamps.py --write   # …and bring the stamps up to date

rebuild.sh passes --write, and runs this before prebuild.py so the keys are
right when the caching decision is made.
"""

import argparse
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent      # html/
BODY = ROOT.parent                          # the book repo root
CONTENT = ROOT / "content"
PREAMBLE = ROOT / "latex-preambles" / "book.tex"
AUX = ROOT / ".aux-snapshot" / "main.aux"   # what the blocks read; see rebuild.sh

# Everything every block reads through the preamble.
SHARED = ["macros.sty", "knowledges.tex", "transducer-book-pics.pdf"]

# (content page, the source it inputs). The preface is the landing page and so
# lives in _index.md; the chapters are one per \input in ../main.tex.
PAGES = [
    ("_index", "preface.tex"),
    ("01-introduction", "intro.tex"),
    ("02-mealy-machines-introduction", "mealy-intro.tex"),
    ("03-mealy-machines", "mealy.tex"),
    ("04-krohn-rhodes", "krohn-rhodes.tex"),
    ("05-rational-functions-introduction", "rational-intro.tex"),
    ("06-rational-relations", "rational-relations.tex"),
    ("07-rational-functions", "rational-functions.tex"),
    ("08-weighted-automata", "weighted.tex"),
    ("09-machine-independent", "myhill-nerode.tex"),
    ("10-regular-functions-introduction", "regular-intro.tex"),
    ("11-prime-regular-functions", "regular-primes.tex"),
    ("12-two-way-transducers", "2dfa.tex"),
    ("13-streaming-string-transducers", "sst.tex"),
    ("14-logic", "logic.tex"),
    ("15-polyregular-functions-introduction", "polyregular-intro.tex"),
    ("16-for-transducers", "polyregular-for.tex"),
    ("17-pebble-transducers", "polyregular-pebble.tex"),
]

STAMP = re.compile(r"^% source stamp [^\n]*\n", re.M)
NEWLABEL = re.compile(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}")


def digest(*parts):
    h = hashlib.sha256()
    for part in parts:
        h.update(part if isinstance(part, bytes) else part.encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()[:8]


def numbers():
    """Every label's number, as the continuous build resolved it — pages left out.

    A \\ref in a chapter is typeset as this number, so the chapter has to be
    recompiled when it changes. The page beside it in main.aux moves far more
    often and changes nothing anyone can see here.
    """
    if not AUX.exists():
        return "no-aux"
    aux = AUX.read_text(errors="ignore")
    return "\n".join(sorted(f"{m.group(1)}={m.group(2)}" for m in NEWLABEL.finditer(aux)))


def shared_stamp():
    parts = []
    for name in SHARED:
        path = BODY / name
        parts.append(path.read_bytes() if path.exists() else b"missing")
    parts.append(numbers())
    return digest(*parts)


def source_stamp(source):
    path = BODY / source
    return digest(path.read_bytes() if path.exists() else b"missing")


def restamp(text, line, before=None):
    """Replace the stamp in `text`, or insert it — before `before` if given."""
    if STAMP.search(text):
        return STAMP.sub(line + "\n", text, count=1)
    if before and before in text:
        return text.replace(before, line + "\n" + before, 1)
    return line + "\n" + text


def main(write):
    changes = []

    want = ("% source stamp shared:" + shared_stamp() +
            " — maintained by build-source-stamps.py; it is what makes editing"
            " ../macros.sty, the pictures or the book's numbering recompile"
            " every block")
    text = PREAMBLE.read_text(encoding="utf-8")
    stamped = restamp(text, want)
    if stamped != text:
        changes.append(f"{PREAMBLE.relative_to(ROOT)}: shared inputs changed")
        if write:
            PREAMBLE.write_text(stamped, encoding="utf-8")

    for slug, source in PAGES:
        page = CONTENT / f"{slug}.md"
        if not page.exists() or not (BODY / source).exists():
            print(f"  skipped {slug}: no {page.name if not page.exists() else source}",
                  file=sys.stderr)
            continue
        text = page.read_text(encoding="utf-8")
        want = f"% source stamp {source}:{source_stamp(source)}"
        stamped = restamp(text, want, before=f"\\input{{../../../{source}}}")
        if stamped != text:
            changes.append(f"content/{page.name}: {source} changed")
            if write:
                page.write_text(stamped, encoding="utf-8")

    if not changes:
        print("source stamps are up to date.")
        return
    if write:
        print("source stamps updated — the blocks below will be recompiled:")
        for c in changes:
            print(f"  {c}")
        return
    print("\nsource stamps are out of date (re-run with --write):", file=sys.stderr)
    for c in changes:
        print(f"  {c}", file=sys.stderr)
    raise SystemExit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help="bring the stamps up to date")
    main(parser.parse_args().write)
