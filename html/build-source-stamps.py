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
  per page      `% context stamp 4d9e0f21` at the top of every block on a page,
                covering what that page is shown from elsewhere: the numbers of
                the labels it \\refs, and the bibliography entries it cites. A
                \\ref renders as whatever number the continuous build gave it,
                and a chapter showing last week's numbering is stale in the same
                silent way as one whose text is out of date.
  shared        one stamp in latex-preambles/book.tex, which is part of *every*
                block's key by construction, covering what every block reads
                through the preamble: macros.sty, transducer-macros.sty,
                knowledges.tex and the picture file.

The numbers are per page and not shared for a reason worth stating, because the
obvious arrangement is the wrong one. Hashing every label in the book into the
shared stamp is simpler and correct, and it was what this script did until
2026-09-08 — but ourexamplecounter and the theorem counters run through the
whole book, so inserting one theorem in Part A changes the number of everything
after it, and every build following any insertion was a cold build of all 229
blocks. Chapters barely refer to each other: of the labels referenced anywhere,
116 are used by a single chapter and only four by more than three. Per page, a
renumbering recompiles the pages that show the number.

Only the numbers are taken from main.aux, not the whole file: page numbers move
whenever anything above them grows, and recompiling a chapter because a
paragraph above it got longer would make every build a cold one. main.bbl is
read the same way, entry by entry rather than whole, so that adding a reference
recompiles the chapters citing it rather than the book.

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
BBL = BODY / "main.bbl"                     # biber's output; every \cite reads it

# Everything every block reads through the preamble.
SHARED = ["macros.sty", "transducer-macros.sty", "knowledges.tex",
          "transducer-book-pics.pdf"]

# (content page, the source it inputs). The preface is the landing page and so
# lives in _index.md; the chapters are one per \input in ../main.tex.
PAGES = [
    ("_index", "preface.tex"),
    ("01-introduction", "intro.tex"),
    ("02-mealy-machines-introduction", "partAMealy/intro.tex"),
    ("03-mealy-machines", "partAMealy/mealy.tex"),
    ("04-krohn-rhodes", "partAMealy/krohn-rhodes.tex"),
    ("04z-mealy-machines-references", "partAMealy/bib-notes.tex"),
    ("05-rational-functions-introduction", "partBRational/intro.tex"),
    ("06-rational-relations", "partBRational/rational-relations.tex"),
    ("07-rational-functions", "partBRational/rational-functions.tex"),
    ("08-weighted-automata", "partBRational/weighted.tex"),
    ("09-machine-independent", "partBRational/myhill-nerode.tex"),
    ("09z-rational-functions-references", "partBRational/bib-notes.tex"),
    ("10-regular-functions-introduction", "partCRegular/intro.tex"),
    ("11-prime-regular-functions", "partCRegular/regular-primes.tex"),
    ("12-two-way-transducers", "partCRegular/2dfa.tex"),
    ("13-streaming-string-transducers", "partCRegular/sst.tex"),
    ("14-logic", "partCRegular/logic.tex"),
    ("14a-combinators", "partCRegular/combinators.tex"),
    ("14z-regular-functions-references", "partCRegular/bib-notes.tex"),
    ("15-polyregular-functions-introduction", "partDPolyregular/intro.tex"),
    ("16-for-transducers", "partDPolyregular/for.tex"),
    ("17-pebble-transducers", "partDPolyregular/pebble.tex"),
    ("17z-polyregular-functions-references", "partDPolyregular/bib-notes.tex"),
]

STAMP = re.compile(r"^% source stamp [^\n]*\n", re.M)
CONTEXT = re.compile(r"^% context stamp [^\n]*\n", re.M)
NEWLABEL = re.compile(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}")

# What a block can show that comes from outside itself: a number it \refs, and
# a citation label it prints. Both are looked up rather than written out, so a
# block is stale when the *answer* changes even though its own text has not.
# The book uses exactly these three reference commands and no others, no
# \crefrange, and no macro of its own that wraps them — checked, and worth
# re-checking if a fourth ever appears, because a reference this misses is a
# number that silently stops being updated.
REF = re.compile(r"\\(?:ref|cref|eqref)\s*\*?\s*\{([^}]*)\}")
CITE = re.compile(r"\\cite\s*(?:\[[^\]]*\]\s*)*\{([^}]*)\}")
BLOCK_OPEN = re.compile(r"\{\{<\s*latex\b[^>]*>\}\}\n")


def digest(*parts):
    h = hashlib.sha256()
    for part in parts:
        h.update(part if isinstance(part, bytes) else part.encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()[:8]


def label_numbers():
    """label -> the number the continuous build resolved it to; pages left out.

    A \\ref is typeset as this number, so a block showing it is stale when the
    number moves. The page recorded beside it in main.aux moves far more often
    and changes nothing anyone can see here.
    """
    if not AUX.exists():
        return {}
    aux = AUX.read_text(errors="ignore")
    return {m.group(1): m.group(2) for m in NEWLABEL.finditer(aux)}


def bbl_entries():
    """citation key -> the entry biber wrote for it in ../main.bbl.

    The label a \\cite prints — [Mea55] — and everything the third column shows
    about a reference come from here, so editing an entry in bib.bib has to
    recompile the blocks that cite it. Nothing else in the file matters: biber
    rewrites the whole of main.bbl on every run, and hashing it whole would make
    a new citation anywhere a cold build for the entire book.
    """
    if not BBL.exists():
        return {}
    text = BBL.read_text(errors="ignore")
    return {m.group(1): m.group(2)
            for m in re.finditer(r"\\entry\{([^}]+)\}(.*?)\\endentry", text, re.S)}


def keys_in(pattern, text):
    """The comma-separated keys of every `pattern` command in `text`."""
    out = set()
    for m in pattern.finditer(text):
        out.update(k.strip() for k in m.group(1).split(","))
    return {k for k in out if k}


def context_stamp(text, numbers, entries):
    """What this page is shown from elsewhere: the numbers and entries it uses.

    Deliberately per page rather than per block. A page's exercises are
    regenerated from its chapter by build-exercises.py and share its subject
    matter, so a reference that moves in one usually matters to the others; and
    one stamp per page means build-exercises.py and this script cannot disagree
    about which block owns which reference.
    """
    refs = sorted(keys_in(REF, text))
    cites = sorted(keys_in(CITE, text))
    return digest("\n".join(f"{k}={numbers.get(k, 'unresolved')}" for k in refs),
                  "\n".join(entries.get(k, "uncited") for k in cites))


def shared_stamp():
    parts = []
    for name in SHARED:
        path = BODY / name
        parts.append(path.read_bytes() if path.exists() else b"missing")
    return digest(*parts)


def source_stamp(source):
    path = BODY / source
    return digest(path.read_bytes() if path.exists() else b"missing")


def stamp_blocks(text, line):
    """Put `line` at the top of every {{< latex >}} block on the page."""
    return BLOCK_OPEN.sub(lambda m: m.group(0) + line + "\n", CONTEXT.sub("", text))


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
            " ../macros.sty, ../transducer-macros.sty or the pictures recompile"
            " every block")
    text = PREAMBLE.read_text(encoding="utf-8")
    stamped = restamp(text, want)
    if stamped != text:
        changes.append(f"{PREAMBLE.relative_to(ROOT)}: shared inputs changed")
        if write:
            PREAMBLE.write_text(stamped, encoding="utf-8")

    numbers, entries = label_numbers(), bbl_entries()

    for slug, source in PAGES:
        page = CONTENT / f"{slug}.md"
        if not page.exists() or not (BODY / source).exists():
            print(f"  skipped {slug}: no {page.name if not page.exists() else source}",
                  file=sys.stderr)
            continue
        text = page.read_text(encoding="utf-8")
        why = []

        stamped = restamp(text, f"% source stamp {source}:{source_stamp(source)}",
                          before=f"\\input{{../../../{source}}}")
        if stamped != text:
            why.append(f"{source} changed")

        # The chapter and the exercises beside it are read together: the
        # exercises are generated from the chapter, and a \ref in a solution
        # resolves through the same main.aux as one in the body.
        was = CONTEXT.search(stamped)
        line = "% context stamp " + context_stamp(
            (BODY / source).read_text(errors="ignore") + stamped, numbers, entries)
        stamped = stamp_blocks(stamped, line)
        if was is None or was.group(0).strip() != line:
            why.append("a number or reference it shows changed" if was
                       else "no context stamp yet")

        if stamped != text:
            changes.append(f"content/{page.name}: " + ", ".join(why or ["stamps moved"]))
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
