#!/usr/bin/env python3
"""Find (and rewrite) the places where a result of the book is named by its number.

This project identifies a result of *Transducers* (M. Bojanczyk) by its LaTeX
`\\label`, never by its number: a number moves whenever a result is inserted
earlier in the book, and a docstring that says `Theorem C.4.1` then quietly
refers to something else, with nothing to catch it.  This script is what
catches it.

It scans the Lean sources and the markdown of this project for phrases of the
form

    Theorem C.4.1        Lemma A.2.5        Definition B.1.3
    Corollary C.2.7      Claim B.4.9        Conjecture C.1.5

and reports each one, together with the label that `main.aux` gives to that
number, if there is exactly one.  With `--fix` it rewrites them, turning

    **Theorem C.4.1.**   into   **Theorem `thm:mso-logic-languages`.**

Usage
-----

    tools/relabel.py                 report every book number found (exit 1 if any)
    tools/relabel.py --fix           rewrite the unambiguous ones in place
    tools/relabel.py --book DIR      where main.aux lives

`ARISTOTLE_SUMMARY.md` is skipped: it is a dated log of past work, and rewriting
what an earlier entry said would falsify it.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
PROJECT = HERE.parent
sys.path.insert(0, str(HERE))

from tex_numbering import read_aux  # noqa: E402

KINDS = "Theorem|Lemma|Definition|Corollary|Claim|Conjecture|Proposition|Example|Exercise"
NUMBER = re.compile(rf"\b({KINDS})s?\s+((?:[A-Z]?\.)?[A-Z]?\.?\d+(?:\.\d+)+)")

SKIP_FILES = {"ARISTOTLE_SUMMARY.md"}
SKIP_DIRS = {".lake", ".git", "tools"}

CODE_SPAN = re.compile(r"`[^`]*`")


def in_code_span(line: str, start: int, end: int) -> bool:
    """Is the slice `line[start:end]` inside a pair of backticks?

    A number quoted that way is an example of the notation this project avoids,
    not a reference to a result, so it is left alone.
    """
    return any(span.start() < start and end <= span.end() for span in CODE_SPAN.finditer(line))


def sources() -> list[pathlib.Path]:
    out = []
    for path in sorted(PROJECT.rglob("*")):
        if path.is_dir():
            continue
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        if path.name in SKIP_FILES:
            continue
        if path.suffix in (".lean", ".md"):
            out.append(path)
    return out


def by_number(numbers: dict[str, str]) -> dict[str, list[str]]:
    """The inverse dictionary: number -> the labels that carry it."""
    inverse: dict[str, list[str]] = {}
    for label, number in numbers.items():
        inverse.setdefault(number, []).append(label)
    return inverse


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book", type=pathlib.Path, default=PROJECT.parent)
    parser.add_argument("--fix", action="store_true", help="rewrite the unambiguous ones")
    args = parser.parse_args()

    inverse = by_number(read_aux(args.book))

    found = 0
    for path in sources():
        text = path.read_text(encoding="utf-8")
        changed = text
        for line_no, line in enumerate(text.splitlines(), 1):
            for match in NUMBER.finditer(line):
                kind, number = match.groups()
                if in_code_span(line, match.start(), match.end()):
                    continue
                labels = inverse.get(number, [])
                rel = path.relative_to(PROJECT)
                if len(labels) == 1:
                    label = labels[0]
                    print(f"{rel}:{line_no}: {kind} {number} -> `{label}`")
                    if args.fix:
                        changed = changed.replace(f"{kind} {number}", f"{kind} `{label}`")
                else:
                    what = "no label" if not labels else f"ambiguous: {labels}"
                    print(f"{rel}:{line_no}: {kind} {number} ({what})")
                found += 1
        if args.fix and changed != text:
            path.write_text(changed, encoding="utf-8")

    if found:
        print(f"{found} book number(s) found"
              + (" and rewritten where unambiguous" if args.fix else ""))
        return 0 if args.fix else 1
    print("no result of the book is named by its number")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
