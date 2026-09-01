#!/usr/bin/env python3
"""The label -> number dictionary of the book.

This project never names a result of *Transducers* (M. Bojanczyk) by its number:
numbers move whenever the sources are edited, labels do not.  The numbers are
still worth recording in `LABELS.md`, so that the table can be checked against
the pdf by eye, and this script is what produces them.

The dictionary is read out of the `\\newlabel` entries of the LaTeX auxiliary
file `main.aux`, which LaTeX writes next to `main.tex` and which holds, for
every `\\label`, the number that the label resolved to in the last run.  So the
numbers are the author's, not a reimplementation of the numbering scheme.

Usage
-----

    tools/tex_numbering.py                     print the whole dictionary
    tools/tex_numbering.py LABEL ...           print the number of each LABEL
    tools/tex_numbering.py --check LABELS.md   check the number column of a
                                               markdown table against main.aux

`--book DIR` says where `main.aux` is; it defaults to the parent of the
directory that holds this project, which is where the LaTeX sources live.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
PROJECT = HERE.parent

NEWLABEL = re.compile(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}")

# A row of the dictionary of `LABELS.md`:
#     | C.2.12 | lemma | `lem:output-of-snake-graph-is-regular` | `2dfa.tex` |
ROW = re.compile(r"\|\s*([^|]+?)\s*\|\s*([a-z]+)\s*\|\s*`([^`]+)`\s*\|")


def read_aux(book: pathlib.Path) -> dict[str, str]:
    """The label -> number dictionary of `main.aux`."""
    aux = book / "main.aux"
    if not aux.is_file():
        sys.exit(f"{aux} not found; pass --book DIR")
    numbers: dict[str, str] = {}
    for label, number in NEWLABEL.findall(aux.read_text(encoding="utf-8")):
        if label.endswith("@cref"):
            continue
        numbers.setdefault(label, number)
    return numbers


def check_table(path: pathlib.Path, numbers: dict[str, str]) -> int:
    """Check the number column of a markdown table against `main.aux`."""
    bad = 0
    for line in path.read_text(encoding="utf-8").splitlines():
        row = ROW.match(line)
        if row is None:
            continue
        listed, _kind, label = row.groups()
        if label.startswith("nolabel:"):
            continue
        real = numbers.get(label)
        if real is None:
            print(f"{path}: `{label}` has no \\newlabel in main.aux")
            bad += 1
        elif real != listed:
            print(f"{path}: `{label}` is {real} in main.aux, not {listed}")
            bad += 1
    return bad


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("labels", nargs="*", help="labels to look up, or a file with --check")
    parser.add_argument("--book", type=pathlib.Path, default=PROJECT.parent,
                        help="directory holding main.aux (default: the parent of the project)")
    parser.add_argument("--check", action="store_true",
                        help="treat the arguments as markdown tables and check their number column")
    args = parser.parse_args()

    numbers = read_aux(args.book)

    if args.check:
        bad = 0
        for name in args.labels or ["LABELS.md"]:
            bad += check_table(PROJECT / name if not pathlib.Path(name).exists() else
                               pathlib.Path(name), numbers)
        if bad:
            print(f"{bad} number(s) out of date")
            return 1
        print("every number agrees with main.aux")
        return 0

    if args.labels:
        status = 0
        for label in args.labels:
            number = numbers.get(label)
            if number is None:
                print(f"{label}: not in main.aux")
                status = 1
            else:
                print(f"{label} = {number}")
        return status

    for label, number in numbers.items():
        print(f"{label} = {number}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
