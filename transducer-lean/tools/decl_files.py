#!/usr/bin/env python3
"""Locate the Lean file in which each declaration of the index tables is proved.

`THEOREMS.md` and `EXERCISES.md` name, for every formalised result of the book,
the Lean declarations that render it.  This script finds the file of each such
declaration by scanning `RequestProject/` for its definition, so that the `File`
column of the index tables can be checked (`--check`) or printed (`--list`).

A declaration is looked for as the subject of a `theorem`, `lemma`, `def`,
`abbrev`, `structure`, `inductive` or `noncomputable def` command, possibly
inside a `namespace`, and the name printed is relative to `RequestProject/`.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
PROJECT = HERE.parent
SRC = PROJECT / "RequestProject"
sys.path.insert(0, str(HERE))

from gen_labels import TABLE_ROW, DECL  # noqa: E402

DEF = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|alias)\s+"
    r"([A-Za-z_][\w.']*)")
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][\w.']*)")
SECTION = re.compile(r"^section\b")
END = re.compile(r"^end\b")


def index() -> dict[str, list[str]]:
    """fully qualified declaration name -> files of `RequestProject/` defining it."""
    out: dict[str, list[str]] = {}
    for path in sorted(SRC.rglob("*.lean")):
        stack: list[str] = []
        for line in path.read_text(encoding="utf-8").splitlines():
            ns = NAMESPACE.match(line)
            if ns:
                stack.append(ns.group(1))
                continue
            if SECTION.match(line):
                stack.append("")
                continue
            if END.match(line):
                if stack:
                    stack.pop()
                continue
            d = DEF.match(line)
            if d:
                rel = str(path.relative_to(SRC))
                full = ".".join([s for s in stack if s] + [d.group(1)])
                out.setdefault(full, []).append(rel)
    return out


def lookup(where: dict[str, list[str]], name: str) -> list[str]:
    """The files defining `name`, which the tables may abbreviate."""
    if name in where:
        return where[name]
    hits: list[str] = []
    for full, files in where.items():
        if full == name or full.endswith("." + name):
            hits += files
    return hits


def rows() -> list[tuple[str, str, list[str], str]]:
    """(table, label, declarations, file column) of every row of the index.

    Only the `## Index` section of `THEOREMS.md` carries a `File` column;
    `EXERCISES.md` is maintained by several runs at once and is left alone.
    """
    out = []
    for name in ("THEOREMS.md",):
        inside = False
        for line in (PROJECT / name).read_text(encoding="utf-8").splitlines():
            if line.startswith("## "):
                inside = line == "## Index"
            if not inside:
                continue
            m = TABLE_ROW.match(line.replace("\\|", "\u2223"))
            if m is None:
                continue
            _, label, _, lean, status = m.groups()
            cols = [c.strip() for c in
                    line.replace("\\|", "\u2223").strip().strip("|").split("|")]
            column = cols[3].replace("\u2223", "\\|") if len(cols) > 3 else ""
            if "not formalised" in lean or "not formalised" in (status or "") \
                    or "removed from the formalised theorems" in lean:
                continue
            out.append((name, label, DECL.findall(lean), column))
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true",
                    help="check the `File` column of the index tables")
    args = ap.parse_args()
    where = index()
    problems = 0
    for table, label, decls, column in rows():
        files = lookup(where, decls[0]) if decls else []
        if args.check:
            # Rows with no declaration of this project (a result that is not
            # formalised, or one rendered by a declaration of Mathlib) carry an
            # em dash and nothing to check.
            if not decls or column == "—":
                continue
            if not files:
                print(f"{table}: `{label}`: no file found for `{decls[0]}`")
                problems += 1
                continue
            if not any(f in column for f in files):
                print(f"{table}: `{label}`: file column is `{column}`, "
                      f"but `{decls[0]}` is in {files}")
                problems += 1
        else:
            print(f"{label}\t{', '.join(files) or '-'}")
    if args.check:
        print(f"{problems} problem(s)" if problems else "the file columns agree with the sources")
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
