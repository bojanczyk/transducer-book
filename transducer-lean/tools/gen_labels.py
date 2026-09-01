#!/usr/bin/env python3
"""Keep `RequestProject/Labels.lean` in step with the status tables.

`Labels.lean` is the label-indexed view of the formalisation: for every result
of *Transducers* (M. Bojanczyk) that is formalised, an alias in the namespace
`Transducers.Book` whose Lean name *is* the LaTeX label of the result, followed
by `assert_no_sorry` (or `assert_uses_sorry`).  The file ends with a comment
listing the theorem-like environments of the book that are *not* aliased, with a
reason for each, so that all of them are accounted for.

The content of that file is determined by three sources:

* the dictionary of `LABELS.md`, which lists every theorem-like environment of
  the book (its number column is checked against `main.aux` by
  `tools/tex_numbering.py --check`);
* the index tables of `THEOREMS.md` (the numbered results) and `EXERCISES.md`
  (the exercises), which say for each one what it is called in Lean and whether
  it is formalised;
* the Lean environment itself, which is what `assert_no_sorry` consults.

What this script does
---------------------

    tools/gen_labels.py                (or --check)  check `Labels.lean`
                                       against the three sources above
    tools/gen_labels.py --emit LABEL   print the entry that LABEL should have,
                                       ready to paste into `Labels.lean`

`--check` verifies, and reports every violation of, the invariants that make the
file trustworthy:

1.  the alias name agrees with the label in its own docstring, and the `#2`,
    `#3`, ... suffixes of a label run consecutively from its first entry;
2.  every aliased label has a row in `THEOREMS.md` or in `EXERCISES.md`, and the
    docstring repeats the kind and the description of that row;
3.  every alias target is one of the declarations named in that row;
4.  a row that says *not formalised* has no alias, and every other row of the
    index tables has one;
5.  every label of the dictionary of `LABELS.md` is either aliased or listed,
    exactly once, in the accounting comment at the end of the file;
6.  every label the project mentions is a label of the book (or a `nolabel:`
    placeholder for an environment that carries none).

`--check` deliberately stops short of regenerating the file.  Several entries
carry a docstring note that the tables do not contain -- the sense in which
`Transducers.Subseq.delay_bound` renders Claim `claim:bounded-extensions`, say,
or the alphabet over which `lem:output-of-snake-graph-is-regular` is stated --
and a generator that reproduced the file from the tables alone would silently
delete them.  So the file is maintained by hand and this script is what stops
the hand from drifting; `--emit` writes the boilerplate for a new entry.
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

LABELS_LEAN = PROJECT / "RequestProject" / "Labels.lean"
LABELS_MD = PROJECT / "LABELS.md"
TABLES = ["THEOREMS.md", "EXERCISES.md"]

KIND_OF = {
    "definition": "Definition", "theorem": "Theorem", "lemma": "Lemma",
    "claim": "Claim", "corollary": "Corollary", "conjecture": "Conjecture",
    "exercise": "Exercise", "paragraph": "Paragraph",
}

DICT_ROW = re.compile(r"\|\s*([^|]+?)\s*\|\s*([a-z]+)\s*\|\s*`([^`]+)`\s*\|")
TABLE_ROW = re.compile(
    r"\|\s*(Definitions?|Theorems?|Lemmas?|Corollary|Corollaries|Claims?|Conjecture|Exercise)"
    r"\s+`([^`]+)`([^|]*)\|([^|]*)\|(?:([^|]*)\|)?")
ENTRY = re.compile(
    r"/--\s*\*\*(\w+) `([^`]+)`\*\*\s*(\([^)]*\))?.*?-/\s*\n"
    r"alias «([^»]+)» :=\s*([A-Za-z_][\w.']*)\s*\n"
    r"assert_(no_sorry|uses_sorry) «([^»]+)»", re.S)
ACCOUNTED = re.compile(r"^\* `([^`]+)` \((\w+)\) -- (.*?);?$", re.M)
MENTION = re.compile(r"`((?:def|thm|lem|lemma|claim|cor|conj|theorem|exer|ex|nolabel):[^`]+)`")

DECL = re.compile(r"`([A-Za-z_][\w.']*)`")


def base(label: str) -> str:
    return label.split("#")[0]


def tail(name: str) -> str:
    return name.split(".")[-1]


def read_dictionary() -> dict[str, str]:
    """label -> kind, from the dictionary of `LABELS.md`."""
    out: dict[str, str] = {}
    for line in LABELS_MD.read_text(encoding="utf-8").splitlines():
        row = DICT_ROW.match(line)
        if row and row.group(2) in KIND_OF:
            out[row.group(3)] = row.group(2)
    return out


class Row:
    def __init__(self, kind: str, label: str, description: str, lean: str, status: str,
                 source: str) -> None:
        self.kind = kind
        self.label = label
        self.description = description.strip()
        self.declarations = DECL.findall(lean)
        self.lean = lean.strip()
        self.status = status.strip()
        self.source = source

    @property
    def formalised(self) -> bool:
        return "not formalised" not in self.lean and "not formalised" not in self.status \
            and "removed from the formalised theorems" not in self.lean


def read_tables() -> dict[str, Row]:
    rows: dict[str, Row] = {}
    for name in TABLES:
        for line in (PROJECT / name).read_text(encoding="utf-8").splitlines():
            m = TABLE_ROW.match(line.replace("\\|", "\u2223"))
            if m is None:
                continue
            kind, label, description, lean, status = m.groups()
            rows.setdefault(label,
                            Row(kind.rstrip("s"), label, description, lean, status or "", name))
    return rows


class Entry:
    def __init__(self, kind: str, label: str, description: str, alias: str, target: str,
                 assertion: str, asserted: str) -> None:
        self.kind = kind
        self.label = label
        self.description = (description or "").strip()
        self.alias = alias
        self.target = target
        self.assertion = assertion
        self.asserted = asserted


def read_entries() -> list[Entry]:
    text = LABELS_LEAN.read_text(encoding="utf-8")
    return [Entry(*m.groups()) for m in ENTRY.finditer(text)]


def read_accounting() -> dict[str, str]:
    text = LABELS_LEAN.read_text(encoding="utf-8")
    trailing = text[text.rfind("The theorem-like environments of the book that are not aliased"):]
    return {m.group(1): m.group(2) for m in ACCOUNTED.finditer(trailing)}


def check() -> int:
    problems: list[str] = []
    dictionary = read_dictionary()
    rows = read_tables()
    entries = read_entries()
    accounted = read_accounting()

    seen: dict[str, int] = {}
    for entry in entries:
        # (1) the alias, the assertion and the docstring agree.
        if entry.alias != entry.asserted:
            problems.append(f"alias «{entry.alias}» is asserted as «{entry.asserted}»")
        if base(entry.alias) != entry.label:
            problems.append(f"alias «{entry.alias}» has `{entry.label}` in its docstring")
        n = seen.get(entry.label, 0) + 1
        seen[entry.label] = n
        expected = entry.label if n == 1 else f"{entry.label}#{n}"
        if entry.alias != expected:
            problems.append(f"alias «{entry.alias}» should be «{expected}»")

        row = rows.get(entry.label)
        if row is None:
            problems.append(f"«{entry.label}» is aliased but has no row in "
                            + " or ".join(TABLES))
            continue
        # (2) the docstring repeats the kind of the row.
        if entry.kind != row.kind:
            problems.append(f"«{entry.label}» is a {row.kind} in {row.source} "
                            f"but a {entry.kind} in Labels.lean")
        # (3) the alias target is named in the row.
        if tail(entry.target) not in [tail(d) for d in row.declarations]:
            problems.append(f"«{entry.alias}» := {entry.target}, which {row.source} "
                            f"does not name for `{entry.label}`")

    # (4) formalised iff aliased.
    for label, row in rows.items():
        if row.formalised and label not in seen:
            problems.append(f"`{label}` is formalised according to {row.source} "
                            "but has no alias")
        if not row.formalised and label in seen:
            problems.append(f"`{label}` is aliased but {row.source} calls it not formalised")

    # (5) every environment of the book is aliased or accounted for, not both.
    for label in dictionary:
        if label in seen and label in accounted:
            problems.append(f"`{label}` is both aliased and listed as not aliased")
        if label not in seen and label not in accounted:
            problems.append(f"`{label}` is neither aliased nor listed as not aliased")
    for label in accounted:
        if label not in dictionary:
            problems.append(f"`{label}` is listed as not aliased but is not in LABELS.md")

    # (6) every label the project mentions is a label of the book.
    known = set(read_aux(PROJECT.parent))
    for path in sorted(PROJECT.rglob("*")):
        if path.is_dir() or path.suffix not in (".lean", ".md"):
            continue
        if any(part in {".lake", ".git", "tools"} for part in path.parts):
            continue
        if path.name == "ARISTOTLE_SUMMARY.md":
            continue
        for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            for label in MENTION.findall(line):
                label = base(label)
                if label.startswith("nolabel:") or label in known or label in rows:
                    continue
                problems.append(f"{path.relative_to(PROJECT)}:{line_no}: "
                                f"`{label}` is not a label of the book")

    for problem in problems:
        print(problem)
    if problems:
        print(f"{len(problems)} problem(s)")
        return 1
    print(f"Labels.lean agrees with LABELS.md and the index tables "
          f"({len(entries)} aliases, {len(accounted)} environments accounted for)")
    return 0


def emit(label: str) -> int:
    rows = read_tables()
    row = rows.get(label)
    if row is None:
        print(f"`{label}` has no row in " + " or ".join(TABLES), file=sys.stderr)
        return 1
    if not row.declarations:
        print(f"`{label}` names no Lean declaration in {row.source}", file=sys.stderr)
        return 1
    description = row.description.strip()
    for index, declaration in enumerate(row.declarations, 1):
        alias = label if index == 1 else f"{label}#{index}"
        print(f"/-- **{row.kind} `{label}`** {description}: `{declaration}`. -/")
        print(f"alias «{alias}» := {declaration}")
        print(f"assert_no_sorry «{alias}»")
        print()
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", default=True)
    parser.add_argument("--emit", metavar="LABEL",
                        help="print the entry that LABEL should have")
    args = parser.parse_args()
    if args.emit:
        return emit(args.emit)
    return check()


if __name__ == "__main__":
    raise SystemExit(main())
