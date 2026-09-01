#!/bin/bash
# Run `#print axioms` on every alias of `RequestProject/Labels.lean` -- one per
# formalised result of the book and one per formalised exercise -- and report any
# that depends on `sorryAx` or on an axiom other than `propext`,
# `Classical.choice`, `Quot.sound`.  This is the same check that
# `assert_no_sorry` performs inside `Labels.lean`; it is repeated here so that
# the raw `#print axioms` output can be inspected.
#
# Requires a completed `lake build`.  Usage: bash tools/print_axioms.sh [--all]
# With `--all`, the axioms of every alias are printed, not only the offenders.
set -e
cd "$(dirname "$0")/.."
LP=$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':')".lake/build/lib/lean"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
{
  echo 'import RequestProject.Labels'
  grep -o '^alias «[^»]*»' RequestProject/Labels.lean |
    sed 's/^alias /#print axioms Transducers.Book./'
} > "$tmp/PrintAxioms.lean"
LEAN_PATH=$LP lean "$tmp/PrintAxioms.lean" > "$tmp/out" 2>&1
ALL=${1:-}
python3 - "$tmp/out" "$ALL" <<'PY'
import re, sys
text = open(sys.argv[1]).read()
show_all = len(sys.argv) > 2 and sys.argv[2] == "--all"
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = []
entries = [e for e in re.split(r"\n(?=')", text.strip()) if e]
for entry in entries:
    flat = " ".join(entry.split())
    m = re.match(r"'(.*?)' (does not depend on any axioms|depends on axioms: \[(.*)\])", flat)
    if m is None:
        bad.append(("<unparsed>", flat))
        continue
    axioms = set() if m.group(3) is None else {a.strip() for a in m.group(3).split(",")}
    if show_all:
        print(f"{m.group(1)}: {', '.join(sorted(axioms)) or 'none'}")
    if not axioms <= allowed:
        bad.append((m.group(1), sorted(axioms)))
if bad:
    for name, axioms in bad:
        print(f"{name} depends on {axioms}")
    print(f"{len(bad)} problem(s)")
    sys.exit(1)
print(f"all {len(entries)} aliases depend only on propext, Classical.choice, Quot.sound")
PY
