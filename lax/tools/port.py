#!/usr/bin/env python3
"""Port source modules of transducer-lean into a Lax proof package, verbatim.

    port.py --pkg Lax765601Proofs --dest lax/mealy-machines/proofs \
            [--dep Lax251941Proofs ...] Common/Basic PartA/MealyBasic ...

For each listed module `X/Y` (relative to RequestProject/, no extension) the
file is copied to `<dest>/<pkg>/Source/X/Y.lean` with these rewrites:

  import RequestProject.X.Y     -> import <pkg>.Source.X.Y   if X/Y is ported here
                                -> import <dep>.Source.X.Y   if some --dep package
                                   ports it (recorded in <dep-dest>/ported.txt)
  namespace Transducers          -> namespace <pkg>.Transducers   (root namespaces only)
  end Transducers                -> end <pkg>.Transducers
  open Transducers               -> open <pkg>.Transducers
  (likewise for the other root namespaces PCP, PCPIndex, Acceptance)

Inside `namespace <pkg>.Transducers`, a fully qualified `Transducers.foo` still
resolves (Lean tries every prefix of the current namespace), and so does a
reference to a dependency's `Transducers.foo` once `open <dep>` is in force;
the script inserts `open <dep>` after the imports of every ported file when
--dep packages are given.

The list of ported modules is written to <dest>/ported.txt so that later
packages can resolve their imports against it.
"""
import argparse, os, re, sys

SRC = os.path.expanduser("~/git/transducer-book/transducer-lean/RequestProject")
ROOT_NS = ["Transducers", "PCP", "PCPIndex", "Acceptance"]

ap = argparse.ArgumentParser()
ap.add_argument("--pkg", required=True)
ap.add_argument("--dest", required=True)
ap.add_argument("--dep", action="append", default=[], help="PKG=DEST of a dependency proof package")
ap.add_argument("--provided", action="append", default=[], help="module X/Y written by hand at <dest>/<pkg>/Source/X/Y.lean")
ap.add_argument("modules", nargs="+")
a = ap.parse_args()

deps = {}  # module -> package
for d in a.dep:
    pkg, dest = d.split("=")
    for line in open(os.path.join(dest, "ported.txt")):
        deps[line.strip()] = pkg

mine = set(a.modules) | set(a.provided)

def rewrite_import(m):
    mod = m.group(1)
    if mod in mine:
        return f"import {a.pkg}.Source.{mod.replace('/', '.')}"
    if mod in deps:
        return f"import {deps[mod]}.Source.{mod.replace('/', '.')}"
    sys.exit(f"unported import RequestProject.{mod.replace('/', '.')}")

for mod in a.modules:
    if mod in a.provided:
        continue
    src = os.path.join(SRC, mod + ".lean")
    s = open(src).read()
    s = re.sub(r"^import RequestProject\.([\w.]+)$",
               lambda m: rewrite_import(type("M", (), {"group": lambda self, i: m.group(1).replace('.', '/')})()),
               s, flags=re.M)
    for ns in ROOT_NS:
        s = re.sub(rf"^namespace {ns}\b", f"namespace {a.pkg}.{ns}", s, flags=re.M)
        s = re.sub(rf"^end {ns}\s*$", f"end {a.pkg}.{ns}", s, flags=re.M)
        s = re.sub(rf"^open {ns}\b", f"open {a.pkg}.{ns}", s, flags=re.M)
        s = re.sub(rf"^open scoped {ns}\b", f"open scoped {a.pkg}.{ns}", s, flags=re.M)
    depnames = sorted({p for p in deps.values()})
    if depnames:
        # insert `open <dep>` lines after the last import line
        lines = s.split("\n")
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines[last + 1:last + 1] = [f"open {p}" for p in depnames]
        s = "\n".join(lines)
    out = os.path.join(a.dest, a.pkg, "Source", mod + ".lean")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write(s)
    print("ported", mod, "->", out)

with open(os.path.join(a.dest, "ported.txt"), "w") as f:
    for mod in sorted(mine | set(deps)):
        f.write(mod + "\n")
