#!/usr/bin/env python3
"""Join the book's numbered results to their Lean counterparts.

The web edition can link each theorem to its formalisation and back, but no
single file records that correspondence. Three do, partially, and none of them
was written for this purpose:

  ../main.aux                     every \\label that resolved, with the number
                                  it resolved to and hyperref's anchor — so it
                                  knows *where in the book* a result lives.
  ../transducer-lean/…/*.lean     docstrings that open `**Theorem C.4.1.**`,
                                  attached to the declaration that follows —
                                  so they know *which declaration* a result is.
  ../transducer-lean/THEOREMS.md  index tables `| Theorem C.4.1 | `name` | … |`
                                  — the formalisation's own summary.

The join key is the pair (kind, number): the number alone is ambiguous, since
theorem-likes and exercises count separately and both produce a `.0.1`.

The two Lean-side sources are deliberately both consulted. Docstrings are
primary — they sit next to the declaration, so a rename cannot separate them —
and THEOREMS.md is the cross-check. Where they disagree the report says so
rather than silently preferring one.

Nothing here writes into ../transducer-lean/. That directory is a mirror of
Aristotle's server: the formalisation driver rsyncs it with --delete on every
harvest, so a file added there would not survive the next one. The map is
generated *from* it, into this repo, on every build — which is also why a
declaration being renamed upstream costs nothing: the stable key is the book
number, and the Lean names are re-read each time.

    python3 build-lean-map.py            # report; exit 1 if anything drifted
    python3 build-lean-map.py --write    # …and write data/lean_map.json

rebuild.sh passes --write, so the map follows the sources by itself; running it
bare is the read-only check.
"""

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent   # html/
BODY = ROOT.parent                       # the book repo root
AUX = BODY / "main.aux"
LEAN = BODY / "transducer-lean"
LEAN_SRC = LEAN / "RequestProject"
THEOREMS = LEAN / "THEOREMS.md"
OUT = ROOT / "data" / "lean_map.json"

# hyperref names an anchor after the counter that produced it, and macros.sty's
# \newaliascnt keeps those names distinct even though the counters are shared,
# so the anchor prefix is what tells a Lemma from a Theorem.
KINDS = ["theorem", "lemma", "claim", "corollary", "definition",
         "fact", "proposition", "example", "exercise"]
NUMBER = re.compile(r"[A-D]?\.\d+\.\d+")

# Results the book states but deliberately does not formalise as numbered
# statements: internal steps of a larger proof, which the formalisation is free
# to organise its own way. Recorded here so the report can tell "not formalised
# on purpose" apart from "we lost track of it". Exercises are excluded wholesale
# by the same policy, so they are handled by kind rather than listed.
NOT_FORMALISED = {
    ("lemma", "C.2.3"), ("lemma", "C.2.4"), ("lemma", "C.2.12"),
    ("claim", "B.4.9"), ("claim", "B.4.10"), ("claim", "B.4.11"),
    ("claim", "B.4.12"),
    ("lemma", "D.2.2"), ("lemma", "D.2.5"),
    ("claim", "D.2.3"), ("claim", "D.2.6"), ("claim", "D.2.7"),
}


# --------------------------------------------------------------------------
# the book: main.aux
# --------------------------------------------------------------------------

def brace_groups(s, i):
    """Read consecutive {...} groups starting at i, respecting nesting."""
    out = []
    while i < len(s) and s[i] == "{":
        depth, j = 0, i
        while j < len(s):
            if s[j] == "{":
                depth += 1
            elif s[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        out.append(s[i + 1:j])
        i = j + 1
    return out


def read_book():
    """(kind, number) -> {label, number, page, anchor}, from the PDF build."""
    if not AUX.exists():
        sys.exit(f"{AUX} not found — run latexmk on ../main.tex first")
    aux = AUX.read_text(errors="ignore")
    book = {}
    for m in re.finditer(r"\\newlabel\{([^}]+)\}\{", aux):
        label = m.group(1)
        if label.endswith("@cref"):
            continue
        outer = brace_groups(aux, m.end() - 1)
        if not outer:
            continue
        f = brace_groups(outer[0], 0)
        if len(f) < 4:
            continue
        number, page, anchor = f[0], f[1], f[3]
        if not NUMBER.fullmatch(number):
            continue
        kind = anchor.split(".")[0].lower()
        if kind not in KINDS:
            continue
        book[(kind, number)] = {"label": label, "number": number,
                                "page": page, "anchor": anchor, "kind": kind}
    return book


# --------------------------------------------------------------------------
# the formalisation: Lean sources
# --------------------------------------------------------------------------

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+"
                  r"([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
DOC_KIND = "|".join(k.capitalize() for k in KINDS)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def read_lean():
    """(kind, number) -> [{name, file, line}], from docstrings, and all bodies."""
    hits, bodies = {}, {}
    for f in sorted(LEAN_SRC.rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        txt = f.read_text(errors="ignore")
        rel = str(f.relative_to(LEAN))
        # declaration bodies, for the sorry check below
        name, buf = None, []
        for line in txt.splitlines():
            m = DECL.match(line)
            if m and not line.startswith(" "):
                if name:
                    bodies.setdefault(name, "\n".join(buf))
                name, buf = m.group(1), [line]
            elif name:
                buf.append(line)
        if name:
            bodies.setdefault(name, "\n".join(buf))
        # docstrings carrying a book number, and the declaration they precede
        for m in re.finditer(r"/--(.*?)-/", txt, re.S):
            hit = re.search(rf"\*\*({DOC_KIND})\s+({NUMBER.pattern})", m.group(1))
            if not hit:
                continue
            d = DECL.search(txt[m.end():m.end() + 400])
            if not d:
                continue
            key = (hit.group(1).lower(), hit.group(2))
            entry = {"name": d.group(1), "file": rel,
                     "line": txt[:m.start()].count("\n") + 1}
            if entry not in hits.setdefault(key, []):
                hits[key].append(entry)
    return hits, {k: strip_comments(v) for k, v in bodies.items()}


def sorry_witnesses(bodies):
    """declaration -> the `sorry` it rests on, following the sources.

    A source-level approximation of `#print axioms`, so that the map can say
    whether a result is actually proved and not merely stated. It errs towards
    over-reporting, which is the safe direction. The authoritative version, used
    by the formalisation driver to decide when a task is finished, is
    `open_results` in ../formalize-agent/driver.py.
    """
    index = {}
    for name in bodies:
        index.setdefault(name, name)
        index.setdefault(name.split(".")[-1], name)
    rev = {}
    for name, body in bodies.items():
        for tok in re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", body):
            dep = index.get(tok) or index.get(tok.split(".")[-1])
            if dep is not None and dep != name:
                rev.setdefault(dep, set()).add(name)
    witness, pending = {}, []
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
    return witness


def state_of(name, bodies, witness):
    """proved / open / blocked / missing, for one declaration."""
    key = name.split(".")[-1]
    if key not in bodies:
        key = next((k for k in bodies if k.split(".")[-1] == name.split(".")[-1]), None)
        if key is None:
            return "missing", None
    w = witness.get(key)
    if w is None:
        return "proved", None
    return ("open", None) if w == key else ("blocked", w)


# --------------------------------------------------------------------------
# the formalisation's own summary: THEOREMS.md
# --------------------------------------------------------------------------

def read_theorems_md():
    """(kind, number) -> {names, status}, from the index tables."""
    if not THEOREMS.exists():
        return {}
    out = {}
    for line in THEOREMS.read_text(errors="ignore").splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 2:
            continue
        hit = re.match(rf"\**({DOC_KIND})\**\s+({NUMBER.pattern})", cells[0])
        if not hit:
            continue
        names = re.findall(r"`([^`]+)`", cells[1])
        if not names:
            continue
        status = cells[2] if len(cells) > 2 else ""
        out[(hit.group(1).lower(), hit.group(2))] = {
            "names": names, "status": re.sub(r"\s+", " ", status).strip(" —-")}
    return out


# --------------------------------------------------------------------------

def build():
    book = read_book()
    lean, bodies = read_lean()
    witness = sorry_witnesses(bodies)
    md = read_theorems_md()

    entries, by_decl = {}, {}
    for key, b in sorted(book.items()):
        kind, number = key
        decls = []
        for d in lean.get(key, []):
            st, w = state_of(d["name"], bodies, witness)
            decls.append({**d, "state": st, **({"rests_on": w} if w else {})})
        # names THEOREMS.md lists that no docstring pointed at
        seen = {d["name"].split(".")[-1] for d in decls}
        for n in md.get(key, {}).get("names", []):
            if n.split(".")[-1] in seen:
                continue
            st, w = state_of(n, bodies, witness)
            if st == "missing":
                # not in this project: THEOREMS.md is pointing at Mathlib
                st, w = "external", None
            decls.append({"name": n, "file": None, "line": None, "state": st,
                          **({"rests_on": w} if w else {}), "from": "THEOREMS.md"})
        # A result often has several declarations carrying its number: the
        # statement itself plus the two directions of an iff, say. THEOREMS.md
        # names the one it considers canonical, so prefer that; failing that,
        # the first docstring wins. The primary is marked and sorted first, so
        # a page can link one declaration and treat the rest as supporting.
        if decls:
            want = [n.split(".")[-1] for n in md.get(key, {}).get("names", [])]
            order = {n: i for i, n in enumerate(want)}
            decls.sort(key=lambda d: order.get(d["name"].split(".")[-1], len(order)))
            decls[0]["primary"] = True
        e = {"kind": kind, "number": number, "label": b["label"],
             "page": b["page"], "anchor": b["anchor"], "lean": decls}
        if key in md:
            e["theorems_md_status"] = md[key]["status"]
        if key in NOT_FORMALISED or kind == "exercise":
            e["not_formalised"] = True
        entries[b["label"]] = e
        for d in decls:
            by_decl.setdefault(d["name"], {"label": b["label"], "kind": kind,
                                           "number": number})

    return book, lean, md, entries, by_decl


def report(book, lean, md, entries):
    linked = [e for e in entries.values() if e["lean"]]
    print(f"book results with a \\label and a number : {len(book)}")
    print(f"  linked to at least one Lean declaration: {len(linked)}")
    print(f"Lean docstrings carrying a book number    : {len(lean)}")
    print(f"THEOREMS.md index rows                    : {len(md)}")

    proved = sum(1 for e in linked
                 if any(d["state"] == "proved" for d in e["lean"]))
    blocked = [e for e in linked
               if e["lean"] and all(d["state"] != "proved" for d in e["lean"])]
    print(f"  of those, fully proved                  : {proved}")
    print(f"  stated but resting on a `sorry`         : {len(blocked)}")

    problems = 0

    unlinked = [(k, e) for k, e in entries.items()
                if not e["lean"] and not e.get("not_formalised")]
    if unlinked:
        print(f"\nin the book, no Lean counterpart found ({len(unlinked)}):")
        for lab, e in sorted(unlinked, key=lambda r: r[1]["number"]):
            print(f"   {e['kind']:11s} {e['number']:8s}  {lab}")
        problems += len(unlinked)

    booknums = set(book)
    orphan_doc = sorted(set(lean) - booknums)
    if orphan_doc:
        print(f"\nnumbered in a Lean docstring but no \\label in the book "
              f"({len(orphan_doc)}):")
        for k in orphan_doc:
            print(f"   {k[0]:11s} {k[1]:8s}  -> {lean[k][0]['name']}")
        problems += len(orphan_doc)

    orphan_md = sorted(set(md) - booknums - set(lean))
    if orphan_md:
        print(f"\nin THEOREMS.md but no \\label in the book ({len(orphan_md)}):")
        for k in orphan_md:
            print(f"   {k[0]:11s} {k[1]:8s}  -> {md[k]['names'][0]}")
        problems += len(orphan_md)

    disagree = []
    for key in sorted(set(lean) & set(md)):
        a = {n["name"].split(".")[-1] for n in lean[key]}
        b = {n.split(".")[-1] for n in md[key]["names"]}
        if not (a & b):
            disagree.append((key, sorted(a), sorted(b)))
    if disagree:
        print(f"\ndocstring and THEOREMS.md name different declarations "
              f"({len(disagree)}):")
        for (kind, num), a, b in disagree:
            print(f"   {kind:11s} {num:8s}  docstring={a}  THEOREMS.md={b}")
        problems += len(disagree)

    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--write", action="store_true",
                    help="write data/lean_map.json as well as reporting")
    args = ap.parse_args()

    book, lean, md, entries, by_decl = build()
    problems = report(book, lean, md, entries)

    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(
            {"entries": entries, "by_declaration": by_decl}, indent=1,
            ensure_ascii=False, sort_keys=True) + "\n")
        print(f"\nwrote {OUT.relative_to(BODY)} "
              f"({len(entries)} labels, {len(by_decl)} declarations)")

    if problems:
        print(f"\n{problems} thing(s) to look at — see above.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
