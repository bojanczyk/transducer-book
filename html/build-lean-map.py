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
SOURCES = ROOT / "data" / "lean_sources.json"

# hyperref names an anchor after the counter that produced it, and macros.sty's
# \newaliascnt keeps those names distinct even though the counters are shared,
# so the anchor prefix is what tells a Lemma from a Theorem.
KINDS = ["theorem", "lemma", "claim", "corollary", "definition",
         "fact", "proposition", "conjecture", "subclaim", "example", "exercise"]
NUMBER = re.compile(r"[A-D]?\.\d+\.\d+")

# Which results are deliberately not formalised is read from THEOREMS.md's own
# index (see read_theorems_md), not kept in a list here that would go stale.


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
    """label -> {kind, number, page, anchor}, from the PDF build.

    Keyed on the label, not on the number. The number is what the book prints,
    but it moves the moment a result is inserted earlier, and everything keyed
    on it then points at the wrong theorem with nothing to catch it. The label
    is chosen by the author and does not move; the number is recoverable from
    it here, and not the other way round.
    """
    if not AUX.exists():
        sys.exit(f"{AUX} not found — run latexmk on ../main.tex first")
    aux = AUX.read_text(errors="ignore")
    book = {}
    for m in re.finditer(r"\\newlabel\{([^}]+)\}\{", aux):
        label = m.group(1)
        # hyperref writes targets of its own alongside the authored labels
        if label.endswith("@cref") or label.startswith("autoref-"):
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
        book[label] = {"label": label, "number": number,
                       "page": page, "anchor": anchor, "kind": kind}
    return book


# --------------------------------------------------------------------------
# the formalisation: Lean sources
# --------------------------------------------------------------------------

# The name is matched with \w rather than [A-Za-z0-9_], because Lean names are
# not ASCII: `exists_isTwoNFT₁_not_isTwoNFT₂` was being indexed as
# `exists_isTwoNFT`, truncated at the subscript, so nothing that referred to it
# by its real name could be found in the sources at all.
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+"
                  r"([^\W\d][\w'.]*)", re.M)
DOC_KIND = "|".join(k.capitalize() for k in KINDS)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", " ", text)


def blank_comments(text):
    """Comments replaced by spaces, character for character.

    Length and line breaks are preserved, so positions still line up with the
    original, and nesting is respected. Stripping per declaration instead would
    let a `/- … -/` block that spans a declaration boundary leak its contents
    into the next one — which is how the superseded statements kept beside
    Theorem B.4.2, `sorry` and all, made a finished proof look unproved.
    """
    out, i, n = list(text), 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                j = n
        else:
            i += 1
            continue
        for k in range(i, j):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


def doc_comments(text):
    """Every `/-- … -/` that is live code, as (start, end, body).

    Lean's block comments nest, and a result that has been withdrawn is left in
    the sources commented out — `/- … /-- **Theorem C.4.17.** … -/ … -/`. A
    non-nesting regex reads that as a docstring and reports a statement that is
    no longer there, so ordinary comments are skipped whole instead.
    """
    out, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("/--", i) or text.startswith("/-", i):
            doc = text.startswith("/--", i)
            depth, j = 1, i + (3 if doc else 2)
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            if doc:
                out.append((i, j, text[i + 3:max(i + 3, j - 2)]))
            i = j
        else:
            i += 1
    return out


def span_of(name, decl_line, starts, lines, rel, doc_before):
    """Where a declaration begins and ends, comment included."""
    after = [x for x in starts if x > decl_line]
    end = (after[0] - 1) if after else len(lines)
    while end > decl_line and not lines[end - 1].strip():
        end -= 1
    return {"file": rel, "line": doc_before.get(decl_line, decl_line),
            "decl_line": decl_line, "end": end}


LABELS = LEAN / "RequestProject" / "Labels.lean"


def read_labels():
    """label -> [(declaration, proved_claim)], from the project's own registry.

    `Labels.lean` declares, for every formalised result, an alias whose Lean
    name *is* the book's label, and follows it with `assert_no_sorry` or
    `assert_uses_sorry`. Both are elaborators, so the correspondence and the
    status are checked by the compiler on every build — which makes this a far
    better source than reading docstrings, where nothing checks that the name in
    the prose is the name below it. Several declarations for one result are
    written `label#2`, `label#3`.
    """
    if not LABELS.exists():
        return {}
    out, text = {}, LABELS.read_text(errors="ignore")
    # The file also accounts for the results it does *not* alias, one per line
    # with the reason. A conjecture is not a gap in the formalisation, and nor
    # is a step the book only uses inside a proof; taking the list from here
    # beats inferring it from prose elsewhere.
    excused = {}
    for m in re.finditer(r"^\* `([^`]+)` \((\w+)\) -- ([^;]+)", text, re.M):
        excused[m.group(1)] = m.group(3).strip()
    out["__excused__"] = excused
    for m in re.finditer(r"^alias «([^»]+)» := ([A-Za-z_][\w'.]*)", text, re.M):
        tag, decl = m.group(1), m.group(2)
        label = tag.split("#")[0]
        after = text[m.end():m.end() + 200]
        claim = ("proved" if "assert_no_sorry" in after.split("alias")[0]
                 else "open" if "assert_uses_sorry" in after.split("alias")[0]
                 else None)
        out.setdefault(label, []).append((decl, claim))
    return out


def read_lean():
    """(kind, number) -> [{name, file, line, end}], from docstrings, and all bodies.

    `line` is the first line of the docstring and `end` the last line before the
    next top-level declaration, so the pair delimits the whole result — comment
    and proof together — for the web edition to highlight.
    """
    hits, bodies, sources, locations = {}, {}, {}, {}
    for f in sorted(LEAN_SRC.rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        txt = f.read_text(errors="ignore")
        rel = str(f.relative_to(LEAN))
        sources[rel] = txt
        lines = txt.splitlines()
        code = blank_comments(txt).splitlines()   # same lines, comments blanked
        # Where one result ends and the next begins, by 1-based line. A
        # declaration is not the boundary: the next result's docstring comes
        # first, and belongs to it, not to the one before.
        starts = [i + 1 for i, line in enumerate(lines)
                  if (DECL.match(code[i]) and not code[i].startswith(" "))
                  or line.startswith("/--") or line.startswith("/-!")]
        # where each declaration's own docstring begins, so a result shown in the
        # web edition starts at its comment rather than at its first token
        doc_before = {}
        for dstart, dend, _ in doc_comments(txt):
            d = DECL.search(txt[dend:dend + 400])
            if d:
                doc_before[txt[:dend + d.start(1)].count("\n") + 1] = \
                    txt[:dstart].count("\n") + 1
        # declaration bodies, for the sorry check below, and where each one is
        name, buf, at = None, [], 0
        for no, line in enumerate(code, 1):
            m = DECL.match(line)
            if m and not line.startswith(" "):
                if name:
                    bodies.setdefault(name, "\n".join(buf))
                    locations.setdefault(name, span_of(name, at, starts, lines, rel, doc_before))
                name, buf, at = m.group(1), [line], no
            elif name:
                buf.append(line)
        if name:
            bodies.setdefault(name, "\n".join(buf))
            locations.setdefault(name, span_of(name, at, starts, lines, rel, doc_before))
        # docstrings carrying a book number, and the declaration they precede
        for start, end, doc in doc_comments(txt):
            hit = re.search(rf"\*\*({DOC_KIND})\s+`([a-z]+:[a-z0-9-]+)`", doc)
            if not hit:
                continue
            d = DECL.search(txt[end:end + 400])
            if not d:
                continue
            doc_line = txt[:start].count("\n") + 1
            # from the name, not from the match: DECL opens with `^\s*`, which
            # happily matches the newline after `-/` and would put the
            # declaration a line early — and so end the result before it began
            decl_line = txt[:end + d.start(1)].count("\n") + 1
            after = [s for s in starts if s > decl_line]
            end = (after[0] - 1) if after else len(lines)
            while end > decl_line and not lines[end - 1].strip():
                end -= 1                      # don't trail off into blank lines
            key = hit.group(2)          # the label; kind comes from the book
            entry = {"name": d.group(1), "file": rel, "line": doc_line,
                     "decl_line": decl_line, "end": end}
            if entry not in hits.setdefault(key, []):
                hits[key].append(entry)
    return hits, bodies, sources, locations


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

# What a Lean declaration name can look like: letters, digits, underscores,
# primes, dotted namespaces. Notably *not* a colon — which is what tells a Lean
# name from one of the book's own labels. Rows here often mention a label in
# passing ("the Lean proof of Theorem `thm:pebble-are-for` replaces it"), and
# reading that as a declaration is how Lemma D.2.2 came to claim it was
# formalised by something it merely refers to.
LEAN_NAME = re.compile(r"^[^\W\d][\w'!?]*(\.[\w'!?]+)*$")


def lean_names_in(cell):
    """Backticked declaration names in a cell — file paths and labels are not."""
    return [n for n in re.findall(r"`([^`]+)`", cell)
            if not n.endswith(".lean") and "/" not in n and LEAN_NAME.match(n)]


def number_key(num):
    """Sortable form of a book number, so a range can be expanded."""
    part = num[0] if num[:1].isalpha() else ""
    return (part, [int(x) for x in num.lstrip("ABCD").split(".") if x])


KIND_WORD = "|".join(k.capitalize() for k in KINDS) + "|Corollaries"
CELL_TOKEN = re.compile(
    rf"\**({KIND_WORD})s?\**"                                   # a kind, perhaps plural
    rf"|({NUMBER.pattern})\s*[–—-]\s*({NUMBER.pattern})"         # or a range
    rf"|({NUMBER.pattern})")                                     # or one number


def parse_results_cell(cell, book):
    """The labels a row is about.

    A row names one result, a comma-separated list of them, or a range written
    `` `first` to `last` ``. A range is expanded through the book's own ordering
    — the numbers in `main.aux` — so nothing is invented and the endpoints stay
    the author's.
    """
    labels = re.findall(r"`([a-z]+:[a-z0-9-]+)`", cell)
    labels = [l for l in labels if l in book]
    if re.search(r"`\s+to\s+`", cell) and len(labels) == 2:
        lo, hi = (number_key(book[l]["number"]) for l in labels)
        kind = book[labels[0]]["kind"]
        span = [l for l, b in book.items()
                if b["kind"] == kind and lo <= number_key(b["number"]) <= hi]
        return sorted(span, key=lambda l: number_key(book[l]["number"]))
    return labels


def read_theorems_md(book):
    """label -> {names, status, internal, not_formalised}.

    Most rows are about a single result. Some cover several at once, and those
    are the ones that record what happened to the book's internal steps — the
    claims inside the proof of Theorem B.4.8, say, which are not numbered
    results in Lean but do have proofs there under names of their own. Read
    literally, such a row links n results to n declarations, in order.
    """
    if not THEOREMS.exists():
        return {}
    out = {}
    for line in THEOREMS.read_text(errors="ignore").splitlines():
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip("|").split("|")]
        if len(cells) < 2:
            continue
        results = parse_results_cell(cells[0], book)
        if not results:
            continue
        names = lean_names_in(cells[1])
        absent = "not formalised" in cells[1].lower()
        # "Mathlib's `Semiring`" — the one thing that licenses calling a name we
        # cannot find in this project *formalised elsewhere* rather than missing.
        mathlib = "mathlib" in line.lower()
        if len(results) > 1:
            # pair them up only when the row names exactly one declaration per
            # result; anything else is prose, not a mapping
            paired = len(names) == len(results)
            for i, key in enumerate(results):
                out[key] = {"names": [names[i]] if paired else [],
                            "status": re.sub(r"\s+", " ", cells[1])[:160],
                            "internal": paired and absent,
                            "mathlib": mathlib,
                            "not_formalised": absent and not paired}
            continue
        if not names:
            continue
        status = cells[2] if len(cells) > 2 else ""
        out[results[0]] = {
            "names": names, "status": re.sub(r"\s+", " ", status).strip(" —-"),
            "internal": False, "mathlib": mathlib, "not_formalised": absent}
    return out


# --------------------------------------------------------------------------

def build():
    book = read_book()
    lean, bodies, sources, locations = read_lean()
    witness = sorry_witnesses(bodies)
    md = read_theorems_md(book)
    registry = read_labels()

    entries, by_decl = {}, {}
    for key, b in sorted(book.items(), key=lambda kv: number_key(kv[1]["number"])):
        kind, number = b["kind"], b["number"]
        decls = []
        # The registry first: `Labels.lean` is the one correspondence the
        # compiler checks, so prefer it to the docstrings, which nothing checks.
        for name, claim in registry.get(key, []):
            st, w = state_of(name, bodies, witness)
            loc = locations.get(name) or locations.get(name.split(".")[-1]) or \
                  next((v for k2, v in locations.items()
                        if k2.split(".")[-1] == name.split(".")[-1]), None)
            d = {"name": name, "state": st, **(loc or {"file": None, "line": None}),
                 **({"rests_on": w} if w else {})}
            # the registry asserts a status at compile time; if our own reading of
            # the sources disagrees, say so rather than quietly pick one
            if claim == "proved" and st in ("open", "blocked"):
                d["disagrees"] = f"Labels.lean asserts no sorry, sources say {st}"
            elif claim == "open" and st == "proved":
                d["disagrees"] = "Labels.lean asserts a sorry, sources say proved"
            decls.append(d)
        seen_reg = {d["name"].split(".")[-1] for d in decls}
        for d in lean.get(key, []):
            if d["name"].split(".")[-1] in seen_reg:
                continue
            st, w = state_of(d["name"], bodies, witness)
            decls.append({**d, "state": st, **({"rests_on": w} if w else {})})
        # names THEOREMS.md lists that no docstring pointed at
        seen = {d["name"].split(".")[-1] for d in decls}
        for n in md.get(key, {}).get("names", []):
            if n.split(".")[-1] in seen:
                continue
            st, w = state_of(n, bodies, witness)
            loc = locations.get(n) or locations.get(n.split(".")[-1]) or \
                  next((v for k2, v in locations.items()
                        if k2.split(".")[-1] == n.split(".")[-1]), None)
            decls.append({"name": n, "state": st,
                          **(loc or {"file": None, "line": None}),
                          **({"rests_on": w} if w else {}), "from": "THEOREMS.md",
                          **({"internal": True} if md[key].get("internal") else {})})
        # A name this project does not define is one of two quite different
        # things, and the difference is not ours to guess: either the result is
        # formalised elsewhere — Definition B.3.1 is Mathlib's `Semiring`, and
        # THEOREMS.md says as much — or the name no longer resolves, which is
        # drift to report rather than a fact to print under the result. Printing
        # "provided by Mathlib" for the latter states something false about the
        # formalisation; printing the bare word "missing" for the former says
        # nothing useful about a result that is, in fact, formalised.
        mathlib = md.get(key, {}).get("mathlib", False)
        unresolved = [d["name"] for d in decls if d["state"] == "missing" and not mathlib]
        for d in decls:
            if d["state"] == "missing" and mathlib:
                d["state"] = "external"
        decls = [d for d in decls if d["state"] != "missing"]

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
        if unresolved:
            e["unresolved"] = unresolved
        if key in md:
            e["theorems_md_status"] = md[key]["status"]
        excuse = registry.get("__excused__", {}).get(key)
        if excuse or md.get(key, {}).get("not_formalised") or kind == "exercise":
            e["not_formalised"] = True
            if excuse:
                e["not_formalised_because"] = excuse
        entries[key] = e          # key *is* the label
        for d in decls:
            by_decl.setdefault(d["name"], {"label": b["label"], "kind": kind,
                                           "number": number})

    # Only the files some result actually points into: the web edition inlines
    # them per page (it must work opened over file://, where fetching a sibling
    # file is blocked), so shipping the whole 2 MB corpus would be waste.
    used = {d["file"] for e in entries.values() for d in e["lean"] if d.get("file")}
    return book, lean, md, entries, by_decl, {f: sources[f] for f in sorted(used)}


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

    stale = [(k, e) for k, e in entries.items() if e.get("unresolved")]
    if stale:
        print(f"\nnamed in THEOREMS.md or Labels.lean but not found in the sources "
              f"({len(stale)}) — renamed upstream, or never there:")
        for lab, e in sorted(stale, key=lambda r: number_key(r[1]["number"])):
            print(f"   {e['kind']:11s} {e['number']:8s}  {', '.join(e['unresolved'])}")
        problems += len(stale)

    booknums = set(book)
    orphan_doc = sorted(set(lean) - booknums)
    if orphan_doc:
        print(f"\ncited by a Lean docstring but not a \\label of the book "
              f"({len(orphan_doc)}):")
        for k in orphan_doc:
            print(f"   {k:44s} -> {lean[k][0]['name']}")
        problems += len(orphan_doc)

    orphan_md = sorted(set(md) - booknums - set(lean))
    if orphan_md:
        print(f"\nin THEOREMS.md but not a \\label of the book ({len(orphan_md)}):")
        for k in orphan_md:
            print(f"   {k:44s} -> {md[k]['names'][0]}")
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
        for lab, a, b in disagree:
            print(f"   {lab:44s} docstring={a}  THEOREMS.md={b}")
        problems += len(disagree)

    return problems


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--write", action="store_true",
                    help="write data/lean_map.json as well as reporting")
    args = ap.parse_args()

    book, lean, md, entries, by_decl, sources = build()
    problems = report(book, lean, md, entries)

    if args.write:
        OUT.parent.mkdir(parents=True, exist_ok=True)
        OUT.write_text(json.dumps(
            {"entries": entries, "by_declaration": by_decl}, indent=1,
            ensure_ascii=False, sort_keys=True) + "\n")
        print(f"\nwrote {OUT.relative_to(BODY)} "
              f"({len(entries)} labels, {len(by_decl)} declarations)")
        SOURCES.write_text(json.dumps(sources, ensure_ascii=False,
                                      sort_keys=True) + "\n")
        kb = sum(len(v) for v in sources.values()) / 1024
        print(f"wrote {SOURCES.relative_to(BODY)} "
              f"({len(sources)} Lean files, {kb:.0f} KB)")

    if problems:
        print(f"\n{problems} thing(s) to look at — see above.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
