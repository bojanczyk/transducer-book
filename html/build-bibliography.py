#!/usr/bin/env python3
"""Turn the book's bibliography into something the page can show.

A citation in the text is a link now (see latex-preambles/book.tex's
`bibhyperref` hook), and clicking one opens the reference in the third column.
That column needs the entry itself — author, title, where it appeared, a DOI to
follow — which exists in two places, neither of them reachable from the browser:

  ../bib.bib     the entries as written, with all their fields.
  ../main.bbl    biber's output for the book: which entries are actually cited,
                 and the label the printed text shows for each ("MSV03").

So both are read here and written out as one small script. A script rather than
JSON for the same reason as the search index: the built site has to work opened
straight off disk, where fetching a sibling file is refused but a <script src>
is not.

An entry whose paper is in literature/pdfs is also given the path to that file,
so the column can show the paper itself and not only a DOI to follow. Which scan
belongs to which entry is written down nowhere, so it is worked out from the
file's name — see match_pdfs — and a scan left belonging to nothing is reported,
since a file no citation reaches is a file nobody will ever open.

An entry that the book cites but bib.bib does not define is reported rather than
skipped quietly — the printed text shows the raw key in that case, and so does
the PDF, which is a fault in the book worth knowing about.

    python3 build-bibliography.py           # report; exit 1 if the file is stale
    python3 build-bibliography.py --write   # …and write static/bibliography.js

rebuild.sh passes --write.
"""

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

ROOT = Path(__file__).resolve().parent      # html/
BODY = ROOT.parent                          # the book repo root
BIB = BODY / "bib.bib"
BBL = BODY / "main.bbl"
AUX = BODY / "main.aux"
PDFS = BODY / "literature" / "pdfs"
OUT = ROOT / "static" / "bibliography.js"

# Where those PDFs answer from once the site is built: hugo.toml mounts the
# folder there rather than copying it, so this is the one place the two names
# have to agree.
PDF_HREF = "pdfs/"

# Where an entry appeared, in the order we would rather name it.
VENUE = ["journal", "booktitle", "publisher", "school", "institution", "series",
         "howpublished", "note"]

ACCENT = {"'": "\u0301", "`": "\u0300", '"': "\u0308", "^": "\u0302",
          "~": "\u0303", "v": "\u030c", "c": "\u0327", ".": "\u0307",
          "=": "\u0304", "u": "\u0306", "H": "\u030b", "r": "\u030a"}
LETTER = {"l": "ł", "L": "Ł", "o": "ø", "O": "Ø", "ss": "ß", "ae": "æ",
          "AE": "Æ", "aa": "å", "AA": "Å", "i": "ı", "j": "ȷ"}


def detex(s):
    """A bibliography field as a person would read it."""
    if not s:
        return ""
    # {\'e} and \'{e} and \'e — an accent command, then the letter it sits on
    def accent(m):
        mark, letter = m.group(1), m.group(2)
        return unicodedata.normalize("NFC", letter + ACCENT[mark])
    pattern = "|".join(re.escape(k) for k in ACCENT)
    s = re.sub(r"\\(" + pattern + r")\s*\{?([A-Za-z])\}?", accent, s)
    # \l, \ss, … — a letter that is a command of its own
    s = re.sub(r"\\([a-zA-Z]+)\s*\{\}|\\([a-zA-Z]+)(?![a-zA-Z])",
               lambda m: LETTER.get(m.group(1) or m.group(2), " "), s)
    s = s.replace("--", "\u2013").replace("~", " ")
    s = re.sub(r"[{}]", "", s)
    return re.sub(r"\s+", " ", s).strip()


def names(field):
    """"Milo, Tova and Suciu, Dan" -> "Tova Milo, Dan Suciu"."""
    out = []
    for who in re.split(r"\s+and\s+", field):
        who = who.strip()
        if not who:
            continue
        if "," in who:
            family, given = who.split(",", 1)
            who = f"{given.strip()} {family.strip()}".strip()
        out.append(detex(who))
    return ", ".join(out)


# Words that carry no weight when telling one title from another, in the three
# languages the bibliography is written in.
STOP = {"a", "an", "the", "of", "on", "in", "and", "for", "to", "with", "by",
        "its", "their", "some", "de", "des", "du", "la", "le", "les", "et",
        "un", "une", "sur", "entre", "der", "die", "das", "und", "von"}


def fold(s):
    """Bojańczyk, Bojanczyk and BOJAŃCZYK are one word here."""
    return "".join(c for c in unicodedata.normalize("NFD", s).lower()
                   if c.isascii() and c.isalnum())


def surnames(field):
    """The family names of an entry's authors, folded, in the order written."""
    out = []
    for who in re.split(r"\s+and\s+", field):
        who = detex(who).strip()
        if not who:
            continue
        family = who.split(",")[0] if "," in who else who.split()[-1]
        if fold(family):
            out.append(fold(family))
    return out


def words(s):
    """A title as a bag of words worth comparing."""
    return {w for w in (fold(t) for t in re.split(r"[\W_]+", s)) if w and w not in STOP}


def read_pdfs():
    """literature/pdfs, read as what each file name claims about its paper.

    The names there were written to one pattern — surnames run together, the
    year, then the title: BojanczykKieferLhote2019_String-to-String_… — so the
    name says who wrote the paper, when, and what it was called, which between
    them identify it. A file that does not follow the pattern keeps only its
    words, and will match nothing; it is reported instead.
    """
    out = []
    for f in sorted(PDFS.glob("*.pdf")):
        head, _, tail = f.stem.partition("_")
        m = re.fullmatch(r"([A-Za-z]+)((?:1[89]|20)\d\d)", head)
        out.append({"name": f.name, "bytes": f.stat().st_size,
                    "who": fold(m.group(1)) if m else "",
                    "year": m.group(2) if m else "",
                    "words": words(tail if m else f.stem)})
    return out


def score(who, year, title, pdf):
    """How strongly one file name claims to be one entry's paper; 0 = not it.

    The surnames must line up exactly, and from the first author on: the blob
    has to be some number of the entry's authors run together, so Engelfriet's
    own 2015 paper is not offered EngelfrietHoogeboom2001 and vice versa. Only
    then do the year and the title break ties — which they must, because one
    author writing twice in one year (Bojańczyk in 2022) is not rare, and two
    files can name the same paper (GinsburgRose1966, with and without a title).
    """
    run, depth = "", 0
    for i, name in enumerate(who):
        run += name
        if run == pdf["who"]:
            depth = i + 1
            break
        if not pdf["who"].startswith(run):
            break
    if not depth:
        return 0
    s = 100 + 10 * depth                       # naming more authors is a surer aim
    if year and year == pdf["year"]:
        s += 50
    if title and pdf["words"]:
        s += 20 * len(title & pdf["words"]) / len(pdf["words"])
    return s


def match_pdfs(out, bib):
    """Give every entry the file that is its paper. Returns the files left over.

    Best claim first and each side used once, rather than best-per-entry: the
    two are different whenever an entry's best file is some other entry's only
    one, which is exactly the Eilenberg volumes (there is a scan of A and none
    of B, and B would otherwise take it).
    """
    pdfs = read_pdfs()
    claims = []
    for key, entry in out.items():
        fields = bib.get(key)
        if fields is None:
            continue
        who = surnames(fields.get("author") or fields.get("editor", ""))
        title, year = words(entry.get("title", "")), entry.get("year", "")
        for pdf in pdfs:
            s = score(who, year, title, pdf)
            if s:
                claims.append((-s, key, pdf["name"], pdf))
    claims.sort()
    took_key, took_pdf = set(), set()
    for _, key, name, pdf in claims:
        if key in took_key or name in took_pdf:
            continue
        took_key.add(key)
        took_pdf.add(name)
        out[key]["pdf"] = PDF_HREF + name
        out[key]["pdfbytes"] = pdf["bytes"]
    return [p["name"] for p in pdfs if p["name"] not in took_pdf]


def read_bib():
    """key -> {field: value}, straight from bib.bib."""
    if not BIB.exists():
        return {}
    text = BIB.read_text(errors="ignore")
    entries = {}
    for m in re.finditer(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", text):
        kind, key = m.group(1).lower(), m.group(2)
        # the entry runs to its matching closing brace
        depth, i = 1, m.end()
        while i < len(text) and depth:
            if text[i] == "{":
                depth += 1
            elif text[i] == "}":
                depth -= 1
            i += 1
        body, fields = text[m.end():i - 1], {"type": kind}
        for f in re.finditer(r"(\w+)\s*=\s*", body):
            j = f.end()
            if j < len(body) and body[j] in "{\"":
                close = "}" if body[j] == "{" else '"'
                d, k = 1, j + 1
                while k < len(body) and d:
                    if body[k] == "{" and close == "}":
                        d += 1
                    elif body[k] == close:
                        d -= 1
                    k += 1
                value = body[j + 1:k - 1]
            else:
                value = re.match(r"[^,\n]*", body[j:]).group(0)
            fields[f.group(1).lower()] = value.strip()
        entries[key] = fields
    return entries


def read_labels():
    """key -> the label the printed text shows, from biber's own output."""
    if not BBL.exists():
        return {}
    out, key = {}, None
    for line in BBL.read_text(errors="ignore").splitlines():
        m = re.search(r"\\entry\{([^}]*)\}", line)
        if m:
            key = m.group(1)
        m = re.search(r"\\field\{labelalpha\}\{([^}]*)\}", line)
        if m and key:
            out[key] = detex(m.group(1))
    return out


def cited():
    """Every key the book actually cites, as biblatex recorded it."""
    if not AUX.exists():
        return set()
    return set(re.findall(r"\\abx@aux@cite\{[^}]*\}\{([^}]*)\}",
                          AUX.read_text(errors="ignore")))


def build():
    bib, labels = read_bib(), read_labels()
    out, missing = {}, []
    for key in sorted(set(bib) | set(labels) | cited()):
        fields = bib.get(key)
        if fields is None:
            missing.append(key)
            out[key] = {"label": labels.get(key, key), "missing": True}
            continue
        entry = {"label": labels.get(key, ""),
                 "type": fields.get("type", ""),
                 "authors": names(fields.get("author") or fields.get("editor", "")),
                 "title": detex(fields.get("title", "")),
                 "year": detex(fields.get("year") or fields.get("date", "")),
                 "where": next((detex(fields[v]) for v in VENUE if fields.get(v)), ""),
                 "doi": fields.get("doi", "").strip(),
                 "url": fields.get("url", "").strip()}
        if fields.get("volume"):
            entry["volume"] = detex(fields["volume"])
        if fields.get("pages"):
            entry["pages"] = detex(fields["pages"])
        out[key] = {k: v for k, v in entry.items() if v}
    return out, missing, match_pdfs(out, bib)


def render(bib):
    return ("// Generated by build-bibliography.py — do not edit.\n"
            "// Loaded as a plain script, not fetched: the built site has to work\n"
            "// over file://, where fetching a sibling file is refused.\n"
            "window.__bookBib=" + json.dumps(bib, separators=(",", ":"),
                                             ensure_ascii=False) + ";\n")


def main(write):
    bib, missing, stray = build()
    js = render(bib)
    have_label = sum(1 for e in bib.values() if e.get("label"))
    have_pdf = sum(1 for e in bib.values() if e.get("pdf"))
    print(f"bibliography: {len(bib)} entries, {have_label} of them cited by the book, "
          f"{have_pdf} with a PDF to show, {len(js) / 1024:.0f} KB")
    if stray:
        print(f"\nin literature/pdfs but belonging to no entry ({len(stray)}) — "
              f"nothing in the book can open these:", file=sys.stderr)
        for name in stray:
            print(f"   {name}", file=sys.stderr)
    if missing:
        print(f"\ncited by the book but not defined in bib.bib ({len(missing)}) — "
              f"the printed text shows the raw key here, and so does the PDF:",
              file=sys.stderr)
        for key in missing:
            print(f"   {key}", file=sys.stderr)

    if OUT.exists() and OUT.read_text(encoding="utf-8") == js:
        print("static/bibliography.js is up to date.")
        return
    if not write:
        print("\nstatic/bibliography.js is out of date (re-run with --write).",
              file=sys.stderr)
        raise SystemExit(1)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(js, encoding="utf-8")
    print("wrote static/bibliography.js")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true",
                        help="write static/bibliography.js")
    main(parser.parse_args().write)
