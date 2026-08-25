#!/usr/bin/env python3
"""Build the search index the sidebar's search box reads.

Nothing on a built page is searchable text. Reflow TeX ships each chapter as a
compiled node list and the viewer draws it as line-level <svg> segments, so the
words in the browser are glyph runs — with the spaces between them implied by
position rather than written down. That is fine to read and useless to grep,
which is why the index is built here, from the LaTeX the chapters are made of,
rather than scraped back out of the rendered site.

What comes out is one plain .js file (not .json): the built site has to work
opened straight off disk, and over file:// fetching a sibling file is a
cross-origin request the browser refuses, while a plain <script src> is not.
It is loaded once per page and shared by all of them, so a search finds results
in every chapter, not just the one being read.

Each entry records where it came from as an *anchor* the page already has —
either one of the readable `theorem-C.2.5` anchors (see lean-pane.html) or a
`\\label` the viewer turns into a scroll target. Prose between labels is
attributed to the last anchor before it, so following a hit lands in the right
neighbourhood; the search UI then looks for the words themselves in the painted
text and moves the last few lines (see search.html's refine()).

    python3 build-search-index.py           # report; exit 1 if the index is stale
    python3 build-search-index.py --write   # …and write static/search-index.js

rebuild.sh passes --write, so the index follows the sources by itself; running
it bare is the read-only check.
"""

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent      # html/
BODY = ROOT.parent                          # the book repo root
CONTENT = ROOT / "content"
AUX = BODY / "main.aux"
MACROS = BODY / "macros.sty"
OUT = ROOT / "static" / "search-index.js"

# The preface, which the site shows as its landing page and so has no directory
# of its own — an empty slug. Searchable like anything else the book says.
FRONT = [("", "preface.tex", "Preface")]

# (page slug, source file) in book order — the same list build-references.py
# keeps, for the same reason: nothing in the sources states it.
CHAPTERS = [
    ("01-introduction", "intro.tex"),
    ("02-mealy-machines-introduction", "mealy-intro.tex"),
    ("03-mealy-machines", "mealy.tex"),
    ("04-krohn-rhodes", "krohn-rhodes.tex"),
    ("05-rational-functions-introduction", "rational-intro.tex"),
    ("06-rational-relations", "rational-relations.tex"),
    ("07-rational-functions", "rational-functions.tex"),
    ("08-weighted-automata", "weighted.tex"),
    ("09-machine-independent", "myhill-nerode.tex"),
    ("10-regular-functions-introduction", "regular-intro.tex"),
    ("11-prime-regular-functions", "regular-primes.tex"),
    ("12-two-way-transducers", "2dfa.tex"),
    ("13-streaming-string-transducers", "sst.tex"),
    ("14-logic", "logic.tex"),
    ("15-polyregular-functions-introduction", "polyregular-intro.tex"),
    ("16-for-transducers", "polyregular-for.tex"),
    ("17-pebble-transducers", "polyregular-pebble.tex"),
]

# Environments whose content is mathematics: dropped whole. Their contents are
# symbols laid out in two dimensions, which no amount of stripping turns into
# words worth matching a query against.
MATH_ENVS = ["align*", "align", "equation*", "equation", "eqnarray*", "eqnarray",
             "gather*", "gather", "multline*", "multline", "array", "smallmatrix",
             "pmatrix", "bmatrix", "matrix", "cases", "tikzcd", "tikzpicture"]

# Theorem-likes: each becomes an entry of its own, titled with the number the
# printed book gives it.
RESULT_ENVS = ["theorem", "lemma", "claim", "corollary", "definition", "fact",
               "proposition", "myexample", "example", "exercise", "remark"]

# What each environment is called in the book: macros.sty names the numbered
# examples `myexample`, and "Myexample" is not what the page says.
DISPLAY = {"myexample": "Example"}

# Macros that print their argument as running text.
UNWRAP = ["emph", "textbf", "textit", "textsc", "text", "underline", "mathrm",
          "mathit", "textrm", "footnote", "caption", "intro", "kl", "ka", "reintro"]

# Macros to remove along with their arguments: they print nothing a reader
# would search for.
DROP_WITH_ARG = ["label", "pageref", "cite", "citep", "citet",
                 "index", "todo", "input", "usepackage",
                 "mypic", "mypiccore", "vspace", "hspace", "setcounter",
                 "newcommand", "renewcommand", "knowledge", "AP", "phantomintro"]

SENTENCE_END = re.compile(r"(?<=[.!?])\s+")
MAX_LEN = 600           # characters per entry; long paragraphs are split on sentences
MIN_LEN = 25            # shorter than this is not worth an entry of its own


# --------------------------------------------------------------------------
# LaTeX → words
# --------------------------------------------------------------------------

def brace_group(s, i):
    """The {...} starting at i, respecting nesting: (content, index after it)."""
    if i >= len(s) or s[i] != "{":
        return None, i
    depth, j = 0, i
    while j < len(s):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    return s[i + 1:], len(s)


def strip_comments(text):
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def abbreviations():
    """{'mso': 'MSO', …} — the small-caps abbreviations macros.sty defines.

    Read rather than listed, so that searching for SST or PSpace keeps working
    when the book gains another one. Only the zero-argument \\textsc kind: those
    are the ones that stand for a word a reader would type.
    """
    if not MACROS.exists():
        return {}
    out = {}
    for m in re.finditer(r"\\newcommand\{\\([A-Za-z]+)\}\{([^\n]*?)\}\s*$",
                         MACROS.read_text(errors="ignore"), re.M):
        name, body = m.group(1), m.group(2)
        sc = re.search(r"\\textsc\{([^{}]*)\}", body)
        if sc:
            out[name] = sc.group(1).upper()
    return out


ABBREV = None
NUMBERS = {}        # label -> the number the PDF build gave it, for \ref


def strip_latex(text):
    """Markup out, words in — as close to what the page says as text can get."""
    global ABBREV
    if ABBREV is None:
        ABBREV = abbreviations()

    # Mathematics first, so that what is left is prose and the macros in it are
    # text-level ones.
    for env in MATH_ENVS:
        text = re.sub(r"\\begin\{" + re.escape(env) + r"\}.*?\\end\{" + re.escape(env) + r"\}",
                      " ", text, flags=re.S)
    text = re.sub(r"\\\[.*?\\\]", " ", text, flags=re.S)
    # Inline math: a symbol or two is part of the sentence ("the function f"),
    # a formula is not. The short ones stay, stripped to their letters.
    def inline(m):
        inner = re.sub(r"[\\{}$^_]", "", m.group(1)).strip()
        return inner if len(inner) <= 3 and inner.isalnum() else " "
    text = re.sub(r"(?<!\\)\$([^$]*)\$", inline, text, flags=re.S)

    # A cross-reference reads as its number in the book, and a snippet that says
    # "from Section A.2" is worth more than one that says "from Section~:".
    def numbered(m):
        return NUMBERS.get(m.group(2), "").lstrip(".")
    text = re.sub(r"\\(ref|cref|Cref|autoref)\s*\{([^}]*)\}", numbered, text)
    text = re.sub(r"\\eqref\s*\{([^}]*)\}",
                  lambda m: "(" + NUMBERS.get(m.group(1), "").lstrip(".") + ")", text)
    text = text.replace("~", " ")

    for name, word in ABBREV.items():
        text = re.sub(r"\\" + name + r"\b\s*(\{\})?", word + " ", text)

    for name in DROP_WITH_ARG:
        text = re.sub(r"\\" + name + r"\s*(\[[^\]]*\])?", lambda m: "\x00", text)
    # each marker eats the brace groups that followed the macro it replaced
    out, i = [], 0
    while i < len(text):
        if text[i] == "\x00":
            i += 1
            while i < len(text) and text[i] == "{":
                _, i = brace_group(text, i)
        else:
            out.append(text[i])
            i += 1
    text = "".join(out)

    for _ in range(4):                       # \emph{\textbf{x}} needs a few passes
        before = text
        text = re.sub(r"\\(?:" + "|".join(UNWRAP) + r")\s*\{", "{", text)
        if text == before:
            break
    text = re.sub(r"\\(?:begin|end)\{[^}]*\}", " ", text)
    text = re.sub(r"\\item\b", " ", text)
    text = re.sub(r"\\[A-Za-z@]+\*?", " ", text)      # any macro still standing
    text = text.replace("{", " ").replace("}", " ").replace("\\", " ")
    text = re.sub(r"[ \t]+", " ", text)
    text = re.sub(r" ([,.;:!?])", r"\1", text)
    return text


# --------------------------------------------------------------------------
# the book's own numbering
# --------------------------------------------------------------------------

NUMBER = re.compile(r"[A-D]?\.\d+\.\d+")


def read_aux():
    """label -> (kind, number) for numbered results; NUMBERS for everything else.

    Same source and same shape as build-lean-map.py's read_book: hyperref names
    an anchor after the counter that produced it, so the anchor's prefix is what
    tells a Lemma from a Theorem when the counters themselves are shared.
    """
    if not AUX.exists():
        return {}
    aux = AUX.read_text(errors="ignore")
    out = {}
    for m in re.finditer(r"\\newlabel\{([^}]+)\}\{\{([^{}]*)\}\{([^{}]*)\}", aux):
        label, number = m.group(1), m.group(2)
        if label.endswith("@cref"):
            continue
        NUMBERS.setdefault(label, number)
        if not NUMBER.fullmatch(number):
            continue
        rest = aux[m.end():m.end() + 400]
        kind = re.search(r"\{(theorem|lemma|claim|corollary|definition|fact|"
                         r"proposition|example|exercise)\.\d+\}", rest)
        if kind:
            out[label] = (kind.group(1), number.lstrip("."))
    return out


# --------------------------------------------------------------------------
# one chapter
# --------------------------------------------------------------------------

STRUCT = re.compile(
    r"\\(section|subsection|subsubsection|paragraph)\*?\s*\{"
    r"|\\label\s*\{([^}]*)\}"
    r"|\\begin\{(" + "|".join(RESULT_ENVS) + r")\}"
    r"|\\end\{(" + "|".join(RESULT_ENVS) + r")\}"
    r"|\\exer\s*\{")


def chapter_entries(page, source, labels, anchors):
    """Every searchable passage of one chapter, in reading order."""
    text = strip_comments((BODY / source).read_text(errors="ignore"))
    entries = []
    heading = ""            # the section the reader would say they are in
    anchor = ""             # the nearest thing on the page we can scroll to
    prose_from = 0          # where the current run of prose started
    exercise_no = 0         # position in the chapter — see the \exer branch

    def flush(upto, title="", kind=""):
        """Turn the source between prose_from and upto into entries."""
        raw = strip_latex(text[prose_from:upto])
        for chunk in re.split(r"\n\s*\n", raw):
            chunk = " ".join(chunk.split())
            if len(chunk) < MIN_LEN:
                continue
            for piece in split_long(chunk):
                entries.append({"a": anchor, "h": heading, "k": kind,
                                "t": piece, "n": title})

    i = 0
    while True:
        m = STRUCT.search(text, i)
        if not m:
            flush(len(text))
            break
        flush(m.start())
        kw, lab, env_open, env_close, = m.group(1), m.group(2), m.group(3), m.group(4)

        if kw:                                   # a heading
            title, after = brace_group(text, m.end() - 1)
            # \section{…}\label{…}: the label comes after the heading but names
            # it, so it is this heading's own anchor, not the previous one's.
            ahead = re.match(r"\s*\\label\s*\{([^}]*)\}", text[after:])
            if ahead and ahead.group(1) in anchors:
                anchor = ahead.group(1)
            heading = " ".join(strip_latex(title).split())
            if heading:
                entries.append({"a": anchor, "h": "", "k": "section",
                                "t": heading, "n": ""})
            i = prose_from = after
        elif lab is not None:                    # a scroll target on the page
            if lab in labels:                    # a numbered result: readable anchor
                kind, number = labels[lab]
                anchor = kind + "-" + number
            elif lab in anchors:                 # any other \label the viewer kept
                anchor = lab
            i = prose_from = m.end()
        elif env_open:                           # a theorem-like: its own entry
            end = text.find("\\end{" + env_open + "}", m.end())
            end = len(text) if end < 0 else end
            body = text[m.end():end]
            lab_m = re.search(r"\\label\s*\{([^}]*)\}", body)
            if lab_m and lab_m.group(1) in labels:
                kind, number = labels[lab_m.group(1)]
                anchor = kind + "-" + number
                title = kind.capitalize() + " " + number
            elif lab_m and lab_m.group(1) in anchors:
                anchor = lab_m.group(1)
                title = DISPLAY.get(env_open, env_open.capitalize())
            else:
                title = DISPLAY.get(env_open, env_open.capitalize())
            prose_from = m.end()
            flush(end, title=title, kind=env_open)
            i = prose_from = end
        elif env_close:
            i = prose_from = m.end()
        else:                                    # \exer{statement}{solution}
            stmt, after = brace_group(text, m.end() - 1)
            sol, after = brace_group(text, after)
            # build-exercises.py re-emits each exercise as its own block at the
            # foot of the page, in source order, as <div class="exercise"
            # id="exercise-N">. That div is a better anchor than any \label
            # before it — it *is* the exercise — and it is where a hit in a
            # solution has to land, since the solution is folded inside it.
            exercise_no += 1
            where = "exercise-%d" % exercise_no
            lab_m = re.search(r"\\label\s*\{([^}]*)\}", stmt or "")
            title = "Exercise"
            if lab_m and lab_m.group(1) in labels:
                title = "Exercise " + labels[lab_m.group(1)][1]
            for part, what, sol_flag in ((stmt, title, 0),
                                         (sol, title + " — solution", 1)):
                body = " ".join(strip_latex(part or "").split())
                if len(body) < MIN_LEN:
                    continue
                for piece in split_long(body):
                    e = {"a": where, "h": heading, "k": "exercise",
                         "t": piece, "n": what}
                    if sol_flag:
                        e["s"] = 1          # …inside a <details> the page folds away
                    entries.append(e)
            i = prose_from = after
    return entries


def split_long(chunk):
    """Long paragraphs, cut on sentence ends, so a hit points somewhere narrow."""
    if len(chunk) <= MAX_LEN:
        return [chunk]
    out, cur = [], ""
    for sentence in SENTENCE_END.split(chunk):
        if cur and len(cur) + len(sentence) > MAX_LEN:
            out.append(cur.strip())
            cur = ""
        cur += sentence + " "
    if cur.strip():
        out.append(cur.strip())
    return out


# --------------------------------------------------------------------------

def page_titles():
    """slug -> the chapter's title, from its content page's front matter."""
    out = {}
    for slug, _ in CHAPTERS:
        md = CONTENT / (slug + ".md")
        if not md.exists():
            continue
        m = re.search(r'^title\s*=\s*"([^"]*)"', md.read_text(), re.M)
        out[slug] = m.group(1) if m else slug
    return out


def build():
    labels = read_aux()
    link_map = ROOT / "data" / "latex_link_map.json"
    anchors = set(json.loads(link_map.read_text())) if link_map.exists() else set()
    titles = page_titles()

    pages, entries = [], []
    everything = FRONT + [(slug, source, None) for slug, source in CHAPTERS]
    for slug, source, name in everything:
        if not (BODY / source).exists():
            print(f"  skipped {source}: not found", file=sys.stderr)
            continue
        pages.append({"u": slug, "t": name or titles.get(slug, slug)})
        for e in chapter_entries(slug, source, labels, anchors):
            e["p"] = len(pages) - 1
            entries.append(e)
    return {"pages": pages, "entries": entries}


def render(index):
    return ("// Generated by build-search-index.py — do not edit.\n"
            "// Loaded as a plain script, not fetched: the built site has to work\n"
            "// over file://, where fetching a sibling file is refused.\n"
            "window.__bookSearch=" + json.dumps(index, separators=(",", ":"),
                                                ensure_ascii=False) + ";\n")


def main(write):
    index = build()
    js = render(index)
    by_page = {}
    for e in index["entries"]:
        by_page[e["p"]] = by_page.get(e["p"], 0) + 1
    print(f"search index: {len(index['entries'])} passages over "
          f"{len(index['pages'])} chapters, {len(js) / 1024:.0f} KB")
    for i, p in enumerate(index["pages"]):
        print(f"  {p['u']:42s} {by_page.get(i, 0):5d}")
    anchored = sum(1 for e in index["entries"] if e["a"])
    print(f"{anchored} of {len(index['entries'])} passages have an anchor to land on "
          f"({100 * anchored / max(1, len(index['entries'])):.0f}%)")

    if OUT.exists() and OUT.read_text(encoding="utf-8") == js:
        print("static/search-index.js is up to date.")
        return
    if not write:
        print("\nstatic/search-index.js is out of date (re-run with --write).",
              file=sys.stderr)
        raise SystemExit(1)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(js, encoding="utf-8")
    print("wrote static/search-index.js")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true",
                        help="write static/search-index.js")
    main(parser.parse_args().write)
