# The web edition of the book

This directory renders the book as a reflowable website: the same LaTeX
sources that produce `../main.pdf`, typeset by a real TeX run and re-broken to
the reader's screen in the browser (not a rasterised page image, not a
MathJax approximation). It is built with [Reflow TeX](https://github.com/radek-p/reflowtex)
by Radek Piórkowski, and is a rehousing of the package he prepared in
`../html-radek/` — same layouts, same colour map, same chapter structure, with
the paths changed so that the site lives inside the book's own repository and
reads the sources directly from `../`.

Everything is driven by one script:

```sh
./rebuild.sh            # rebuild dist/
./rebuild.sh server     # …and serve it, live-reloading while you edit
```

`dist/index.html` also works opened straight off disk — `file://` is fine, no
server needed.

## One-time setup

1. **Reflow TeX**, on its `devel` branch, checked out next to the book repo:

   ```sh
   git clone -b devel https://github.com/radek-p/reflowtex ~/Documents/ksiazki/reflowtex
   ```

   `rebuild.sh` looks for it at `../../reflowtex` by default; anywhere else
   works if you set `REFLOWTEX_ROOT=/path/to/reflowtex`. It is not installed,
   just used out of the checkout — the compiler (`src/`), the Hugo integration
   (`integrations/hugo/prebuild.py`) and the browser-side viewer all come from
   there, so `git pull` in that directory is how the tool gets updated.

2. **The command-line tools**: `lualatex` (TeX Live), `dvisvgm`, `gs`
   (Ghostscript), `protoc`, `hugo` (extended), `python3` ≥ 3.10, and `latexmk`
   for the PDF step. On this machine all of them are already present
   (MacTeX + Homebrew). `make check` in the reflowtex checkout verifies them.

3. Nothing else. The Python side (protobuf, fonttools) is installed into
   `reflowtex/.venv` by `rebuild.sh` itself on first run.

## What `rebuild.sh` does

1. **`latexmk` on `../main.tex`**, if any `.tex`/`.sty`/`.bib` in the book root
   is newer than `../main.aux`. Each chapter here is compiled *in isolation*,
   so a `\ref` from Chapter 12 to a theorem in Chapter 3 has nothing to resolve
   against on its own; `xr-hyper` resolves it against the `main.aux` of the
   ordinary continuous PDF build (see `latex-preambles/book.tex`). That is the
   only reason this step exists — and why the web edition's numbers are always
   the printed edition's numbers. Skip it with `--no-pdf`, force it with
   `--pdf`.
2. **A snapshot of `../main.aux`** into `.aux-snapshot/`, checked for the line
   LaTeX writes last. Every block resolves its cross-references against that
   copy rather than against `../main.aux` itself, because your editor rewrites
   that file every time it rebuilds the PDF — and a block that reads it
   mid-write dies with `! File ended within \read`, taking the build down with
   it. The copy also means every block in one build sees the same numbering.
3. **The content steps**, each with `--write`: `build-references.py`
   (per-chapter counters, below), `build-exercises.py` (a block per exercise so
   its solution can be folded), `build-lean-map.py` (the book ↔ Lean join) and
   `build-search-index.py` (the search index).
4. **`build-source-stamps.py --write`** — writes a hash of each chapter's
   source into the block that `\input`s it, and a hash of the shared inputs
   into the preamble. This is load-bearing; see below.
5. **`prebuild.py`** (from reflowtex) — compiles every `{{< latex >}}` block
   into a binary node list under `data/latex_blocks/`, subsets the fonts it
   used into `static/fonts/`, and copies the viewer into `static/`. Blocks are
   cached by key, so an edit to one chapter recompiles that chapter only: a
   routine rebuild is seconds to a couple of minutes, a cold one (or `--force`)
   is more like twenty.
6. **`hugo`** — assembles `dist/`.

`--force` is rarely needed now — the stamps below invalidate what an edit
affects. Reach for it after updating reflowtex itself, which changes how blocks
compile without changing anything this repository can hash.

## How the site is put together

### The landing page is the preface

`content/_index.md` holds one LaTeX block that `\input`s `../preface.tex`, so
opening the site without asking for anything in particular shows what the book
says about itself. It is an ordinary reading page in every other respect —
sidebar, search, reader controls, the lot — which is why `baseof.html` no
longer treats the home page as a special case, and why `list.html` is now just
`{{ .Content }}`: the chapter list it used to print is the sidebar's job.

The preface has no entry of its own in `data/book_toc.json`; the book's title
at the top of the sidebar is the link back to it. Say the word if you would
rather it were listed above "Introduction" as well.

### One content page per chapter

`content/01-introduction.md` … `content/17-pebble-transducers.md`, one per
`\input` in `../main.tex`. Each is a few lines of front matter plus a small
LaTeX wrapper that sets the chapter's counters and pulls in the real source:

```markdown
{{< latex preamble="book" align="justify" last-line-penalty="1000000" color-map="transducer-book-color-map" >}}
\setcounter{mypart}{0}
\setcounter{section}{0}
\setcounter{ourexamplecounter}{0}
\input{../../../intro.tex}
{{< /latex >}}
```

The `../../../` is not a guess: every block compiles in its own
`html/.reflowtex-build/<hash>/`, always exactly three directories below the
book root. There is deliberately no second copy of the LaTeX for the web
edition — this is the same `intro.tex` the PDF uses, so the two cannot drift.
Keep it that way, and keep absolute paths (`/Users/…`) out of this directory
entirely.

### Why the blocks carry source stamps

reflowtex caches a compiled block under the hash of the block's own text plus
its preamble, and skips any block whose key it already has. That is right for a
block that *contains* its LaTeX. Ours do not — a chapter's block is three
`\setcounter` lines and an `\input` — so its key did not move when the chapter
was rewritten, and **editing a chapter changed nothing on the site** until
someone passed `--force`. A silent wrong answer, and the reason this step
exists.

`build-source-stamps.py` writes the missing dependency in as a LaTeX comment,
which changes the key and nothing else:

- `% source stamp intro.tex:8a3f2b1c` inside the chapter's own block, so
  editing that chapter recompiles that chapter;
- one stamp in `latex-preambles/book.tex`, which is part of *every* block's key
  by construction, covering what every block reads through the preamble:
  `../macros.sty`, `../knowledges.tex`, the picture file — and the numbers in
  `../main.aux`, since a `\ref` is typeset as whatever number the continuous
  build gave it, and a chapter showing last week's numbering is stale in the
  same silent way.

Only the *numbers* are taken from `main.aux`, not the whole file: page numbers
move whenever anything above them grows, and recompiling the whole book because
a paragraph got longer would make every build a cold one. Expect a cold build
whenever a numbered result is added or removed, though — that really does
change what other chapters print.

Copying the chapters into `content/` so that reflowtex could hash them would
also have worked, and was rejected: there is deliberately one copy of the
book's LaTeX, and it is the one the PDF builds from.

Because every edit now mints a new key, the old key's compiled block and build
directory are dead as soon as it lands — a few hundred megabytes per month of
editing if nothing collects them. So `rebuild.sh` passes `--prune` and deletes
the build directories that no longer have a compiled block, keeping
`data/latex_blocks/` and `.reflowtex-build/` to exactly the blocks the site
uses. The cost is that undoing an edit recompiles that chapter rather than
finding it in the cache.

### Per-chapter counters

Compiling a chapter alone means its counters start at zero unless told
otherwise, and this is the part that fails *silently* — wrong numbers, not an
error. Two cases:

- `mypart` and `section` are structural: which part and section a chapter
  opens in. They are hardcoded in `build-references.py`'s `CHAPTERS` list, and
  setting `section` is enough to fix `theorem` and everything aliased to it
  (amsthm resets those per section on its own).
- `ourexamplecounter` (`macros.sty`'s numbered examples) runs continuously
  across the whole book and is never reset, so each chapter's correct starting
  value is however many examples all the earlier chapters contain — a number
  that shifts whenever you add or delete an example anywhere upstream.

`build-references.py` counts `\begin{myexample}` chapter by chapter, checks
every computed number against what `../main.aux` says that label actually got
in the continuous build, then writes the values into the `\setcounter` lines
(`--write`, which `rebuild.sh` passes). Run it bare for a read-only check. If
it reports a mismatch rather than a drift, the PDF build and this script
disagree about the book — usually a stale `main.aux`, so rebuild the PDF
first.

### Table of contents and chapter titles

Menu labels and on-page titles are themselves compiled LaTeX (so they get the
book's fonts and math), which means they cannot live in a Hugo template —
shortcodes only expand in content. Three hand-written pieces:

- `data/book_toc.json` — the sidebar tree: `href` + the *name* of the compiled
  snippet holding the label, with `children` for the chapters inside a part.
- `data/page_titles.json` — page URL → snippet name for the page's own title.
- `content/menu-block-cache.md` — a `render = "never"` page holding all those
  snippets as inline blocks tagged `as="menu-04-krohn-rhodes.tex"` etc.
  `as=` registers a block under a name that any template can then look up
  (`layouts/partials/book-toc-node.html`, `latex-file-block.html`).

Adding or renaming a chapter means touching all three, plus `CHAPTERS` in
`build-references.py` and a new `content/NN-slug.md`. Nothing generates them.

### Citable links to results

Clicking any numbered result — theorem, lemma, definition, claim, corollary,
exercise — opens the third column on it, with its address at the top, above
the formalisation:

```
https://…/12-two-way-transducers/#theorem-C.2.5      [Copy]
```

The fragment is `kind-number`, built from the same `(kind, number)` pair
`build-lean-map.py` joins the book to Lean on, so it is unique and reads as
the citation itself. The book's own `#thm:composition-of-two-way-transducers`
anchors are untouched and still work — the readable name is added beside the
viewer's, never instead of it — so links given out earlier keep landing where
they did.

Two things worth knowing:

- **The address is taken from the browser, not from a base configured here.**
  It is therefore right wherever the site is served from, and shows a
  `file://` path when you are reading the built site off disk. Nothing needs
  configuring when the site is published; if you ever want the citation to
  read as the public URL even in local preview, that is the one thing to
  change (in `layouts/partials/lean-pane.html`, `citeURL`).
- **A number-based link moves if the book is renumbered.** Inserting a chapter
  ahead of Part C turns `#theorem-C.2.5` into a link to nothing in particular.
  That is the price of a citation that is legible; the LaTeX-label anchors are
  the stable alternative if a link ever has to outlive a renumbering.

Following such a link scrolls to the result and glows on its heading for a
moment. That takes some work behind the scenes, because the viewer paints
lazily: the anchor a fragment names usually does not exist yet when the page
loads, so the wanted one is remembered and tried again after each relayout,
and the landing is corrected as the lines above it are painted (until the
reader takes over with a wheel, a touch or a key). See `scrollToSlug`, `aim`
and `flash` in `layouts/partials/lean-pane.html`.

### Searching

The box above the contents searches the whole book, not just the chapter being
read. Typing folds the results out between the box and the contents — the
contents are pushed down, not replaced, so you can still see where you are —
and the × (or Escape) folds them away again. `/` or ⌘K puts the cursor in the
box; the arrow keys and Enter work through the results without the mouse.

**Where the text comes from.** Nothing on a rendered page is searchable text:
Reflow TeX ships each chapter as a compiled node list and the viewer paints it
as line-level `<svg>`s, so the words in the browser are glyph runs with the
spaces between them implied by position. `build-search-index.py` therefore
builds the index from the LaTeX itself — stripping the maths, resolving `\ref`s
to the numbers the book gives them, expanding `\mso` and its friends to the
words they print — and cuts each chapter into ~1000 passages, one per
paragraph, per section heading and per numbered result.

It writes `static/search-index.js`, ~300 KB, as a **plain script rather than
JSON**: the built site has to work opened off disk, and over `file://` fetching
a sibling file is a cross-origin request the browser refuses, while a
`<script src>` is not. One copy is shared by every page.

**Where a hit takes you.** Each passage is attributed to an anchor the page
already has — a readable `theorem-C.2.5` anchor, a `\label`, or the exercise
block it belongs to (98% of passages have one; the rest land at the top of
their chapter). That gets the reader to the right neighbourhood. The last few
lines are then done in the browser: `?find=` carries the query across the page
load, and `search.html`'s `findLine` looks for the words in the painted text
and scrolls onto the line holding them, which then glows for a moment.

That last step has to work around the same things the citation landing does,
plus two of its own: the painted text runs words together wherever the
typesetter changed font mid-line (so matching is done with the spaces and
punctuation removed on both sides), and a phrase can be broken across a line
break (so consecutive lines are also tried joined). A hit inside an exercise's
folded solution opens the fold.

**When the sources change**, `rebuild.sh` regenerates the index like everything
else. `python3 build-search-index.py` on its own reports what it would write
and exits non-zero if `static/search-index.js` has fallen behind.

### Colour theme

`latex-color-maps/transducer-book-color-map.json` remaps the colours
`../macros.sty` defines onto values that stay legible in all four reader
themes (light / dark / sepia / contrast). Chapters opt in with
`color-map="transducer-book-color-map"` on their shortcode.

### Layouts

`layouts/` holds the site's own templates — the shell with the sidebar, the
reader controls (width / text size / theme), the TOC partials. Two files in
there are *not* the site's own: `layouts/shortcodes/latex.html` and
`layouts/partials/reflowtex-viewer.html` are vendored copies that `rebuild.sh`
refreshes from the reflowtex checkout on every run, so don't edit them here.

Reader settings ride along in the URL (`?theme=&width=&zoom=`) as well as
`localStorage`, because under `file://` every page is its own storage origin
in some browsers and the setting would otherwise be lost when following a link
to the next chapter.

## Troubleshooting

- **`! LaTeX Error: File 'X' not found`** — something is reaching for `X` by
  bare name and it isn't in the book root. Either give it a relative path from
  the block's build directory (`../../../X`) or extend `TEXINPUTS` at the top
  of `rebuild.sh`.
- **`! File ended within \read`, or a block dies inside `xr-hyper`** — the aux
  it was reading was being rewritten at that moment, i.e. something rebuilt the
  PDF while the site was building. Step 2 above is meant to prevent this; if it
  happens anyway, the snapshot was taken during the write, so just re-run.
- **An edit to a chapter does not show up** — that was the cache bug the source
  stamps fix; check that `build-source-stamps.py` ran (it prints what it
  invalidated) and that the chapter is listed in its `PAGES`.
- **A page shows "LaTeX block not compiled"** — a name in `book_toc.json` or
  `page_titles.json` doesn't match any `as="…"` in `content/menu-block-cache.md`
  (or prebuild hasn't run since it was added).
- **One counter is off** — see the counters section; rebuild the PDF, then
  `./rebuild.sh`.
- **Numbers or references look right in the PDF but not on the site** —
  `main.aux` was stale when the site was built. `./rebuild.sh --pdf`.
- **Everything recompiles when you expected an incremental build** — the
  preamble or `macros.sty` changed; that is correct, every block depends on
  them.
- **Reflow TeX itself** (shortcode attributes, viewer internals, theming, font
  handling) — the reflowtex checkout's own `README.md`, `docs/architecture.md`,
  `src/viewer/README.md` and `integrations/hugo/README.md`.

`../html-radek/README.md` is Radek's original write-up of the pipeline,
including the parts that only matter when starting a *different* book from
scratch.
