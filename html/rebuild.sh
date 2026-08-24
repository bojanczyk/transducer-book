#!/usr/bin/env bash
# Rebuild the web edition of the book from the LaTeX sources one level up.
#
#   ./rebuild.sh              # refresh main.aux if stale, compile changed
#                             # chapters, run hugo -> dist/
#   ./rebuild.sh server       # …then `hugo server` for live preview
#   ./rebuild.sh --no-pdf     # skip the latexmk step (cross-references keep
#                             # whatever ../main.aux currently says)
#   ./rebuild.sh --pdf        # run latexmk even if nothing looks stale
#   ./rebuild.sh --force      # recompile every LaTeX block from scratch
#                             # (after changing macros.sty, the preamble, or
#                             # reflowtex itself), and drop stale cache entries
#
# Anything else on the command line is passed straight to hugo.
#
# The pipeline, in order:
#   1. ../main.pdf via latexmk — the *continuous* build, whose main.aux is the
#      only thing that can resolve a \ref from one chapter into another (each
#      chapter here compiles alone; see latex-preambles/book.tex).
#   2. build-references.py --write — carries the ourexamplecounter starting
#      values into content/*.md and cross-checks every number against main.aux.
#   2b. build-lean-map.py --write — joins each numbered result to its Lean
#      counterpart in ../transducer-lean, writing data/lean_map.json.
#   3. reflowtex's prebuild.py — compiles each {{< latex >}} block to a node
#      list, provisions fonts, writes data/ and static/.
#   4. hugo — assembles dist/.
set -euo pipefail

SITE="$(cd "$(dirname "$0")" && pwd)"
BOOK="$(cd "$SITE/.." && pwd)"

# TEXINPUTS is why the LaTeX side works at all: macros.sty and knowledges.tex
# (loaded by latex-preambles/book.tex) and transducer-book-pics.pdf
# (\includegraphics'd from macros.sty's \mypiccore) are found through
# kpathsea's search path rather than a fixed location. A *relative* entry is
# resolved against the directory lualatex itself runs in — always exactly
# SITE/.reflowtex-build/<hash>/, three levels below the book root — so this
# holds wherever the repository is checked out, with no machine-specific path
# anywhere. Non-recursive on purpose: `../../../` is the book root only, so
# kpathsea never descends back into html/ (or transducer-lean/, literature/…).
export TEXINPUTS="../../../:"

# ── where reflowtex itself lives ────────────────────────────────────────────
# Not an installable tool yet: prebuild.py and the viewer are used straight out
# of a checkout. Default is a sibling of the book repo; override with
# REFLOWTEX_ROOT=/path/to/reflowtex ./rebuild.sh
REFLOWTEX="${REFLOWTEX_ROOT:-$BOOK/../reflowtex}"
if [ ! -f "$REFLOWTEX/integrations/hugo/prebuild.py" ]; then
  cat >&2 <<EOF
error: no reflowtex checkout at $REFLOWTEX

  git clone -b devel https://github.com/radek-p/reflowtex "$REFLOWTEX"

or point REFLOWTEX_ROOT at an existing one.
EOF
  exit 1
fi
REFLOWTEX="$(cd "$REFLOWTEX" && pwd)"
HUGO_INT="$REFLOWTEX/integrations/hugo"

BRANCH="$(git -C "$REFLOWTEX" rev-parse --abbrev-ref HEAD 2>/dev/null || echo '?')"
if [ "$BRANCH" != "devel" ]; then
  echo "warning: reflowtex is on branch '$BRANCH'; this site needs devel" >&2
  echo "         (git -C $REFLOWTEX checkout devel)" >&2
fi

# ── arguments ───────────────────────────────────────────────────────────────
SERVE=""
PDF="auto"
HUGO_ARGS=()
for arg in "$@"; do
  case "$arg" in
    server)   SERVE=1 ;;
    --no-pdf) PDF="no" ;;
    --pdf)    PDF="yes" ;;
    --force)  PREBUILD_ARGS="${PREBUILD_ARGS:-} --force --prune" ;;
    *)        HUGO_ARGS+=("$arg") ;;
  esac
done

# ── 0. Python deps ──────────────────────────────────────────────────────────
# protobuf + fonttools live in reflowtex's own virtualenv (`make venv` there);
# create it here too so this script works standalone. Needs Python 3.10+ —
# macOS's /usr/bin/python3 is often older, hence find_python.sh.
VENV="$REFLOWTEX/.venv"
if [ -x "$VENV/bin/python3" ] && "$VENV/bin/python3" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)' 2>/dev/null; then
  :
else
  BASE_PYTHON="$("$REFLOWTEX/scripts/find_python.sh")"
  echo "Creating $VENV with $BASE_PYTHON ($("$BASE_PYTHON" --version))"
  rm -rf "$VENV"
  "$BASE_PYTHON" -m venv "$VENV"
fi
PYTHON="$VENV/bin/python3"
if [ ! -f "$VENV/.deps-installed" ] || [ "$REFLOWTEX/src/encode/requirements.txt" -nt "$VENV/.deps-installed" ]; then
  "$VENV/bin/pip" install --upgrade pip
  "$VENV/bin/pip" install -r "$REFLOWTEX/src/encode/requirements.txt"
  touch "$VENV/.deps-installed"
fi

# reflowtex checks in the protoc-generated src/encode/latex_pb2.py, and the
# protobuf runtime refuses gencode from an older major version outright. The
# pipeline regenerates that file whenever the schema is newer than it, so if
# the import fails, nudging the schema's mtime is enough to get a copy that
# matches whatever protobuf the venv just installed.
if ! PYTHONPATH="$REFLOWTEX/src/encode" "$PYTHON" -c 'import latex_pb2' 2>/dev/null; then
  echo "protobuf gencode is out of step with the runtime — will regenerate it"
  touch "$REFLOWTEX/src/schema/latex.proto"
fi

# ── 1. the continuous PDF build, for cross-references ───────────────────────
if [ "$PDF" != "no" ]; then
  STALE=""
  if [ ! -f "$BOOK/main.aux" ]; then
    STALE="main.aux does not exist yet"
  elif [ -n "$(find "$BOOK" -maxdepth 1 \( -name '*.tex' -o -name '*.sty' -o -name '*.bib' \) -newer "$BOOK/main.aux" -print -quit)" ]; then
    STALE="sources are newer than main.aux"
  fi
  if [ "$PDF" = "yes" ] || [ -n "$STALE" ]; then
    [ -n "$STALE" ] && echo "== latexmk: $STALE"
    if command -v latexmk >/dev/null 2>&1; then
      # A failed PDF build is not a reason to abandon the site build: the
      # previous main.aux is still there, and build-references.py below cross-
      # checks the numbers against it (and refuses on a dangling \ref), so a
      # genuinely stale one gets caught rather than quietly shipped. Warn and
      # carry on — but do fix the PDF, since this run's numbers came from the
      # aux of an older one.
      if ! (cd "$BOOK" && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex); then
        echo >&2
        echo "warning: latexmk failed — building the site against the existing" >&2
        echo "         ../main.aux instead. Fix the PDF build and re-run." >&2
        echo >&2
      fi
    else
      echo "warning: latexmk not found — skipping the PDF refresh; \\ref numbers" >&2
      echo "         will be whatever ../main.aux already holds" >&2
    fi
  fi
fi

# ── 2. per-chapter counters, cross-checked against main.aux ─────────────────
"$PYTHON" "$SITE/build-references.py" --write

# ── 2b. the book ↔ Lean map ─────────────────────────────────────────────────
# Regenerated on every build rather than kept by hand, because ../transducer-lean
# is a mirror of Aristotle's server and is replaced wholesale on each harvest:
# the Lean names move under us, the book numbers do not. Drift is reported but
# is deliberately not fatal — a result whose two sides disagree simply goes
# unlinked, which is no reason to refuse to build the site.
if ! "$PYTHON" "$SITE/build-lean-map.py" --write; then
  echo >&2
  echo "warning: the book <-> Lean map has drifted — see the report above." >&2
  echo "         Affected results will render without a formalisation link." >&2
  echo >&2
fi

# ── 3. compile the LaTeX blocks ─────────────────────────────────────────────
# Vendor the two integration layout files first (the docs' "copy these into
# layouts/" step, done automatically so they can never drift).
mkdir -p "$SITE/layouts/shortcodes" "$SITE/layouts/partials"
cp "$HUGO_INT/layouts/shortcodes/latex.html"          "$SITE/layouts/shortcodes/latex.html"
cp "$HUGO_INT/layouts/partials/reflowtex-viewer.html" "$SITE/layouts/partials/reflowtex-viewer.html"

# Only blocks whose content hash changed are recompiled; -j 1 because a single
# chapter's lualatex run is already the long pole and parallel runs mostly
# fight over the same TeX caches.
# shellcheck disable=SC2086
"$PYTHON" "$HUGO_INT/prebuild.py" "$SITE" -j 1 ${PREBUILD_ARGS:-}

# ── 4. the site ─────────────────────────────────────────────────────────────
if [ -n "$SERVE" ]; then
  exec hugo server --source "$SITE" "${HUGO_ARGS[@]+"${HUGO_ARGS[@]}"}"
fi
exec hugo --source "$SITE" --minify "${HUGO_ARGS[@]+"${HUGO_ARGS[@]}"}"
