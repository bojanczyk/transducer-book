#!/usr/bin/env bash
# Put the web edition on the web.
#
#   ./publish.sh              # rebuild, then send whatever changed
#   ./publish.sh -n           # …say what it would send, and send nothing
#   ./publish.sh --no-build   # send dist/ exactly as it stands
#
# The destination and the address it will be served from:
#   PUBLISH_DEST=user@host:path/ PUBLISH_URL=https://…/ ./publish.sh
set -euo pipefail

SITE="$(cd "$(dirname "$0")" && pwd)"
DEST="${PUBLISH_DEST:-bojan@duch.mimuw.edu.pl:~/public_html/books/transducer/}"
URL="${PUBLISH_URL:-https://www.mimuw.edu.pl/~bojan/books/transducer/}"
# The server refuses curl's own user-agent on every URL, including files that
# are perfectly fine, so the check at the end has to introduce itself as a
# browser or it will report a site that is entirely broken.
UA="Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/151 Safari/537.36"

DRY="" BUILD=1
for arg in "$@"; do
  case "$arg" in
    -n|--dry-run) DRY=1 ;;
    --no-build)   BUILD="" ;;
    *) echo "usage: $0 [-n] [--no-build]" >&2; exit 2 ;;
  esac
done

# ── 1. what is published should be what the sources say ─────────────────────
if [ -n "$BUILD" ]; then
  "$SITE/rebuild.sh"
else
  stale="$(find "$SITE/.." -maxdepth 1 \( -name '*.tex' -o -name '*.sty' -o -name '*.bib' \) \
             -newer "$SITE/dist/index.html" -print -quit 2>/dev/null || true)"
  [ -n "$stale" ] && echo "warning: $(basename "$stale") is newer than the build — publishing it anyway" >&2
fi

# ── 2. send it ──────────────────────────────────────────────────────────────
# --delete so the server mirrors dist/ and a renamed chapter does not linger
# there for ever; -z because 16 MB of base64 node lists compress about fourfold.
echo "== $([ -n "$DRY" ] && echo 'would send' || echo 'sending') to $DEST"
rsync -az --delete ${DRY:+--dry-run} --itemize-changes --stats "$SITE/dist/" "$DEST" \
  | grep -E '^(deleting|[<>ch.][fdLDS])|Number of files transferred|Total transferred file size' \
  | sed 's/^/   /' || true

[ -n "$DRY" ] && exit 0

# ── 3. the modes the web server needs ───────────────────────────────────────
# reflowtex provisions some fonts by copying them out of the TeX installation,
# mode and all, and macOS ships openrsync, which ignores --chmod without saying
# so. rebuild.sh fixes the local copies; this is the belt to that pair of braces,
# because the failure it prevents — every ligature in the book rendered as an
# empty box — looks like anything but a permissions problem.
host="${DEST%%:*}"; path="${DEST#*:}"
ssh -o BatchMode=yes "$host" "chmod -R a+rX $path" || true

# ── 4. see that it is actually there ────────────────────────────────────────
echo "== checking $URL"
fail=0
for probe in "" "01-introduction/" "search-index.js" "bibliography.js"; do
  code="$(curl -s -A "$UA" -o /dev/null -w '%{http_code}' "$URL$probe" || echo 000)"
  printf '   %-22s %s\n' "${probe:-/}" "$code"
  [ "$code" = 200 ] || fail=1
done
font="$(ls "$SITE/dist/fonts" | head -1)"
code="$(curl -s -A "$UA" -o /dev/null -w '%{http_code}' "$URL/fonts/$font" || echo 000)"
printf '   %-22s %s\n' "fonts/" "$code"
[ "$code" = 200 ] || fail=1

# The bibliography's PDFs arrive by a Hugo mount rather than by living in
# static/, so they are the one part of the site that can go missing without
# anything else looking wrong — and the symptom, an empty frame under a
# reference, is easy to read as the browser refusing to show a PDF. Asked for by
# HEAD: these run to tens of megabytes apiece.
pdf="$(ls "$SITE/dist/pdfs" 2>/dev/null | head -1)"
if [ -n "$pdf" ]; then
  code="$(curl -sI -A "$UA" -o /dev/null -w '%{http_code}' "$URL/pdfs/$pdf" || echo 000)"
  printf '   %-22s %s\n' "pdfs/" "$code"
  [ "$code" = 200 ] || fail=1
fi

if [ "$fail" = 0 ]; then
  echo "== published: $URL"
else
  echo "== something is not being served — see the codes above" >&2
  exit 1
fi
