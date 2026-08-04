#!/usr/bin/env bash
# Upload the compiled transducer book PDF to the course website on duch.
# Usage:  ./upload.sh [tag]
#   tag — optional name suffix; defaults to today's date (YYYY-MM-DD).
#         The remote filename is transducer-book-<tag>.pdf.

set -euo pipefail

LOCAL_PDF="$HOME/Documents/ksiazki/transducer-book/main.pdf"
REMOTE_HOST="bojan@duch.mimuw.edu.pl"
REMOTE_DIR="~/public_html/papers/transducer-book/"

TAG="${1:-$(date +%Y-%m-%d)}"
REMOTE_NAME="transducer-book-${TAG}.pdf"
PUBLIC_URL="https://mimuw.edu.pl/~bojan/papers/transducer-book/${REMOTE_NAME}"

if [[ ! -f "$LOCAL_PDF" ]]; then
  echo "error: local PDF not found at $LOCAL_PDF" >&2
  echo "       (build it with latexmk first?)" >&2
  exit 1
fi

echo "Uploading $LOCAL_PDF"
echo "        → ${REMOTE_HOST}:${REMOTE_DIR}/${REMOTE_NAME}"
scp "$LOCAL_PDF" "${REMOTE_HOST}:${REMOTE_DIR}/${REMOTE_NAME}"

echo
echo "Done. URL:"
echo "  ${PUBLIC_URL}"
