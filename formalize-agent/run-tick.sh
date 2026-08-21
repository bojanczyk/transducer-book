#!/bin/sh
# One tick of the formalisation driver.
#
# This is what launchd runs.  It exists because the interpreter that has the
# aristotlelib package lives in a pipx venv whose path contains a space, which
# a #! line cannot express portably.
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)

# Find an interpreter that can import aristotlelib.
PY=""
for candidate in \
    "$HOME/Library/Application Support/pipx/venvs/aristotlelib/bin/python" \
    "$HOME/.local/pipx/venvs/aristotlelib/bin/python" \
    "$(command -v python3 || true)"
do
    if [ -x "$candidate" ] && "$candidate" -c 'import aristotlelib' 2>/dev/null; then
        PY="$candidate"
        break
    fi
done

if [ -z "$PY" ]; then
    echo "[$(date -u '+%Y-%m-%d %H:%M:%SZ')] no python with aristotlelib found" \
        >> "$HERE/logs/driver.log"
    exit 1
fi

exec "$PY" "$HERE/driver.py" "${1:-tick}"
