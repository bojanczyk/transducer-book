#!/bin/sh
# Foreground ticker: run this in a Terminal window and leave it open.
#
# Use it when the launchd job cannot run because macOS has not granted a
# background process access to ~/Documents (see README, "macOS permissions").
# A process started from Terminal inherits Terminal's own access, so this
# always works -- but it stops when you close the window or reboot.
#
#   ./tick-loop.sh          # tick every 15 minutes
#   ./tick-loop.sh 300      # tick every 5 minutes
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
INTERVAL=${1:-900}

echo "ticking every ${INTERVAL}s — Ctrl-C to stop (Aristotle keeps working either way)"
while :; do
    "$HERE/run-tick.sh" tick || echo "tick failed; will try again"
    sleep "$INTERVAL"
done
