#!/bin/sh
# Install (or reinstall) the launchd job that ticks the formalisation driver.
set -eu

HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
LABEL=com.bojanczyk.transducer-formalize
PLIST="$HOME/Library/LaunchAgents/$LABEL.plist"

mkdir -p "$HOME/Library/LaunchAgents" "$HERE/logs/summaries"
chmod +x "$HERE/run-tick.sh" "$HERE/driver.py"
cp "$HERE/$LABEL.plist" "$PLIST"

# bootout is expected to fail when the job is not loaded yet
launchctl bootout "gui/$(id -u)/$LABEL" 2>/dev/null || true
launchctl bootstrap "gui/$(id -u)" "$PLIST"

echo "installed $LABEL"
echo "it ticks every 15 minutes, and once at login."
echo
launchctl print "gui/$(id -u)/$LABEL" 2>/dev/null | grep -E '^\s+(state|last exit code|runs) ' || true
