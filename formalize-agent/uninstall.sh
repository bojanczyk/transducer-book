#!/bin/sh
# Stop the scheduled driver. Does not touch the Lean sources or the state file,
# and does not cancel a task that is already running on Aristotle's servers.
set -eu

LABEL=com.bojanczyk.transducer-formalize
launchctl bootout "gui/$(id -u)/$LABEL" 2>/dev/null || true
rm -f "$HOME/Library/LaunchAgents/$LABEL.plist"
echo "removed $LABEL"
echo "the queue state is untouched; reinstall with ./install.sh to carry on."
