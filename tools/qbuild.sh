#!/bin/bash
# Quick single-module check: compile a Lean file of the project against Mathlib and the
# modules already compiled into $QB (a scratch build directory), without going through lake.
# Usage: tools/qbuild.sh RequestProject/PartD/ForSem.lean
set -e
cd "$(dirname "$0")/.."
QB=${QB:-/tmp/lbuild}
mkdir -p "$QB"
LP=$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':')"$QB:.lake/build/lib/lean"
mod=${1%.lean}
out="$QB/${mod}.olean"
mkdir -p "$(dirname "$out")"
LEAN_PATH=$LP lean -o "$out" "$1"
