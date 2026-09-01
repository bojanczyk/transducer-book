#!/bin/bash
# Quick single-file check: elaborate a Lean file of the project against Mathlib and the
# oleans already produced by `lake build`, without going through lake.  Unlike `qbuild.sh`
# it does not write an olean, so a scratch directory cannot shadow the real build output.
# Usage: bash tools/qcheck.sh RequestProject/Exercises/KrohnRhodes.lean
set -e
cd "$(dirname "$0")/.."
LP=$(ls -d .lake/packages/*/.lake/build/lib/lean | tr '\n' ':')".lake/build/lib/lean"
LEAN_PATH=$LP lean "$1"
