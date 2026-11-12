#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
if [ -n "${MEMO_PROOF_DIR:-}" ]; then
  work=$MEMO_PROOF_DIR
else
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT HUP INT TERM
fi
MEMO_PROOF_DIR="$work" verification/check-memo-trace.sh
cd verification
LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/MemoTables.olean" MemoTables.lean
LEAN_PATH="$work" lean -DwarningAsError=true MemoTablesTests.lean
echo 'Checked 6 memo table boundary cases and 2 trace-to-table invariant theorems.'
