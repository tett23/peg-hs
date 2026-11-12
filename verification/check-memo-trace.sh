#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
if [ -n "${MEMO_PROOF_DIR:-}" ]; then
  work=$MEMO_PROOF_DIR
else
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT HUP INT TERM
fi
MEMO_PROOF_DIR="$work" verification/check-memo-recognition.sh
cd verification
LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/MemoTrace.olean" MemoTrace.lean
LEAN_PATH="$work" lean -DwarningAsError=true MemoTraceTests.lean
echo 'Checked 6 memo trace boundary cases and the source-locked cache transitions.'
