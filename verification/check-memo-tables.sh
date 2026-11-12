#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
verification/check-memo-recognition.sh
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/MemoRecognition.olean" verification/MemoRecognition.lean
LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/MemoTrace.olean" verification/MemoTrace.lean
LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/MemoTables.olean" verification/MemoTables.lean
LEAN_PATH="$work" lean -DwarningAsError=true verification/MemoTablesTests.lean
echo 'Checked 6 memo table boundary cases and 2 trace-to-table invariant theorems.'
