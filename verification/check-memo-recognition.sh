#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
if [ -n "${MEMO_PROOF_DIR:-}" ]; then
  work=$MEMO_PROOF_DIR
else
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT HUP INT TERM
fi

# The model is tied to the runtime by check-runtime-core.sh:
# ExtractRuntimeCore.hs translates mergeFailure, saveErrors, evalBody,
# newErrors, appendSlice, replay, logUndo, memo, memoArg, nomemo and
# defaultConfig from Peg.Runtime.Internal, and RuntimeCoreProof.lean proves
# that the translated memo and memoArg satisfy memoStep below.
cd verification
LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}" lean -DwarningAsError=true -o "$work/MemoRecognition.olean" MemoRecognition.lean
LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}" lean -DwarningAsError=true MemoRecognitionTests.lean
echo 'Checked the memo recognition model and 9 Lean boundary cases.'
