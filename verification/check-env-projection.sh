#!/bin/sh
set -eu

work=${1:?pass the shared Lean object directory}
cd "$(dirname "$0")"
for module in EnvProjection EnvProjectionPredicate MemoKeyTransfer; do
  LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/$module.olean" "$module.lean"
done
LEAN_PATH="$work" lean -DwarningAsError=true EnvProjectionTests.lean
echo 'Checked 5 Env projection boundary cases and 3 memo key-transfer modules.'
