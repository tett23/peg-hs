#!/bin/sh
set -eu

cd "$(dirname "$0")"
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
[ -f "$LEAN_PATH/GHCGrammar.olean" ] || { echo 'GHCGrammar.olean is missing' >&2; exit 1; }
[ -f "$LEAN_PATH/RenderExpression.olean" ] || { echo 'RenderExpression.olean is missing' >&2; exit 1; }

lean -DwarningAsError=true -o "$scratch/RenderExpressionGHC.olean" RenderExpressionGHC.lean \
  > "$scratch/RenderExpressionGHC.log"
if grep -Eq 'sorryAx|^error:' "$scratch/RenderExpressionGHC.log"; then
  cat "$scratch/RenderExpressionGHC.log" >&2
  exit 1
fi

# A changed production number must break the fixed GHC grammar equality.
sed 's/(id := 533) (by decide)/(id := 534) (by decide)/' RenderExpressionGHC.lean \
  > "$scratch/RenderExpressionGHCInvalid.lean"
if lean -DwarningAsError=true "$scratch/RenderExpressionGHCInvalid.lean" \
    > "$scratch/RenderExpressionGHCInvalid.log" 2>&1; then
  echo 'Lean accepted a changed fexp application production' >&2
  exit 1
fi
grep -Eq 'error: Tactic `decide` failed|error: Tactic `decide` proved that' \
  "$scratch/RenderExpressionGHCInvalid.log" || {
  cat "$scratch/RenderExpressionGHCInvalid.log" >&2
  exit 1
}
printf 'GHC CFG expression composition: 11 theorems, 1 rejected production mutation.\n'
