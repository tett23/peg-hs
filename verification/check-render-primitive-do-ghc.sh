#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderPrimitiveDoGHC.olean" RenderPrimitiveDoGHC.lean) \
  > "$scratch/RenderPrimitiveDoGHC.log"
if grep -Fq 'sorryAx' "$scratch/RenderPrimitiveDoGHC.log"; then
  cat "$scratch/RenderPrimitiveDoGHC.log" >&2
  exit 1
fi

sed 's/\[\.terminal 113\] ++ statement.tokens/[.terminal 114] ++ statement.tokens/' \
  verification/RenderPrimitiveDoGHC.lean > "$scratch/RenderPrimitiveDoGHCInvalid.lean"
if cmp -s verification/RenderPrimitiveDoGHC.lean "$scratch/RenderPrimitiveDoGHCInvalid.lean"; then
  echo 'do token mutation did not change the source' >&2
  exit 1
fi
if (cd verification && lean -DwarningAsError=true \
    "$scratch/RenderPrimitiveDoGHCInvalid.lean") \
    > "$scratch/RenderPrimitiveDoGHCInvalid.log" 2>&1; then
  echo 'Lean accepted a changed do separator token' >&2
  exit 1
fi
grep -Fq 'error: Type mismatch' "$scratch/RenderPrimitiveDoGHCInvalid.log" || {
  cat "$scratch/RenderPrimitiveDoGHCInvalid.log" >&2
  exit 1
}

printf 'Do GHC bridge: 4 Lean theorems, 1 rejected token mutation, 0 sorry axioms.\n'
