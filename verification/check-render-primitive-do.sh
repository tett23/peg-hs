#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderPrimitiveDo.olean" RenderPrimitiveDo.lean) \
  > "$scratch/RenderPrimitiveDo.log"
if grep -Fq 'sorryAx' "$scratch/RenderPrimitiveDo.log"; then
  cat "$scratch/RenderPrimitiveDo.log" >&2
  exit 1
fi

cat > "$scratch/RenderPrimitiveDo.expected" <<'SOURCE'
doBlock :: [Text] -> Text
doBlock stmts = "do { " <> T.concat (intersperse "\n          ; " stmts) <> "\n          }"
SOURCE
sed -n '/^doBlock ::/,/^doBlock stmts =/p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderPrimitiveDo.actual"
diff -u "$scratch/RenderPrimitiveDo.expected" "$scratch/RenderPrimitiveDo.actual"

sed 's/List.intersperse "\\n          ; " statements/List.intersperse "\\n          , " statements/' \
  verification/RenderPrimitiveDo.lean > "$scratch/RenderPrimitiveDoInvalid.lean"
if cmp -s verification/RenderPrimitiveDo.lean "$scratch/RenderPrimitiveDoInvalid.lean"; then
  echo 'do separator mutation did not change the source' >&2
  exit 1
fi
if (cd verification && lean -DwarningAsError=true \
    "$scratch/RenderPrimitiveDoInvalid.lean") \
    > "$scratch/RenderPrimitiveDoInvalid.log" 2>&1; then
  echo 'Lean accepted a changed do separator' >&2
  exit 1
fi
grep -Fq 'error: unsolved goals' "$scratch/RenderPrimitiveDoInvalid.log" || {
  cat "$scratch/RenderPrimitiveDoInvalid.log" >&2
  exit 1
}

printf 'Do renderer: 3 Lean theorems, 1 exact source check, 1 rejected mutation, 0 sorry axioms.\n'
