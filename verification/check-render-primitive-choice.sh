#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderPrimitiveChoice.olean" RenderPrimitiveChoice.lean) \
  > "$scratch/RenderPrimitiveChoice.log"
if grep -Fq 'sorryAx' "$scratch/RenderPrimitiveChoice.log"; then
  cat "$scratch/RenderPrimitiveChoice.log" >&2
  exit 1
fi

cat > "$scratch/RenderPrimitiveChoice.expected" <<'SOURCE'
    , "  " <> memoCall <> "\n    (" <> expectWrap <> treeWrap <> "PegRt.choice\n      [ " <> T.intercalate "\n      , " alts <> "\n      ])" <> treeClose <> expectClose
SOURCE
sed -n '/^    , "  " <> memoCall /p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderPrimitiveChoice.actual"
diff -u "$scratch/RenderPrimitiveChoice.expected" "$scratch/RenderPrimitiveChoice.actual"

sed 's/rest.map Alternative.tokens).foldl RenderExpressionGHC.commaAppend/rest.map Alternative.tokens).foldl RenderExpressionGHC.semicolonAppend/' \
  verification/RenderPrimitiveChoice.lean > "$scratch/RenderPrimitiveChoiceInvalid.lean"
if cmp -s verification/RenderPrimitiveChoice.lean "$scratch/RenderPrimitiveChoiceInvalid.lean"; then
  echo 'choice token mutation did not change the source' >&2
  exit 1
fi
if (cd verification && lean -DwarningAsError=true \
    "$scratch/RenderPrimitiveChoiceInvalid.lean") \
    > "$scratch/RenderPrimitiveChoiceInvalid.log" 2>&1; then
  echo 'Lean accepted a changed choice separator token' >&2
  exit 1
fi
grep -Fq 'error: Type mismatch' "$scratch/RenderPrimitiveChoiceInvalid.log" || {
  cat "$scratch/RenderPrimitiveChoiceInvalid.log" >&2
  exit 1
}

printf 'Rule choice renderer: 3 Lean theorems, 1 exact source check, 1 rejected mutation, 0 sorry axioms.\n'
