#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderDeclarationBinders.olean" RenderDeclarationBinders.lean) \
  > "$scratch/RenderDeclarationBinders.log"
if grep -q 'sorryAx' "$scratch/RenderDeclarationBinders.log"; then
  cat "$scratch/RenderDeclarationBinders.log" >&2
  exit 1
fi

source=packages/peg-grammar/src/Peg/Grammar/Assemble.hs
sed -n '/^toParam ::/,/^-- | The body/p' "$source" |
  grep -Fq ', isValidIdent name ->'
sed -n '/^    binderKeyword name =/,/^    known =/p' "$source" |
  grep -Fq 'extensionKeyword recursiveDoEnabled arrowsEnabled name'
sed -n '/^extensionKeyword recursiveDoEnabled arrowsEnabled name =/,/^$/p' "$source" |
  grep -Fq 'recursiveDoEnabled && name `elem` ["mdo", "rec"]'
sed -n '/^    unqualifiedName name =/,/^    isTypeName/p' "$source" |
  head -n 2 > "$scratch/UnqualifiedExportName.actual"
cat > "$scratch/UnqualifiedExportName.expected" <<'SOURCE'
    unqualifiedName name = isValidIdent name && name `notElem` reservedWords
      && not (extensionKeyword recursiveDoEnabled arrowsEnabled name)
SOURCE
diff -u "$scratch/UnqualifiedExportName.expected" "$scratch/UnqualifiedExportName.actual"
sed -n '/^    errors =/,/^-- | Whether a text is a path/p' "$source" |
  grep -Fq ', binderKeyword name'
sed -n '/^    errors =/,/^-- | Whether a text is a path/p' "$source" |
  grep -Fq ', binderKeyword (paramName p)'
sed -n '/^reservedWords =/,/^  ]/p' packages/peg-grammar/src/Peg/Grammar.hs |
  grep -Fq '"case"'
sed -n '/^    keyParamType p/,/^    storeDecl/p' packages/peg-codegen/src/Peg/Codegen.hs |
  grep -Fq 'paramName p == "_" = "()"'
sed -n '/^    keyParam p/,/^    alts/p' packages/peg-codegen/src/Peg/Codegen.hs |
  grep -Fq 'paramName p == "_" = "()"'

printf 'Binder names: 12 Lean theorems, 2 validator sites, 2 memo-key sites, 1 reserved-word membership.\n'
