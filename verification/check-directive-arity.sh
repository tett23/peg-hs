#!/bin/sh
set -eu
cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
source=../packages/peg-grammar/src/Peg/Grammar/Assemble.hs
runghc-9.10.3 -Werror ExtractDirectiveArity.hs "$source" > "$work/TranslatedArity.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedArity.olean" "$work/TranslatedArity.lean"
lean -DwarningAsError=true -o "$work/DirectiveArityProof.olean" DirectiveArityProof.lean

# Make %module take no argument. The modified guard still translates, but its
# proof against the assembler model must fail at the changed flag condition.
changed="$work/changed-arity"
mkdir -p "$changed"
sed '/takes no argument/s/\["syntax", "library"\]/["syntax", "library", "module"]/' \
  "$source" > "$changed/Assemble.hs"
runghc-9.10.3 -Werror ExtractDirectiveArity.hs "$changed/Assemble.hs" > "$changed/TranslatedArity.lean"
lean -DwarningAsError=true -R "$changed" -o "$changed/TranslatedArity.olean" "$changed/TranslatedArity.lean"
if LEAN_PATH="$changed:$LEAN_PATH" lean -DwarningAsError=true DirectiveArityProof.lean > "$changed/result" 2>&1; then
  echo 'accepted %module in the list of directives taking no argument' >&2
  exit 1
fi
grep -Fq 'flags.contains name' "$changed/result" || { cat "$changed/result" >&2; exit 1; }
