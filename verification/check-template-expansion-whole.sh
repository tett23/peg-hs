#!/bin/sh
# Tie TemplateExpansionWhole.lean to Peg.Grammar.Templates: the source of
# every function the model follows is fixed, and the model must give the same
# result as the real expandTemplates on the grammars of the probe.
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Templates.hs}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# substituteAlt and the constructors of Expr are fixed by this script.
verification/check-template-substitution.sh "$source_file" packages/peg-grammar/src/Peg/Grammar.hs > /dev/null

# expandTemplates to drain, then exprSize to the end of the module. Only
# instanceType and identifierSplit, which make the types of the instances,
# are left out: the model takes the type of an instance as a parameter.
{
  sed -n '/^expandTemplates ::/,/^    maxSize = 10000$/p' "$source_file"
  sed -n '/^exprSize ::/,$p' "$source_file"
} > "$work/source"
diff -u verification/template-expansion-whole.source "$work/source"

"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -Wall -Werror -package=peg-grammar \
  verification/TemplateExpansionWholeProbe.hs expect > "$work/haskell-output"
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -Wall -Werror -package=peg-grammar \
  verification/TemplateExpansionWholeProbe.hs lean > "$work/TemplateExpansionWholeData.lean"

(cd verification &&
  for module in TemplateQueue TemplateLocation TemplateSubstitution TemplateExpansion TemplateExpansionFresh TemplateExpansionWhole; do
    LEAN_PATH="$work" lean -DwarningAsError=true -o "$work/$module.olean" "$module.lean" > /dev/null
  done &&
  LEAN_PATH="$work" lean -DwarningAsError=true -R "$work" -o "$work/TemplateExpansionWholeData.olean" \
    "$work/TemplateExpansionWholeData.lean" > /dev/null &&
  LEAN_PATH="$work" lean --run TemplateExpansionWholeProbe.lean > "$work/lean-output")

diff -u "$work/haskell-output" "$work/lean-output"
printf 'Compared %s grammars expanded by the model and by expandTemplates.\n' \
  "$(grep -c '^case ' "$work/lean-output")"
