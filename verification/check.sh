#!/bin/sh
# Run from any directory. The Lean modules are compiled into a fresh directory.
set -eu

cd "$(dirname "$0")"
toolchain=$(cat lean-toolchain)
version=$(lean --version)
case "$version" in
  "Lean (version ${toolchain#leanprover/lean4:v},"*) ;;
  *) echo "Expected $toolchain; found $version" >&2; exit 1 ;;
esac
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
export LEAN_PATH="$work"

for module in Guard Parsing Header Lexical Nullable Reachable Literal Signatures File Consumption Pipeline Pragmas RenderExpression RuleRejection RuleRejectionRefs RuleRejectionRepeat RuleRejectionNullable Whitespace TemplateQueue; do
  lean -DwarningAsError=true -o "$work/$module.olean" "$module.lean"
done
lean --run Boundary.lean > "$work/boundary-expected"
cd ..
verification/check-guard.sh
verification/check-header.sh
verification/check-lexical.sh
verification/check-whitespace.sh
verification/check-template-queue.sh "$work"
verification/check-nullable.sh "$work"
verification/check-reachable.sh
verification/check-literal.sh "$work"
verification/check-pragmas.sh "$work"
verification/check-render-expression.sh "$work"
verification/check-no-record.sh
verification/check-pipeline.sh
verification/check-rule-rejection.sh
verification/check-rule-rejection-nullable.sh

extract_file() {
  "${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar verification/ExtractFile.hs "$@"
}
extract_file packages/peg-grammar/grammar/Peg.hpeg packages/peg-grammar/grammar/PegSyntax.hpeg > "$work/FileTrees.lean"
(cd verification && lean -DwarningAsError=true -R "$work" -o "$work/FileTrees.olean" "$work/FileTrees.lean" &&
  lean -DwarningAsError=true CheckEmpty.lean && lean -DwarningAsError=true Audit.lean)

# Each edited hpeg must still parse and translate. Only the Lean certificate fails.
reject_mutation() {
  grammar=$1
  edit=$2
  expected=$3
  sed "$edit" "packages/peg-grammar/grammar/$grammar.hpeg" > "$work/Mutant.hpeg"
  extract_file "$work/Mutant.hpeg" > "$work/Mutant.lean"
  if (cd verification && lean "$work/Mutant.lean") > "$work/mutant.log" 2>&1; then
    echo "invariant1: Lean accepted the mutation $edit" >&2
    exit 1
  fi
  grep -Fq "$expected" "$work/mutant.log" || { cat "$work/mutant.log" >&2; exit 1; }
}
reject_mutation Peg 's/^File <- Ws TopItem\* (!\.) \^top$/File <- Ws TopItem*/' 'fileExpr ws item'
reject_mutation Peg 's/^Verbatim <-.*/Verbatim <- Here/' 'run (ruleTopItem rest) []'
reject_mutation PegSyntax 's/^TopItem <- \&\. /TopItem <- /' 'run (ruleTopItem rest) []'
reject_mutation Peg 's/^Ws <-.*/Ws <- ./' 'run (ruleWs rest) []'
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar \
  verification/ExtractSignatures.hs \
  packages/peg-grammar/grammar/Peg.hpeg \
  packages/peg-grammar/grammar/PegSyntax.hpeg \
  packages/peg-codegen/test/fixtures/Templates.hpeg > "$work/ExtractedSignatures.lean"
(cd verification && lean -DwarningAsError=true "$work/ExtractedSignatures.lean")
cp "$work/ExtractedSignatures.lean" "$work/InvalidSignatures.lean"
cat >> "$work/InvalidSignatures.lean" <<'SOURCE'
namespace Grammar1
theorem invariant2_missing_reference_must_fail :
    WellFormed definitions (references ++ [(0, 0)]) := by
  exact (invariant2_signatures _ _).mp (by decide)
end Grammar1
SOURCE
if (cd verification && lean -DwarningAsError=true "$work/InvalidSignatures.lean") > "$work/invalid-signatures.log" 2>&1; then
  echo 'invariant2: Lean unexpectedly accepted an undefined rule reference' >&2
  exit 1
fi
[ "$(grep -c 'error:' "$work/invalid-signatures.log")" -eq 1 ] &&
grep -Fq 'Tactic `decide` proved that the proposition' "$work/invalid-signatures.log" &&
grep -Fq 'accepts definitions (references ++ [(0, 0)]) = true' "$work/invalid-signatures.log" &&
grep -Fq 'is false' "$work/invalid-signatures.log" || {
  cat "$work/invalid-signatures.log" >&2
  exit 1
}
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-codegen -package=peg-grammar verification/Boundary.hs > "$work/boundary-actual"
diff -u "$work/boundary-expected" "$work/boundary-actual"
verification/check-core.sh "$work"

# Regenerate both parsers from the actual grammar files, then ask GHC to read
# the exact emitted modules, including their user-supplied Haskell.
cabal=${CABAL:-cabal}
peg=$("$cabal" list-bin exe:peg-hs)
for grammar in Peg PegSyntax; do
  "$peg" gen "packages/peg-grammar/grammar/$grammar.hpeg" -o "$work/$grammar.hs"
  "$cabal" exec -- ghc-9.10.3 -fno-code -fforce-recomp -package peg-runtime \
    -package peg-grammar -outputdir "$work" "$work/$grammar.hs"
done
printf '%s\n' '%module Broken' 'S :: ()' "S <- 'a' { let }" > "$work/Broken.hpeg"
"$peg" gen "$work/Broken.hpeg" -o "$work/Broken.hs"
if "$cabal" exec -- ghc-9.10.3 -fno-code -package peg-runtime -outputdir "$work" \
  "$work/Broken.hs" > "$work/ghc-error" 2>&1; then
  echo 'invariant3: GHC unexpectedly accepted an incomplete expression' >&2
  exit 1
fi
grep -q 'parse error' "$work/ghc-error" || { cat "$work/ghc-error" >&2; exit 1; }

verification/check-render-expression-boundary.sh "$work"
verification/check-ghc-parser-trace.sh "$work"
verification/check-render-expression-lexer.sh "$work"
verification/check-render-module-names.sh "$work/module-names"
verification/check-ghc-derivations.sh "$work"
