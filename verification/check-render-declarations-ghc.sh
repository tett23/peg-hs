#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderDeclarationsGHC.olean" RenderDeclarationsGHC.lean) \
  > "$scratch/RenderDeclarationsGHC.log"

cat > "$scratch/RenderDeclarationsSource.expected" <<'SOURCE'
          , entryName k <> " :: " <> envParamType <> "PegRt.Text -> PegPrelude.Either PegRt.ParseError (" <> resultType n <> ")"
          , entryName k <> envArg <> " peg'input ="
    [ ruleVar (ruleName r) <> " :: " <> T.concat ["(" <> fragmentEnv env (paramType p) <> ") -> " | p <- ruleParams r]
    , ruleVar (ruleName r) <> T.concat [" " <> paramName p | p <- ruleParams r] <> " ="
SOURCE
sed -n '/^    entryDecls =/,/^    syntaxEntryDecls/p' packages/peg-codegen/src/Peg/Codegen.hs |
  grep -E '^          , entryName k <>|^    \[ ruleVar|^    , ruleVar' \
  > "$scratch/RenderDeclarationsSource.actual.entry"
sed -n '/^ruleDecl env r =/,/^  where/p' packages/peg-codegen/src/Peg/Codegen.hs |
  grep -E '^    \[ ruleVar|^    , ruleVar' \
  > "$scratch/RenderDeclarationsSource.actual.rule"
cat "$scratch/RenderDeclarationsSource.actual.entry" \
  "$scratch/RenderDeclarationsSource.actual.rule" \
  > "$scratch/RenderDeclarationsSource.actual"
diff -u "$scratch/RenderDeclarationsSource.expected" \
  "$scratch/RenderDeclarationsSource.actual"

grep -q 'reduce (rule 496)' "$scratch/Peg.trace"
grep -q 'reduce (rule 485)' "$scratch/Peg.trace"
grep -q 'reduce (rule 491)' "$scratch/Peg.trace"
grep -q 'reduce (rule 486)' "$scratch/Peg.trace"

sed 's/productions 496 =/productions 497 =/' \
  verification/RenderDeclarationsGHC.lean \
  > "$scratch/RenderDeclarationsGHCInvalid.lean"
if (cd verification && lean -DwarningAsError=true \
  "$scratch/RenderDeclarationsGHCInvalid.lean") \
  > "$scratch/RenderDeclarationsGHCInvalid.log" 2>&1; then
  echo 'Lean accepted a changed signature production' >&2
  exit 1
fi
grep -q 'error:' "$scratch/RenderDeclarationsGHCInvalid.log"
printf 'Declarations: 1 Lean module, 4 traced reductions, 1 rejected production mutation.\n'
