#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderDeclarationsGHC.olean" RenderDeclarationsGHC.lean) \
  > "$scratch/RenderDeclarationsGHC.log"
if grep -q 'sorryAx' "$scratch/RenderDeclarationsGHC.log"; then
  cat "$scratch/RenderDeclarationsGHC.log" >&2
  exit 1
fi

cat > "$scratch/RenderDeclarationsSource.expected" <<'SOURCE'
    valueOf = if syntax then "PegPrelude.fmap PegPrelude.fst " else ""
    wrapValue e = if syntax then valueOf <> "(" <> e <> ")" else e
    hasEnv = isJust (grammarEnv g)
    fstName = if importsPrelude g then "PegPrelude.fst" else "Prelude.fst"
    envType = maybe "()" (fragment src marker) (grammarEnv g)
    resultType n = maybe "()" (ruleTypeFragment env) (M.lookup n (envRules env))
    envArg = if hasEnv then " peg'env" else ""
    envParamType = if hasEnv then "(" <> envType <> ") -> " else ""
    entryDecls =
      concat
        [ [ "-- | Parse the whole input with the rule @" <> n <> "@."
          , entryName k <> " :: " <> envParamType <> "PegRt.Text -> PegPrelude.Either PegRt.ParseError (" <> resultType n <> ")"
          , entryName k <> envArg <> " peg'input ="
          , "  " <> wrapValue (fstName <> " (PegRt.runParser peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " peg'input)")
          , ""
          ]
        | (k, n) <- entries
        , keep (entryName k)
        ]
    syntaxEntryDecls
      | syntax =
          concat
            [ [ "-- | Parse the whole input with the rule @" <> n <> "@ and return its lossless syntax tree."
              , "parseSyntax" <> maybe "" id k <> " :: " <> envParamType <> "PegRt.Text -> PegPrelude.Either PegRt.ParseError PegRt.SyntaxNode"
              , "parseSyntax" <> maybe "" id k <> envArg <> " peg'input ="
              , "  PegPrelude.fmap (\\peg'r -> PegRt.syntaxRoot peg'input " <> kindVar n <> " (PegPrelude.snd peg'r)) (" <> fstName <> " (PegRt.runParser peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " peg'input))"
              , ""
              ]
            | (k, n) <- entries
            , keep ("parseSyntax" <> maybe "" id k)
            ]
      | otherwise = []
    [ ruleVar (ruleName r) <> " :: " <> T.concat ["(" <> fragmentEnv env (paramType p) <> ") -> " | p <- ruleParams r]
    , ruleVar (ruleName r) <> T.concat [" " <> paramName p | p <- ruleParams r] <> " ="
SOURCE
sed -n '/^    valueOf =/,/^    hasEnv =/p
        /^    fstName =/,/^    resultType n =/p
        /^    envArg =/,/^    recoverEntryDecls/{ /^    recoverEntryDecls/!p; }' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderDeclarationsSource.actual.entry"
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
