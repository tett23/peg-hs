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
    noTraditionalRecordSyntax =
      any (elem "NoTraditionalRecordSyntax" . map T.strip . T.splitOn "," . unLoc) (grammarLanguages g)
    debugConfig
      | noTraditionalRecordSyntax = "(peg'withTabstop (PegRt.cfgTabstop peg'config) peg'cfg)"
      | otherwise = "peg'cfg {PegRt.cfgTabstop = PegRt.cfgTabstop peg'config}"
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
    recoverEntryDecls
      | recovering =
          concat
            [ ( if keep ("parseRecover" <> maybe "" id k)
                  then
                    [ "-- | Parse the whole input with the rule @" <> n <> "@, recovering from labelled failures."
                    , "-- The value is 'PegPrelude.Nothing' only if the rule could not be recovered."
                    , "parseRecover" <> maybe "" id k <> " :: " <> envParamType <> "PegRt.Text -> (PegPrelude.Maybe (" <> resultType n <> "), [PegRt.SyntaxError])"
                    , "parseRecover" <> maybe "" id k <> envArg <> " peg'input ="
                    , "  let (peg'v, peg'e, _) = PegRt.runParserRecover peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " peg'input"
                    , "   in (" <> valueOf <> "peg'v, peg'e)"
                    , ""
                    ]
                  else []
              )
                ++ ( if syntax && keep ("parseSyntaxRecover" <> maybe "" id k)
                       then
                         [ "-- | The lossless syntax tree of the whole input, recovering from labelled failures."
                         , "-- Always returns a tree; unrecovered input becomes error nodes."
                         , "parseSyntaxRecover" <> maybe "" id k <> " :: " <> envParamType <> "PegRt.Text -> (PegRt.SyntaxNode, [PegRt.SyntaxError])"
                         , "parseSyntaxRecover" <> maybe "" id k <> envArg <> " peg'input ="
                         , "  let (peg'n, peg'e, _) = PegRt.runSyntaxRecover peg'config (peg'newStore" <> envArg <> ") " <> ruleVar n <> " " <> kindVar n <> " peg'input"
                         , "   in (peg'n, peg'e)"
                         , ""
                         ]
                       else []
                   )
            | (k, n) <- entries
            ]
            ++ ( if optDebugEntry opts
                   then
                     [ "-- | Like 'peg'parseWith', recovering. Only meant for testing the generator."
                     , "peg'parseRecoverWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegPrelude.Maybe (" <> resultType start <> "), [PegRt.SyntaxError], PegRt.Stats)"
                     , "peg'parseRecoverWith peg'cfg" <> envArg <> " peg'input ="
                     , "  let (peg'v, peg'e, peg's) = PegRt.runParserRecover " <> debugConfig <> " (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"
                     , "   in (" <> valueOf <> "peg'v, peg'e, peg's)"
                     , ""
                     ]
                       ++ ( if syntax
                              then
                                [ "-- | Like 'peg'parseSyntaxWith', recovering. Only meant for testing the generator."
                                , "peg'parseSyntaxRecoverWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegRt.SyntaxNode, [PegRt.SyntaxError], PegRt.Stats)"
                                , "peg'parseSyntaxRecoverWith peg'cfg" <> envArg <> " peg'input ="
                                , "  PegRt.runSyntaxRecover " <> debugConfig <> " (peg'newStore" <> envArg <> ") " <> ruleVar start <> " " <> kindVar start <> " peg'input"
                                , ""
                                ]
                              else []
                          )
                   else []
               )
      | otherwise = []
    debugDecls
      | optDebugEntry opts =
          [ "-- | Run the start rule with a runtime configuration and return statistics."
          , "-- Only meant for testing the generator."
          , "peg'parseWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegPrelude.Either PegRt.ParseError (" <> resultType start <> "), PegRt.Stats)"
          , "peg'parseWith peg'cfg" <> envArg <> " peg'input ="
          ]
            ++ ( if syntax
                   then
                     [ "  let (peg'r, peg's) = PegRt.runParser " <> debugConfig <> " (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"
                     , "   in (" <> valueOf <> "peg'r, peg's)"
                     ]
                   else ["  PegRt.runParser " <> debugConfig <> " (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"]
               )
            ++ [""]
            ++ ( if syntax
                   then
                     [ "-- | Like 'peg'parseWith', for the syntax tree. Only meant for testing the generator."
                     , "peg'parseSyntaxWith :: PegRt.Config -> " <> envParamType <> "PegRt.Text -> (PegPrelude.Either PegRt.ParseError PegRt.SyntaxNode, PegRt.Stats)"
                     , "peg'parseSyntaxWith peg'cfg" <> envArg <> " peg'input ="
                     , "  let (peg'r, peg's) = PegRt.runParser " <> debugConfig <> " (peg'newStore" <> envArg <> ") " <> ruleVar start <> " peg'input"
                     , "   in (PegPrelude.fmap (\\peg'x -> PegRt.syntaxRoot peg'input " <> kindVar start <> " (PegPrelude.snd peg'x)) peg'r, peg's)"
                     , ""
                     ]
                   else []
               )
      | otherwise = []
    [ ruleVar (ruleName r) <> " :: " <> T.concat ["(" <> fragmentEnv env (paramType p) <> ") -> " | p <- ruleParams r]
    , ruleVar (ruleName r) <> T.concat [" " <> paramName p | p <- ruleParams r] <> " ="
SOURCE
sed -n '/^    valueOf =/,/^      | otherwise = "peg.cfg {/p
        /^    fstName =/,/^    resultType n =/p
        /^    envArg =/,/^    configDecl =/{ /^    configDecl =/!p; }' \
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
