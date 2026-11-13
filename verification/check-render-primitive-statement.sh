#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderPrimitiveStatement.olean" RenderPrimitiveStatement.lean) \
  > "$scratch/RenderPrimitiveStatement.log"
if grep -Fq 'sorryAx' "$scratch/RenderPrimitiveStatement.log"; then
  cat "$scratch/RenderPrimitiveStatement.log" >&2
  exit 1
fi

cat > "$scratch/RenderPrimitiveStatement.expected" <<'SOURCE'
      | omitsUnitAction (units env) rule items -> do
          stmts <- mapM (itemStmt env True) items
          pure (doBlock (envStmt ++ stmts ++ ["PegPrelude.pure ()"]))
SOURCE
sed -n '/^      | omitsUnitAction (units env) rule items -> do$/{N;N;p;}' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderPrimitiveStatement.actual"
diff -u "$scratch/RenderPrimitiveStatement.expected" "$scratch/RenderPrimitiveStatement.actual"

cat > "$scratch/RenderPrimitiveStatementItem.expected" <<'SOURCE'
itemStmt :: Env -> Bool -> Item -> Gen Text
itemStmt env honorBind i = do
  e <- exprCodeU env (valueUsed env honorBind i) (itemExpr i)
  pure $
    if hasValue (units env) (itemExpr i)
      then case itemBind i of
        Just n | honorBind -> n <> " <- " <> e
        _ -> "_ <- " <> e
      else e
SOURCE
sed -n '/^itemStmt ::/,/^      else e$/p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderPrimitiveStatementItem.actual"
diff -u "$scratch/RenderPrimitiveStatementItem.expected" \
  "$scratch/RenderPrimitiveStatementItem.actual"

grep -Fxq 'doReturn stmts value kids = doBlock (stmts ++ ["PegPrelude.pure (" <> value <> ", " <> kidsExpr kids <> ")"])' packages/peg-codegen/src/Peg/Codegen.hs

cat > "$scratch/SyntaxAction.expected" <<'SOURCE'
  let envStmt = ["_env <- PegRt.askStore peg'env" | isJust (grammarEnv (envGrammar env))]
      items = altItems a
  case altAction a of
    Just act -> do
      rs <- mapM (itemStmtS env True) items
      pure $
        doReturn
          (envStmt ++ ["peg'start <- PegRt.getOffset"] ++ map fst rs ++ ["_span <- PegRt.spanFrom peg'start"])
          ("(" <> fragmentEnv env act <> ")")
          (map snd rs)
SOURCE
sed -n '/^altCodeS env rule a = do$/,/^    Nothing$/{ /^altCodeS /d; /^    Nothing$/d; p; }' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/SyntaxAction.actual"
diff -u "$scratch/SyntaxAction.expected" "$scratch/SyntaxAction.actual"

cat > "$scratch/KidsExpr.expected" <<'SOURCE'
kidsExpr [] = "[]"
kidsExpr [k] = k
kidsExpr ks = "PegPrelude.concat [" <> T.intercalate ", " ks <> "]"
SOURCE
sed -n '/^kidsExpr \[\] =/,/^kidsExpr ks =/p' packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/KidsExpr.actual"
diff -u "$scratch/KidsExpr.expected" "$scratch/KidsExpr.actual"

cat > "$scratch/FreshNames.expected" <<'SOURCE'
fresh = Gen $ \n -> ("peg'v" <> showT n, n + 1)
freshK = Gen $ \n -> ("peg'k" <> showT n, n + 1)
SOURCE
sed -n '/^fresh = /p; /^freshK = /p' packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/FreshNames.actual"
diff -u "$scratch/FreshNames.expected" "$scratch/FreshNames.actual"
grep -Fxq 'newtype Gen a = Gen {runGen :: Natural -> (a, Natural)}' packages/peg-codegen/src/Peg/Codegen.hs
grep -Fxq "parenthesise t = if T.any (== ' ') t then \"(\" <> t <> \")\" else t" packages/peg-codegen/src/Peg/Codegen.hs

cat > "$scratch/RenderPrimitivePureSites.expected" <<'SOURCE'
          pure (doBlock (envStmt ++ stmts ++ ["PegPrelude.pure ()"]))
          pure (doBlock (envStmt ++ stmts ++ ["PegPrelude.pure " <> parenthesise (T.unwords (maybe (dataName d) conName (listToMaybe con) : vs))]))
          pure (doBlock (envStmt ++ stmts ++ ["PegPrelude.pure " <> result]))
          pure (doBlock (envStmt ++ stmts ++ ["PegPrelude.pure " <> result]))
SOURCE
sed -n '/^altCode ::/,/^-- Statements for a sequence/p' \
  packages/peg-codegen/src/Peg/Codegen.hs |
  grep -F 'pure (doBlock' > "$scratch/RenderPrimitivePureSites.actual"
diff -u "$scratch/RenderPrimitivePureSites.expected" \
  "$scratch/RenderPrimitivePureSites.actual"

[ -x "$scratch/trace-generated-module" ] || {
  echo 'GHC parser trace driver is missing' >&2
  exit 1
}
cat > "$scratch/RenderPrimitiveStatementProbe.hs" <<'SOURCE'
module LexProbe where
x = do { PegPrelude.pure () }
SOURCE
"$scratch/trace-generated-module" "$(ghc-9.10.3 --print-libdir)" \
  "$scratch/RenderPrimitiveStatementProbe.hs" \
  > "$scratch/RenderPrimitiveStatement.result" \
  2> "$scratch/RenderPrimitiveStatement.trace"
[ "$(cat "$scratch/RenderPrimitiveStatement.result")" = parsed-no-diagnostics ]
grep '^token: ' "$scratch/RenderPrimitiveStatement.trace" |
  sed 's/^token: //' > "$scratch/RenderPrimitiveStatement.tokens"
cat > "$scratch/RenderPrimitiveStatement.expected-tokens" <<'TOKENS'
ITmodule
ITconid "LexProbe"
ITwhere
ITvocurly
ITvarid "x"
ITequal
ITdo Nothing
ITocurly
ITqvarid ("PegPrelude","pure")
IToparen
ITcparen
ITccurly
ITsemi
ITeof
TOKENS
diff -u "$scratch/RenderPrimitiveStatement.expected-tokens" \
  "$scratch/RenderPrimitiveStatement.tokens"

cat > "$scratch/RenderPrimitiveBindingProbe.hs" <<'SOURCE'
module LexProbe where
x = do { foo <- PegRt.anyChar; _ <- PegRt.anyChar; PegPrelude.pure () }
SOURCE
"$scratch/trace-generated-module" "$(ghc-9.10.3 --print-libdir)" \
  "$scratch/RenderPrimitiveBindingProbe.hs" \
  > "$scratch/RenderPrimitiveBinding.result" \
  2> "$scratch/RenderPrimitiveBinding.trace"
[ "$(cat "$scratch/RenderPrimitiveBinding.result")" = parsed-no-diagnostics ]
grep '^token: ' "$scratch/RenderPrimitiveBinding.trace" |
  sed 's/^token: //' > "$scratch/RenderPrimitiveBinding.tokens"
cat > "$scratch/RenderPrimitiveBinding.expected-tokens" <<'TOKENS'
ITmodule
ITconid "LexProbe"
ITwhere
ITvocurly
ITvarid "x"
ITequal
ITdo Nothing
ITocurly
ITvarid "foo"
ITlarrow NormalSyntax
ITqvarid ("PegRt","anyChar")
ITsemi
ITunderscore
ITlarrow NormalSyntax
ITqvarid ("PegRt","anyChar")
ITsemi
ITqvarid ("PegPrelude","pure")
IToparen
ITcparen
ITccurly
ITsemi
ITeof
TOKENS
diff -u "$scratch/RenderPrimitiveBinding.expected-tokens" \
  "$scratch/RenderPrimitiveBinding.tokens"

# Exercise the actual renderer definitions with zero, one and multiple children.
cat > "$scratch/RenderReturnProbe.hs" <<'SOURCE'
{-# LANGUAGE OverloadedStrings #-}
import Data.List (intersperse)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
SOURCE
sed -n '/^doBlock ::/,/^doBlock stmts =/p; /^doReturn ::/,/^kidsExpr ks =/p' \
  packages/peg-codegen/src/Peg/Codegen.hs >> "$scratch/RenderReturnProbe.hs"
cat >> "$scratch/RenderReturnProbe.hs" <<'SOURCE'
main :: IO ()
main = TIO.putStrLn $ T.unlines
  ("module LexProbe where" : zipWith render ["x", "y", "z"]
    [[], ["peg'k0"], ["peg'k0", "peg'k1", "peg'k2"]])
  where render name kids = name <> " = " <> doReturn [] "peg'v0" kids
SOURCE
runghc "$scratch/RenderReturnProbe.hs" > "$scratch/RenderReturnOutput.hs"
"$scratch/trace-generated-module" "$(ghc-9.10.3 --print-libdir)" \
  "$scratch/RenderReturnOutput.hs" > "$scratch/RenderReturn.result" 2> "$scratch/RenderReturn.trace"
[ "$(cat "$scratch/RenderReturn.result")" = parsed-no-diagnostics ]
sed -n 's/^token: //p' "$scratch/RenderReturn.trace" > "$scratch/RenderReturn.tokens"
{
  printf '%s\n' ITmodule 'ITconid "LexProbe"' ITwhere ITvocurly
  for name in x y z; do
    printf '%s\n' "ITvarid \"$name\"" ITequal 'ITdo Nothing' ITocurly \
      'ITqvarid ("PegPrelude","pure")' IToparen "ITvarid \"peg'v0\"" ITcomma
    case $name in
      x) printf '%s\n' ITobrack ITcbrack ;;
      y) printf '%s\n' "ITvarid \"peg'k0\"" ;;
      z) printf '%s\n' 'ITqvarid ("PegPrelude","concat")' ITobrack \
           "ITvarid \"peg'k0\"" ITcomma "ITvarid \"peg'k1\"" ITcomma "ITvarid \"peg'k2\"" ITcbrack ;;
    esac
    printf '%s\n' ITcparen ITccurly ITsemi
  done
  printf '%s\n' ITeof
} > "$scratch/RenderReturn.expected-tokens"
diff -u "$scratch/RenderReturn.expected-tokens" "$scratch/RenderReturn.tokens"

sed 's/productions 708 =/productions 709 =/' \
  verification/RenderPrimitiveStatement.lean > "$scratch/RenderPrimitiveStatementInvalid.lean"
if cmp -s verification/RenderPrimitiveStatement.lean "$scratch/RenderPrimitiveStatementInvalid.lean"; then
  echo 'pure statement production mutation did not change the source' >&2
  exit 1
fi
if (cd verification && lean -DwarningAsError=true \
    "$scratch/RenderPrimitiveStatementInvalid.lean") \
    > "$scratch/RenderPrimitiveStatementInvalid.log" 2>&1; then
  echo 'Lean accepted a changed unit-constructor production' >&2
  exit 1
fi
grep -Fq 'Tactic `decide` proved that' "$scratch/RenderPrimitiveStatementInvalid.log" || {
  cat "$scratch/RenderPrimitiveStatementInvalid.log" >&2
  exit 1
}

printf 'Generated statements: 30 Lean theorems, 9 source checks, 85 GHC tokens, 1 rejected mutation.\n'
