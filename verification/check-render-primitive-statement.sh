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

printf 'Generated statements: 9 Lean theorems, 3 source checks, 36 GHC tokens, 1 rejected mutation.\n'
