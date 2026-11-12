#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
[ -f "$LEAN_PATH/RenderExpression.olean" ] || {
  echo 'RenderExpression.olean is missing' >&2
  exit 1
}

cat > "$scratch/render-expression-expected" <<'SOURCE'
ruleVar :: Text -> Text
ruleVar n = "peg'rule'" <> n
SOURCE
sed -n '/^ruleVar ::/,/^ruleVar n =/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/render-expression-expected" -

cat > "$scratch/render-expression-expected" <<'SOURCE'
doBlock :: [Text] -> Text
doBlock stmts = "do { " <> T.concat (intersperse "\n          ; " stmts) <> "\n          }"
SOURCE
sed -n '/^doBlock ::/,/^doBlock stmts =/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/render-expression-expected" -

cat > "$scratch/render-expression-expected" <<'SOURCE'
  EAny -> pure "PegRt.anyChar"
  ERef _ n [] -> pure (ruleVar n)
  ERef _ n args ->
    pure ("PegRt.withCol (\\_col -> " <> ruleVar n <> T.concat [" (" <> fragmentEnv env x <> ")" | x <- args] <> ")")
  EGroup alts
    | used && hasValue (units env) expr -> do
        bodies <- mapM (\is -> passThrough env False is >>= \(stmts, v) -> pure (doBlock (stmts ++ ["PegPrelude.pure " <> v]))) alts
        pure ("PegRt.choice [" <> T.intercalate ", " bodies <> "]")
    | otherwise -> do
        bodies <- mapM (\is -> mapM (itemStmt env False) is >>= \stmts -> pure (doBlock (stmts ++ ["PegPrelude.pure ()"]))) alts
        pure ("PegRt.choice [" <> T.intercalate ", " bodies <> "]")
  EStar x -> wrap (if valued x then "PegRt.many" else "PegRt.skipMany") used x
SOURCE
awk '/^exprCodeU env used expr =/ { in_expr = 1 }
     in_expr && /^  EAny ->/ { copy = 1 }
     copy { print }
     copy && /^  EStar x ->/ { exit }' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/render-expression-expected" -

cat > "$scratch/render-expression-expected" <<'SOURCE'
    wrap f inner x = do
      e <- exprCodeU env inner x
      pure (f <> " (" <> e <> ")")
SOURCE
awk '/^exprCodeU env used expr =/ { in_expr = 1 }
     in_expr && /^    wrap f inner x =/ { copy = 1 }
     copy { print }
     copy && index($0, "      pure (f <>") == 1 { exit }' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$scratch/render-expression-expected" -

printf 'Matched rule references, group choice, wrappers, and do-block printer source.\n'
