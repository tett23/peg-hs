#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

[ -f "$LEAN_PATH/Nullable.olean" ] || {
  echo 'Nullable.olean is missing' >&2
  exit 1
}

cat > "$scratch/nullable-source-expected" <<'SOURCE'
nullableRulesWith :: Recovery -> [Rule] -> Set Text
nullableRulesWith recovery rules = go S.empty
  where
    go known =
      let next = S.fromList [ruleName r | r <- rules, any (seqNullableWith recovery known . altItems) (ruleAlts r)]
       in if next == known then known else go next

-- The recovery rule of each label (ADR 0021).
type Recovery = M.Map Text Text

seqNullableWith :: Recovery -> Set Text -> [Item] -> Bool
seqNullableWith recovery known = all (exprNullableWith recovery known . itemExpr)

exprNullable :: Set Text -> Expr -> Bool
exprNullable = exprNullableWith M.empty

exprNullableWith :: Recovery -> Set Text -> Expr -> Bool
exprNullableWith recovery known = go
  where
    go e = case e of
      ELit t _ -> T.null t
      EClass _ _ -> False
      EAny -> False
      ERef _ n _ -> S.member n known
      EGroup alts -> any (seqNullableWith recovery known) alts
SOURCE
sed -n '/^nullableRulesWith ::/,/^      EGroup alts ->/p'   packages/peg-grammar/src/Peg/Grammar/Check.hs |
  diff -u "$scratch/nullable-source-expected" -

printf 'Checked the projected nullableRulesWith source.\n'
