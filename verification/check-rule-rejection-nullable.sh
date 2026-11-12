#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Check.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

# This whole source span is the contract translated by RuleRejectionNullable.
# New constructors, changed operators, or changed fixed-point order fail closed.
cat > "$expected" <<'SOURCE'
nullableRules :: [Rule] -> Set Text
nullableRules = nullableRulesWith M.empty

-- The rules that can match the empty string, given the recovery rule of
-- each label (ADR 0095): with recovery, @e ^l@ acts as @e / R@ for the
-- recovery rule @R@ of @l@. Without recovery rules, those of the language.
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
      EStar _ -> True
      EOpt _ -> True
      EPlus x -> go x
      EAnd _ -> True
      ENot _ -> True
      EPred _ _ -> True
      ECapture x -> go x
      ELabel _ x l -> go x || maybe False (`S.member` known) (M.lookup l recovery)
      EDiscard x -> go x
      ETemplate {} -> True
SOURCE
sed -n '/^nullableRules ::/,/^      ETemplate {} -> True$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    nullable = nullableRules rules
    lr = leftRecursiveRules (M.fromList [(unLoc l, unLoc r) | (l, r) <- grammarRecovers g]) rules
SOURCE
sed -n '/^checkRules ::/,/^-- Left recursion /p' "$source_file" |
  sed -n '/^    nullable = nullableRules rules$/p;/^    lr = leftRecursiveRules /p' |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
        ++ concatMap (repetitionErrors nullable) rules
SOURCE
sed -n '/^    errors =$/,/^        ++ recoverErrors$/p' "$source_file" |
  sed -n '/^        ++ concatMap (repetitionErrors nullable) rules$/p' |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    known = nullableRulesWith recovery rules
SOURCE
sed -n '/^leftRecursiveRules ::/,/^-- Alternatives /p' "$source_file" |
  sed -n '/^    known = nullableRulesWith recovery rules$/p' |
  diff -u "$expected" -

printf 'Checked language and recovery nullable source contracts.\n'
