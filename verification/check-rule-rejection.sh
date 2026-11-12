#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Check.hs}
grammar_file=${2:-packages/peg-grammar/src/Peg/Grammar.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

cat > "$expected" <<'SOURCE'
check :: Grammar -> Either [Diagnostic] Analysis
check g = case (grammarLibrary g, grammarRules g) of
  (Just _, _) -> Left [Diagnostic (Loc 0 1 1) "missing %module directive"]
  (_, []) -> Left [Diagnostic (Loc 0 1 1) "the grammar has no rules"]
  (_, firstRule : _) -> checkRules True g firstRule
SOURCE
sed -n '/^check ::/,/^  (_, firstRule : _) -> checkRules True g firstRule$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
checkRules :: Bool -> Grammar -> Rule -> Either [Diagnostic] Analysis
checkRules root g firstRule =
  case sortOn diagLoc (if root then errors else libraryErrors) of
    [] -> Right (Analysis start lr nullable units classes)
    es -> Left es
  where
SOURCE
sed -n '/^checkRules ::/,/^  where$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    rules = grammarRules g
    ruleMap = M.fromList [(ruleName r, r) | r <- rules]
    start = maybe (ruleName firstRule) unLoc (grammarStart g)
    nullable = nullableRules rules
SOURCE
sed -n '/^checkRules ::/,/^-- Left recursion /p' "$source_file" |
  sed -n '/^    rules = grammarRules g$/,/^    nullable = nullableRules rules$/p' |
  sed '/^    -- /d' | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    errors =
      undefinedErrors
        ++ arityErrors
        ++ entryErrors
        ++ reachabilityErrors
        ++ concatMap (repetitionErrors nullable) rules
        ++ concatMap (altErrors True units (discardingRules g) (valuedRules g classes) (classUnknown classes)) rules
        ++ concatMap bindingReferenceErrors rules
        ++ constructorErrors g classes
        ++ paramLrErrors
        ++ syntaxNameErrors g
        ++ concatMap hygieneErrors (grammarVerbatim g)
        ++ languageErrors
        ++ nomemoErrors
        ++ syntaxErrors
        ++ recoverErrors
SOURCE
sed -n '/^    errors =$/,/^        ++ recoverErrors$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    refs = [(l, n, length args) | r <- rules, a <- ruleAlts r, (l, n, args) <- itemsRefs (altItems a)]
SOURCE
sed -n '/^checkRules ::/,/^-- Left recursion /p' "$source_file" |
  sed -n '/^    refs = \[(l, n, length args) /p' | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    undefinedErrors =
      [Diagnostic l ("undefined rule " <> n) | (l, n, _) <- refs, not (M.member n ruleMap)]
        ++ [ Diagnostic l ("undefined rule " <> n)
           | Located l n <-
               maybe [] pure (grammarStart g)
                 ++ grammarEntries g
                 ++ grammarNoMemo g
                 ++ grammarTokens g
                 ++ grammarTrivia g
                 ++ grammarInline g
                 ++ map fst (grammarExpects g)
           , not (M.member n ruleMap)
           ]
SOURCE
sed -n '/^    undefinedErrors =$/,/^           ]$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
repetitionErrors :: Set Text -> Rule -> [Diagnostic]
repetitionErrors known r = concatMap (seqErrs . altItems) (ruleAlts r)
  where
    seqErrs = concatMap (\i -> exprErrs (itemLoc i) (itemExpr i))
    exprErrs l e = case e of
      EStar x -> rep l x
      EPlus x -> rep l x
      EOpt x -> exprErrs l x
      EAnd x -> exprErrs l x
      ENot x -> exprErrs l x
      ECapture x -> exprErrs l x
      ELabel _ x _ -> exprErrs l x
      EDiscard x -> exprErrs l x
      EGroup alts -> concatMap seqErrs alts
      _ -> []
    rep l x
      | exprNullable known x = Diagnostic l "the repeated expression can match the empty string, which would loop forever" : exprErrs l x
      | otherwise = exprErrs l x
SOURCE
sed -n '/^repetitionErrors ::/,/^      | otherwise = exprErrs l x$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
      EPred _ _ -> True
SOURCE
sed -n '/^exprNullableWith ::/,/^      ETemplate {} -> True$/p' "$source_file" |
  sed -n '/^      EPred _ _ -> True$/p' | diff -u "$expected" -

# Every Expr constructor must be accounted for by the Lean traversal.
cat > "$expected" <<'SOURCE'
ELit
EClass
EAny
ERef
EGroup
EStar
EPlus
EOpt
EAnd
ENot
ECapture
ELabel
EPred
ETemplate
EDiscard
SOURCE
awk '
  /^data Expr$/ { inside = 1; next }
  inside && /^  deriving \(Eq, Show\)$/ { exit }
  inside && /^[[:space:]]*\|?[[:space:]]*E[A-Z][A-Za-z0-9_]*([[:space:]]|$)/ {
    line = $0
    sub(/^[[:space:]]*\|?[[:space:]]*/, "", line)
    split(line, fields, /[[:space:]]/)
    print fields[1]
  }
' "$grammar_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
itemsRefs :: [Item] -> [(Loc, Text, [Located Text])]
itemsRefs = concatMap (exprRefs . itemExpr)

exprRefs :: Expr -> [(Loc, Text, [Located Text])]
exprRefs = \e -> case e of
  ERef l n args -> [(l, n, args)]
  EGroup alts -> concatMap itemsRefs alts
  EStar x -> exprRefs x
  EPlus x -> exprRefs x
  EOpt x -> exprRefs x
  EAnd x -> exprRefs x
  ENot x -> exprRefs x
  ECapture x -> exprRefs x
  ELabel _ x _ -> exprRefs x
  EDiscard x -> exprRefs x
  ETemplate _ _ args _ -> concatMap exprRefs args
  _ -> []
SOURCE
sed -n '/^itemsRefs ::/,/^  _ -> \[\]$/p' "$source_file" | diff -u "$expected" -

printf 'Checked check and checkRules rejection source.\n'
"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-codegen -package=peg-grammar \
  verification/RuleRejectionProbe.hs
