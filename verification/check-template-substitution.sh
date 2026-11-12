#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Templates.hs}
grammar_file=${2:-packages/peg-grammar/src/Peg/Grammar.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

cat > "$expected" <<'SOURCE'
substituteAlt :: M.Map Text (TemplateParam, Expr) -> Alt -> Alt
substituteAlt sub a = a {altItems = map item (altItems a)}
  where
    item i = i {itemExpr = expr (itemExpr i)}
    expr = \case
      ERef _ n [] | Just (p, arg) <- M.lookup n sub -> if isJust (templateParamType p) then arg else EDiscard arg
      EGroup alts -> EGroup (map (map item) alts)
      EStar x -> EStar (expr x)
      EPlus x -> EPlus (expr x)
      EOpt x -> EOpt (expr x)
      EAnd x -> EAnd (expr x)
      ENot x -> ENot (expr x)
      ECapture x -> ECapture (expr x)
      ELabel l x n -> ELabel l (expr x) n
      EDiscard x -> EDiscard (expr x)
      -- A parameter passed on to a template is put as it is: the template
      -- called decides whether its value is used.
      ETemplate l n args vals -> ETemplate l n (map passed args) vals
      e -> e
    passed = \case
      ERef _ n [] | Just (_, arg) <- M.lookup n sub -> arg
      e -> expr e
SOURCE
sed -n '/^substituteAlt ::/,/^      e -> expr e$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    expandExpr caller depth scope = \case
      ERef l n args
        | M.member n templates -> do
            addError (Diagnostic l ("the template " <> n <> " needs arguments: " <> n <> "<...>"))
            pure (ERef l n args)
      ETemplate l n args vals -> case M.lookup n templates of
        Nothing -> do
          addError (Diagnostic l ("rule " <> n <> " is not a template"))
          pure (ERef l n [])
        Just t -> do
          -- The value arguments of the value parameters (ADR 0055).
          let valueParams = ruleParams t
          if null valueParams && not (null vals)
            then addError (Diagnostic l ("the template " <> n <> " takes no value arguments"))
            else
              if length vals /= length valueParams
                then addError (Diagnostic l ("the template " <> n <> " expects " <> T.pack (show (length valueParams)) <> " value argument(s), but got " <> T.pack (show (length vals))))
                else pure ()
          args' <- mapM (expandExpr caller depth scope) args
          let params = ruleTemplateParams t
          if length args' /= length params
            then do
              addError (Diagnostic l ("the template " <> n <> " expects " <> T.pack (show (length params)) <> " argument(s), but got " <> T.pack (show (length args'))))
              pure (ERef l n [])
            else do
              captured <- captures l caller scope t args'
              tys <- mapM (argType l) (zip params args')
              name <- instanceOf l depth t args' tys captured
              pure (ERef l name (vals ++ [Located l x | (x, _) <- captured]))
      EGroup alts -> EGroup <$> mapM (expandItems caller depth scope) alts
SOURCE
sed -n '/^    expandExpr caller depth scope =/,/^      EGroup alts ->/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
                alts <- mapM (expandAlt caller depth S.empty . substituteAlt sub) (ruleAlts t)
SOURCE
sed -n '/^    drain =$/,/^    maxDepth = /p' "$source_file" |
  sed -n '/^                alts <- mapM (expandAlt caller depth S.empty . substituteAlt sub) (ruleAlts t)$/p' |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
      (_, St {stErrors = errs@(_ : _)}) -> Left (nub (reverse errs))
SOURCE
sed -n '/^expandOnce ::/,/^  where$/p' "$source_file" |
  sed -n '/^      (_, St {stErrors = errs@(_ : _)}) -> Left (nub (reverse errs))$/p' |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
addError :: Diagnostic -> Expand ()
addError d = modify' $ \st -> st {stErrors = d : stErrors st}
SOURCE
sed -n '/^addError ::/,/^addError d = /p' "$source_file" | diff -u "$expected" -

# The default cases in substituteAlt are sound only if the constructor list
# remains exactly the one translated into TemplateSubstitution.Expr.
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

printf 'Checked individual template substitution and direct diagnostics.\n'
