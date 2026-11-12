#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Templates.hs}
grammar_file=${2:-packages/peg-grammar/src/Peg/Grammar.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

verification/check-template-substitution.sh "$source_file" "$grammar_file"

cat > "$expected" <<'SOURCE'
    expandAlt caller depth scope a = do
      items <- expandItems caller depth scope (altItems a)
      pure a {altItems = items}

    expandItems caller depth scope = \case
      [] -> pure []
      i : is -> do
        i' <- (\e -> i {itemExpr = e}) <$> expandExpr caller depth scope (itemExpr i)
        rest <- expandItems caller depth (maybe scope (`S.insert` scope) (itemBind i)) is
        pure (i' : rest)
SOURCE
sed -n '/^    expandAlt caller depth scope a =/,/^        pure (i'\'' : rest)$/p' \
  "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
      EStar x -> EStar <$> expandExpr caller depth scope x
      EPlus x -> EPlus <$> expandExpr caller depth scope x
      EOpt x -> EOpt <$> expandExpr caller depth scope x
      EAnd x -> EAnd <$> expandExpr caller depth scope x
      ENot x -> ENot <$> expandExpr caller depth scope x
      ECapture x -> ECapture <$> expandExpr caller depth scope x
      ELabel l x n -> (\x' -> ELabel l x' n) <$> expandExpr caller depth scope x
      EDiscard x -> EDiscard <$> expandExpr caller depth scope x
      e -> pure e
SOURCE
sed -n '/^      EStar x -> EStar <$> expandExpr caller depth scope x$/,/^      e -> pure e$/p' \
  "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    captures l caller scope t args = do
      let names = S.fromList (concatMap (concatMap haskellIdents . exprCode) args)
          bound = [x | x <- S.toAscList names, S.member x scope]
          taken = [(x, ty) | x <- S.toAscList names, x `notElem` reservedBindings, not (S.member x scope), Just ty <- [M.lookup x (callerParams caller)]]
          inBody = M.findWithDefault S.empty (ruleName t) bodyNames
      mapM_ (\x -> addError (Diagnostic l ("the argument of the template " <> ruleName t <> " uses the binding " <> x <> ", which a template cannot take; pass it as a value argument"))) bound
      mapM_
        (\x -> addError (Diagnostic l ("the template " <> ruleName t <> " uses the name " <> x <> " in its body, so its argument cannot take the parameter " <> x <> " of the rule " <> callerName caller <> "; rename the parameter")))
        [x | (x, _) <- taken, S.member x inBody]
      pure taken
SOURCE
sed -n '/^    captures l caller scope t args =/,/^      pure taken$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    argType l (p, a) = case templateParamType p of
      Nothing -> pure Nothing
      Just _ -> case a of
        ERef _ n _ -> do
          known <- gets' stInstanceTypes
          pure (Just (M.findWithDefault (M.findWithDefault "()" n ruleTypes) n known))
        ECapture _ -> pure (Just "PegRt.Text")
        _ -> do
          addError (Diagnostic l ("the argument for " <> templateParamName p <> " must be a rule, a capture or a template call, since its value is used"))
          pure (Just "()")
SOURCE
sed -n '/^    argType l (p, a) =/,/^          pure (Just "()")$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
    instanceOf l depth t args tys captured = do
      let key = (ruleName t, show (map plain args, [(x, unLoc ty) | (x, ty) <- captured]))
      existing <- gets' (M.lookup key . stInstances)
      case existing of
        Just name -> pure name
        Nothing -> do
          n <- gets' stCount
          let name = freshName (ruleName t) n
          modify' $ \st ->
            st
              { stInstances = M.insert key name (stInstances st)
              , stPending = stPending st ++ [(name, t, args, captured, depth + 1, l)]
              , stCount = stCount st + 1
              , stInstanceTypes = M.insert name (instanceType t tys) (stInstanceTypes st)
              , stInstanceNames = S.insert name (stInstanceNames st)
              }
          pure name

    freshName base n = case [c | k <- [n ..], let c = base <> "'" <> T.pack (show (k :: Int)), not (S.member c usedNames)] of
      c : _ -> c
      [] -> base
SOURCE
sed -n '/^    instanceOf l depth t args tys captured =/,/^      \[\] -> base$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
exprSize :: Expr -> Int
exprSize = \case
  EGroup alts -> 1 + sum (map (sum . map (exprSize . itemExpr)) alts)
  EStar x -> 1 + exprSize x
  EPlus x -> 1 + exprSize x
  EOpt x -> 1 + exprSize x
  EAnd x -> 1 + exprSize x
  ENot x -> 1 + exprSize x
  ECapture x -> 1 + exprSize x
  ELabel _ x _ -> 1 + exprSize x
  EDiscard x -> 1 + exprSize x
  ETemplate _ _ args _ -> 1 + sum (map exprSize args)
  _ -> 1
SOURCE
sed -n '/^exprSize ::/,/^  _ -> 1$/p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
                alts <- mapM (expandAlt caller depth S.empty . substituteAlt sub) (ruleAlts t)
SOURCE
sed -n '/^    drain =$/,/^    maxDepth = /p' "$source_file" |
  sed -n '/^                alts <- mapM (expandAlt caller depth S.empty . substituteAlt sub) (ruleAlts t)$/p' |
  diff -u "$expected" -

printf 'Checked captures, argument types, instance memoization, and expansion traversal.\n'
