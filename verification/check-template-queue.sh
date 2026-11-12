#!/bin/sh
set -eu
scratch=${1:?pass the verification scratch directory}
source_file=packages/peg-grammar/src/Peg/Grammar/Templates.hs

# Extract the control flow that sets or propagates instance depth, mutates
# the queue, and schedules expansion passes. Fail if any such line changes.
project() {
  sed -n '/^expandTemplates ::/,/^    maxSize = /p' "$1" |
    grep -E 'depth|stPending|drain|go [(]8|go [(]k|go k known|expandOnce known g|known.*classifiedTypes|maxDepth =|maxSize =|expandAlt caller 0'
}
cat > "$scratch/expected-template-queue" <<'SOURCE'
  | otherwise = go (8 :: Int) M.empty
    go k known = do
      expanded <- expandOnce known g
      let known' = classifiedTypes (classify expanded)
      if known' == known || k <= 0 then Right expanded else go (k - 1) known'
  | otherwise = case runExpand (mapM expandRule ordinary >>= \rs -> (rs ++) <$> drain) (St M.empty [] [] 0 M.empty S.empty) of
      alts <- mapM (expandAlt caller 0 S.empty) (ruleAlts r)
    expandAlt caller depth scope a = do
      items <- expandItems caller depth scope (altItems a)
    expandItems caller depth scope = \case
        i' <- (\e -> i {itemExpr = e}) <$> expandExpr caller depth scope (itemExpr i)
        rest <- expandItems caller depth (maybe scope (`S.insert` scope) (itemBind i)) is
    expandExpr caller depth scope = \case
          args' <- mapM (expandExpr caller depth scope) args
              name <- instanceOf l depth t args' tys captured
      EGroup alts -> EGroup <$> mapM (expandItems caller depth scope) alts
      EStar x -> EStar <$> expandExpr caller depth scope x
      EPlus x -> EPlus <$> expandExpr caller depth scope x
      EOpt x -> EOpt <$> expandExpr caller depth scope x
      EAnd x -> EAnd <$> expandExpr caller depth scope x
      ENot x -> ENot <$> expandExpr caller depth scope x
      ECapture x -> ECapture <$> expandExpr caller depth scope x
      ELabel l x n -> (\x' -> ELabel l x' n) <$> expandExpr caller depth scope x
      EDiscard x -> EDiscard <$> expandExpr caller depth scope x
    instanceOf l depth t args tys captured = do
              , stPending = stPending st ++ [(name, t, args, captured, depth + 1, l)]
    drain =
      gets' stPending >>= \case
        (name, t, args, captured, depth, l) : _ -> do
          modify' $ \st -> st {stPending = drop 1 (stPending st)}
            if depth > maxDepth || sum (map exprSize args) > maxSize
                alts <- mapM (expandAlt caller depth S.empty . substituteAlt sub) (ruleAlts t)
          rest <- drain
    maxDepth = 64
    -- depth limit catches.
    maxSize = 10000
SOURCE
grep -Fqx 'templateNotes g = nub . map note' "$source_file"
project "$source_file" > "$scratch/template-queue-source"
diff -u "$scratch/expected-template-queue" "$scratch/template-queue-source"

# Exercise real expansion through the code generator at the last permitted
# depth and one beyond. Distinct names keep memoization from skipping a layer.
peg=$("${CABAL:-cabal}" list-bin exe:peg-hs)
for depth in 64 65; do
  grammar="$scratch/Chain$depth.hpeg"
  awk -v limit="$depth" 'BEGIN {
    print "%module Chain"
    print "S :: ()"
    print "S <- T1<\047a\047>"
    for (i = 1; i <= limit; i++) {
      print "T" i "<x> :: ()"
      print "T" i "<x> <- " (i == limit ? "x" : "T" (i+1) "<x>") " { () }"
    }
  }' > "$grammar"
  if [ "$depth" = 64 ]; then
    "$peg" gen "$grammar" -o "$scratch/Chain64.hs"
  elif "$peg" gen "$grammar" -o "$scratch/Chain65.hs" > "$scratch/chain65.log" 2>&1; then
    echo 'invariant2: generation unexpectedly accepted a depth-65 instance' >&2
    exit 1
  else
    grep -q 'does not end: templates call templates more than 64 levels deep' "$scratch/chain65.log"
    test ! -e "$scratch/Chain65.hs"
  fi
done
