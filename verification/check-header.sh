#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

cat > "$expected" <<'SOURCE'
generate opts g0 = do
  if any (any isControlChar) [optSourceName opts, optOutputName opts]
    then Left [Diagnostic (Loc 0 1 1) "the file name contains a control character"]
    else pure ()
  if isModuleName (unLoc (grammarModule g0))
    then pure ()
    else Left [Diagnostic (Loc 0 1 1) ("the generated module name is invalid: " <> unLoc (grammarModule g0))]
  g <- either (Left . templateNotes g0) Right (expandTemplates g0)
SOURCE
sed -n '/^generate opts g0 = do$/,/^  g <-/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''
SOURCE
sed -n '/^isIdentChar ::/{p;n;p;}' packages/peg-grammar/src/Peg/Grammar/Assemble.hs | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isClassName :: Text -> Bool
isClassName t = not (T.null t) && all part (T.splitOn "." t)
  where
    part p = case T.uncons p of
      Just (c, rest) -> isUpper c && T.all isIdentChar rest
      Nothing -> False
SOURCE
sed -n '/^isClassName ::/,/^      Nothing -> False/p' packages/peg-grammar/src/Peg/Grammar/Assemble.hs | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isModuleName :: Text -> Bool
isModuleName = isClassName
SOURCE
sed -n '/^isModuleName ::/,/^isModuleName =/p' packages/peg-grammar/src/Peg/Grammar/Assemble.hs | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
        ++ [ "module " <> unLoc (grammarModule g)
      , "  ( " <> T.intercalate "\n  , " exports
      , "  ) where"
      , ""
SOURCE
sed -n '/        ++ \[ "module "/,/      , ""/p' packages/peg-codegen/src/Peg/Codegen.hs | diff -u "$expected" -
