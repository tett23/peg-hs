#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-codegen/src/Peg/Codegen.hs}
assemble_file=${2:-packages/peg-grammar/src/Peg/Grammar/Assemble.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

# These expressions are the complete inner failure and success path modeled
# by InnerGeneration.lean. An unmodeled branch must fail this check.
cat > "$expected" <<'SOURCE'
generate :: Options -> Grammar -> Either [Diagnostic] Text
generate opts g0 = do
  if any (any isControlChar) [optSourceName opts, optOutputName opts]
    then Left [Diagnostic (Loc 0 1 1) "the file name contains a control character"]
    else pure ()
  if isModuleName (unLoc (grammarModule g0))
    then pure ()
    else Left [Diagnostic (Loc 0 1 1) ("the generated module name is invalid: " <> unLoc (grammarModule g0))]
  g <- either (Left . templateNotes g0) Right (expandTemplates g0)
  analysis <- either (Left . templateNotes g0) Right (check g)
  case undefinedExports opts g analysis of
    [] ->
      let unmarked = render opts g analysis ""
          marker = freshRestoreMarker (S.fromList (filter (T.isPrefixOf "{-# PEG'RESTORE_") (T.lines unmarked)))
       in Right (finalize opts marker (render opts g analysis marker))
    missing -> Left [Diagnostic (Loc 0 1 1) ("the generator does not define " <> n) | n <- missing]
SOURCE
sed -n '/^generate ::/,/^    missing -> Left \[Diagnostic (Loc 0 1 1) /p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
freshRestoreMarker :: Set Text -> Text
freshRestoreMarker occupied = choose 0
  where
    choose :: Int -> Text
    choose n =
      let marker = "{-# PEG'RESTORE_" <> T.replicate n "x" <> " #-}"
       in if S.member marker occupied then choose (n + 1) else marker
SOURCE
sed -n '/^freshRestoreMarker ::/,/^       in if S.member marker occupied then choose (n + 1) else marker$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
finalize :: Options -> Text -> Text -> Text
finalize opts marker t = T.unlines (zipWith fix [1 :: Int ..] (T.lines t))
  where
    fix n line
      | line == marker = "{-# LINE " <> showT (n + 1) <> " " <> T.pack (show (optOutputName opts)) <> " #-}"
      | otherwise = line
SOURCE
sed -n '/^finalize ::/,/^      | otherwise = line$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isControlChar :: Char -> Bool
isControlChar c = c < '\x20' || c == '\x7F'
SOURCE
sed -n '/^isControlChar ::/,/^isControlChar c = /p' "$source_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_' || c == '\''
SOURCE
sed -n '/^isIdentChar ::/,/^isIdentChar c = /p' "$assemble_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isClassName :: Text -> Bool
isClassName t = not (T.null t) && all part (T.splitOn "." t)
  where
    part p = case T.uncons p of
      Just (c, rest) -> isUpper c && T.all isIdentChar rest
      Nothing -> False
SOURCE
sed -n '/^isClassName ::/,/^      Nothing -> False$/p' "$assemble_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
isModuleName :: Text -> Bool
isModuleName = isClassName
SOURCE
sed -n '/^isModuleName ::/,/^isModuleName = isClassName$/p' "$assemble_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
undefinedExports :: Options -> Grammar -> Analysis -> [Text]
undefinedExports opts g an = case optExports opts of
  Nothing -> []
  Just names -> nubOrd [n | n <- names, not (S.member n defined)]
  where
    defined = S.fromList (map selectable (generatedNames g an))
    nubOrd = go S.empty
    go _ [] = []
    go seen (x : xs)
      | S.member x seen = go seen xs
      | otherwise = x : go (S.insert x seen) xs
SOURCE
sed -n '/^undefinedExports ::/,/^      | otherwise = x : go (S.insert x seen) xs$/p' "$source_file" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
  , generationModule :: Either [Diagnostic] Text
SOURCE
sed -n '/^data Generation =/,/^generateWithWarnings ::/p' "$source_file" |
  sed -n '/^  , generationModule :: Either \[Diagnostic\] Text$/p' |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
  pure (Generation target warnings (generate opts target))
SOURCE
sed -n '/^generateWithWarnings ::/,/^  pure (Generation target warnings (generate opts target))$/p' "$source_file" |
  sed -n '/^  pure (Generation target warnings (generate opts target))$/p' |
  diff -u "$expected" -

printf 'Checked inner generation source contract.\n'
