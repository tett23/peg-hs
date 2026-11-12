#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
codegen=${1:-packages/peg-codegen/src/Peg/Codegen.hs}
cli=${2:-packages/peg-cli/app/Command/Gen.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

# Any change to the Haskell do/bind chain requires a review of Pipeline.lean.
cat > "$expected" <<'SOURCE'
generateWithWarnings :: Options -> Maybe Text -> [(FilePath, Text)] -> Text -> Either [Diagnostic] Generation
generateWithWarnings opts strip libraries src = do
  g0 <- parseGrammar src >>= \g -> resolveImports g libraries
  g <- either (Left . templateNotes g0) Right (expandTemplates g0 >>= \g -> g <$ check g)
  let target = maybe g (`stripLabelsAs` g) strip
      warnings = maybe (templateNotes g0 (labelWarnings g)) (const []) strip
  pure (Generation target warnings (generate opts target))
SOURCE
sed -n '/^generateWithWarnings ::/,/^  pure (Generation target warnings (generate opts target))$/p' "$codegen" |
  diff -u "$expected" -

[ "$(grep -Fxc '  , generationModule :: Either [Diagnostic] Text' "$codegen")" -eq 1 ]

cat > "$expected" <<'SOURCE'
    Right (imports, texts) -> case generateWithWarnings opts (T.pack <$> strip) texts src of
      Left diags -> reportErrors input imports diags >> pure (ExitFailure 1)
      Right gen -> written imports gen
SOURCE
sed -n '/^    Right (imports, texts) -> case generateWithWarnings/,/^      Right gen -> written imports gen$/p' "$cli" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
        else case generationModule gen of
          Left diags -> reportErrors input imports diags >> pure (ExitFailure 1)
          Right code ->
SOURCE
sed -n '/^        else case generationModule gen of/,/^          Right code ->$/p' "$cli" |
  diff -u "$expected" -

"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-codegen -package=peg-grammar \
  verification/PipelineProbe.hs
