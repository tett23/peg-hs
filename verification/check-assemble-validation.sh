#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-grammar/src/Peg/Grammar/Assemble.hs}
parser_file=${2:-packages/peg-grammar/src/Peg/Grammar/Parser.hs}
codegen_file=${3:-packages/peg-codegen/src/Peg/Codegen.hs}
expected=$(mktemp)
actual=$(mktemp)
trap 'rm -f "$expected" "$actual"' EXIT HUP INT TERM

# Covers every validation list-comprehension, the missing-module branch,
# rule construction, and the finite scans in assemble. Any source change
# requires re-review of the Lean data model and every diagnostic source.
sed -n '/^assemble ::/,/^-- | Whether a text is a path/p' "$source_file" |
  sed '$d' > "$actual"
[ "$(git hash-object --stdin < "$actual")" = 47a3413aa08f794f7acd663957963c0e8b4fc92e ]
# Predicate and splitting helpers (including stringArg/decodeString) are
# opaque in Lean. Pin them too so that a semantic change stops this check.
[ "$(git hash-object "$source_file")" = 7a3eb05bf4d3be02ad1c845a9ccea9a5b68f2738 ]

cat > "$expected" <<'SOURCE'
parseGrammar :: Text -> Either [Diagnostic] Grammar
parseGrammar src = parseTops src >>= assemble
SOURCE
sed -n '/^parseGrammar ::/,/^parseGrammar src =/p' "$parser_file" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
generateWithWarnings :: Options -> Maybe Text -> [(FilePath, Text)] -> Text -> Either [Diagnostic] Generation
generateWithWarnings opts strip libraries src = do
  g0 <- parseGrammar src >>= \g -> resolveImports g libraries
  g <- either (Left . templateNotes g0) Right (expandTemplates g0 >>= \g -> g <$ check g)
  let target = maybe g (`stripLabelsAs` g) strip
      warnings = maybe (templateNotes g0 (labelWarnings g)) (const []) strip
  pure (Generation target warnings (generate opts target))
SOURCE
sed -n '/^generateWithWarnings ::/,/^  pure (Generation target warnings (generate opts target))$/p' \
  "$codegen_file" | diff -u "$expected" -

"${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 \
  -package=peg-codegen -package=peg-grammar \
  verification/AssembleValidationProbe.hs
