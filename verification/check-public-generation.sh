#!/bin/sh
# ADR 0097 invariants 1 to 3 at the public entries (PublicGeneration.lean,
# PublicGenerationGHC.lean). The Haskell that joins the stages is fixed by
# check-pipeline.sh (generateWithWarnings), check-inner-generation.sh
# (generate), check-assemble-validation.sh (parseGrammar),
# check-public-parsing.sh (parseTops) and check-import-resolution.sh
# (resolveImports, with `Right root {grammarRules = ...}`). This script fixes
# the rest of what PublicGeneration models: generateFromSource, the fields of
# the Generation record in the order of Pipeline.Generation, the order of Loc
# that `sortOn diagLoc` uses (PublicGeneration.locGt), and stripLabelsAs.
# A change to any of them requires a review of PublicGeneration.lean.
set -eu

cd "$(dirname "$0")/.."
codegen=${1:-packages/peg-codegen/src/Peg/Codegen.hs}
grammar=${2:-packages/peg-grammar/src/Peg/Grammar.hs}
labels=${3:-packages/peg-grammar/src/Peg/Grammar/Labels.hs}
expected=$(mktemp)
trap 'rm -f "$expected"' EXIT HUP INT TERM

cat > "$expected" <<'SOURCE'
generateFromSource :: Options -> Text -> Either [Diagnostic] Text
generateFromSource opts src = parseGrammar src >>= \g -> resolveImports g [] >>= generate opts
SOURCE
sed -n '/^generateFromSource ::/,/^generateFromSource opts src = /p' "$codegen" |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
data Generation = Generation
  { generationGrammar :: Grammar
  , generationWarnings :: [Diagnostic]
  , generationModule :: Either [Diagnostic] Text
  }
SOURCE
sed -n '/^data Generation = Generation$/,/^  }$/p' "$codegen" | grep -v '^  -- ' |
  diff -u "$expected" -

cat > "$expected" <<'SOURCE'
data Loc = Loc
  { locFile :: !Int
  , locLine :: !Int
  , locColumn :: !Int
  }
  deriving (Eq, Ord, Show)
SOURCE
sed -n '/^data Loc = Loc$/,/^  deriving (Eq, Ord, Show)$/p' "$grammar" | diff -u "$expected" -

cat > "$expected" <<'SOURCE'
stripLabelsAs :: Text -> Grammar -> Grammar
stripLabelsAs m g = (stripLabels g) {grammarModule = Located (locOf (grammarModule g)) m}
SOURCE
sed -n '/^stripLabelsAs ::/,/^stripLabelsAs m g = /p' "$labels" | diff -u "$expected" -

printf 'Checked the public generation source contract.\n'
