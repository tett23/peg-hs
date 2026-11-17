#!/bin/sh
# ADR 0097 invariant 3: the text that generate returns is finalize's output,
# not render's. Compile RenderFinalize and RenderFinalizeModule, pin the
# Haskell that they model, and run the Lean model of finalize on modules that
# peg-hs generates. GHC 9.10.3's parser (the tracer that
# check-ghc-parser-trace.sh builds in the same directory) must accept each
# finalized module. It must not read render's text, with the markers, as the
# same tokens: that is why RenderFinalizeModule states the lexer obligations
# after finalize.
set -eu
cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
ghc=${GHC:-ghc-9.10.3}

for module in RenderFinalize RenderFinalizeModule; do
  (cd verification && lean -DwarningAsError=true \
    -o "$scratch/$module.olean" "$module.lean") > "$scratch/$module.log"
  if grep -Fq 'sorryAx' "$scratch/$module.log"; then
    cat "$scratch/$module.log" >&2
    exit 1
  fi
done

codegen=packages/peg-codegen/src/Peg/Codegen.hs

# The Haskell that RenderFinalize models: finalize, the marker that
# freshRestoreMarker chooses, the two renders in generate, the marker on a
# line of its own after each fragment, and the runtime range in the header.
cat > "$scratch/FinalizeSource.expected" <<'SOURCE'
finalize :: Options -> Text -> Text -> Text
finalize opts marker t = T.unlines (zipWith fix [1 :: Int ..] (T.lines t))
  where
    fix n line
      | line == marker = "{-# LINE " <> showT (n + 1) <> " " <> T.pack (show (optOutputName opts)) <> " #-}"
      | otherwise = line
SOURCE
sed -n '/^finalize ::/,/^      | otherwise = line$/p' "$codegen" > "$scratch/FinalizeSource.actual"
diff -u "$scratch/FinalizeSource.expected" "$scratch/FinalizeSource.actual"

cat > "$scratch/FinalizeMarker.expected" <<'SOURCE'
freshRestoreMarker :: Set Text -> Text
freshRestoreMarker occupied = choose 0
  where
    choose :: Int -> Text
    choose n =
      let marker = "{-# PEG'RESTORE_" <> T.replicate n "x" <> " #-}"
       in if S.member marker occupied then choose (n + 1) else marker
SOURCE
sed -n '/^freshRestoreMarker ::/,/^       in if S.member/p' "$codegen" > "$scratch/FinalizeMarker.actual"
diff -u "$scratch/FinalizeMarker.expected" "$scratch/FinalizeMarker.actual"

cat > "$scratch/FinalizeGenerate.expected" <<'SOURCE'
    [] ->
      let unmarked = render opts g analysis ""
          marker = freshRestoreMarker (S.fromList (filter (T.isPrefixOf "{-# PEG'RESTORE_") (T.lines unmarked)))
       in Right (finalize opts marker (render opts g analysis marker))
SOURCE
sed -n '/^    \[\] ->$/,/^       in Right (finalize/p' "$codegen" > "$scratch/FinalizeGenerate.actual"
diff -u "$scratch/FinalizeGenerate.expected" "$scratch/FinalizeGenerate.actual"

cat > "$scratch/FinalizeFragment.expected" <<'SOURCE'
fragment :: (Int -> FilePath) -> Text -> Located Text -> Text
fragment sources marker (Located (Loc f l c) t) =
  T.concat
    [ "\n{-# LINE "
    , showT l
    , " "
    , T.pack (show (sources f))
    , " #-}\n {-# COLUMN "
    , showT c
    , " #-}"
    , t
    , "\n"
    , marker
    , "\n    "
    ]
SOURCE
sed -n '/^fragment ::/,/^    \]$/p' "$codegen" > "$scratch/FinalizeFragment.actual"
diff -u "$scratch/FinalizeFragment.expected" "$scratch/FinalizeFragment.actual"

[ "$(grep -c '^runtimeVersions = "peg-runtime >=0.1 && <0.2"$' "$codegen")" -eq 1 ] || {
  echo 'runtimeVersions no longer matches RenderFinalize.runtimeVersions' >&2
  exit 1
}
# The header lines themselves are pinned with the rest of render's list by
# check-render-composition.sh.

# Probe: generate modules, undo finalize (each LINE pragma that names the
# output file and the line after it becomes the marker again), and run the
# Lean finalize on that text. It must give the generated file byte for byte.
peg=${PEG_HS:-}
if [ -z "$peg" ]; then
  peg=$("${CABAL:-cabal}" list-bin exe:peg-hs)
fi
tracer="$scratch/trace-generated-module"
[ -x "$tracer" ] || {
  echo 'run check-ghc-parser-trace.sh first: the GHC token tracer is missing' >&2
  exit 1
}
libdir=$("$ghc" --print-libdir)
probe="$scratch/finalize-probe"
rm -rf "$probe"
mkdir -p "$probe"

# Verbatim blocks before and after the rules, a dotted %module, a %language,
# a typed rule, and a verbatim line that holds the first marker that
# freshRestoreMarker tries, so that it must choose another.
cat > "$probe/FinalizeVerbatim.hpeg" <<'GRAMMAR'
%module Probe.Finalize.Verbatim
%language ScopedTypeVariables
%{
import Data.Char (isDigit)
{-# PEG'RESTORE_ #-}

digitCount :: [Char] -> Int
digitCount = length . filter isDigit
}%
S :: Int
S <- 'a' { digitCount "a1" + extra }
%{
extra :: Int
extra = 1
}%
GRAMMAR

languages_of() {
  sed -n 's/^%language //p' "$1" | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' || true
}

grammars=0
markers=0
tokens=0
apart=0
check_grammar() {
  grammar=$1
  name=$2
  pruned=$3
  shift 3
  out="$probe/$name.hs"
  "$peg" gen "$grammar" -o "$out" "$@"
  # The marker: the first restoreMarker k that is no line of the module.
  k=0
  while grep -Fqx "{-# PEG'RESTORE_$(printf '%*s' "$k" '' | tr ' ' x) #-}" "$out"; do
    k=$((k + 1))
  done
  marker="{-# PEG'RESTORE_$(printf '%*s' "$k" '' | tr ' ' x) #-}"
  awk -v out="$out" -v marker="$marker" '
    $0 == "{-# LINE " (NR + 1) " \"" out "\" #-}" { print marker; n++; next }
    { print }
    END { print n > "/dev/stderr" }
  ' "$out" > "$probe/$name.rendered" 2> "$probe/$name.markers"
  count=$(cat "$probe/$name.markers")
  [ "$count" -gt 0 ] || {
    echo "$name: the generated module has no restored LINE pragma" >&2
    exit 1
  }
  markers=$((markers + count))
  (cd verification && lean --run RenderFinalizeProbe.lean finalize "\"$out\"" "$k" \
    "$probe/$name.rendered") > "$probe/$name.finalized"
  cmp "$out" "$probe/$name.finalized" || {
    diff -u "$out" "$probe/$name.finalized" >&2 || true
    echo "$name: the Lean finalize differs from the generated module" >&2
    exit 1
  }

  # The header lines open the module as headerLines predicts.
  # shellcheck disable=SC2046
  (cd verification && lean --run RenderFinalizeProbe.lean header "$grammar" "$pruned" \
    $(languages_of "$grammar")) > "$probe/$name.header"
  head -n "$(wc -l < "$probe/$name.header")" "$out" | cmp - "$probe/$name.header" || {
    echo "$name: the header lines differ from headerLines" >&2
    exit 1
  }

  # GHC reads the finalized module to the end. Render's text, with the
  # markers, is lexed apart from it (the count of such modules is reported).
  for text in hs rendered; do
    file="$probe/$name.$text"
    [ "$text" = hs ] && file=$out
    "$tracer" "$libdir" "$file" 2> "$probe/$name.$text.trace" > "$probe/$name.$text.result" || true
    grep '^LEXID ' "$probe/$name.$text.trace" > "$probe/$name.$text.ids" || true
  done
  grep -q 'action: accept\.' "$probe/$name.hs.trace" || {
    echo "$name: GHC's parser did not accept the generated module" >&2
    exit 1
  }
  if ! cmp -s "$probe/$name.hs.ids" "$probe/$name.rendered.ids"; then
    apart=$((apart + 1))
  fi
  tokens=$((tokens + $(wc -l < "$probe/$name.hs.ids")))
  grammars=$((grammars + 1))
}

check_grammar "$probe/FinalizeVerbatim.hpeg" FinalizeVerbatim full
grep -Fqx "{-# PEG'RESTORE_ #-}" "$probe/FinalizeVerbatim.hs" || {
  echo 'FinalizeVerbatim: the verbatim marker line was not kept' >&2
  exit 1
}
grep -Fqx "{-# PEG'RESTORE_x #-}" "$probe/FinalizeVerbatim.rendered" || {
  echo 'FinalizeVerbatim: freshRestoreMarker did not skip the occupied marker' >&2
  exit 1
}
fixtures=packages/peg-codegen/test/fixtures
check_grammar "$fixtures/Templates.hpeg" Templates full
check_grammar "$fixtures/Recover.hpeg" Recover full
check_grammar "$fixtures/Extensions.hpeg" Extensions full
check_grammar "$fixtures/Link.hpeg" Link full
check_grammar "$fixtures/Calc.hpeg" CalcPruned pruned --export parse
grep -Fqx '{-# OPTIONS_GHC -Wno-unused-imports -Wno-unused-top-binds #-}' "$probe/CalcPruned.hs" || {
  echo 'CalcPruned: --export did not prune the module' >&2
  exit 1
}
check_grammar packages/peg-grammar/grammar/PegSyntax.hpeg PegSyntax full
[ "$apart" -gt 0 ] || {
  echo "GHC lexed render's text with the markers as the generated module; revisit RenderFinalizeModule" >&2
  exit 1
}

# A changed line number in the model must break finalize_line_numbers.
sed 's/  if line = marker then linePragma (n + 1) shown else line/  if line = marker then linePragma (n + 2) shown else line/' \
  verification/RenderFinalize.lean > "$scratch/RenderFinalizeInvalid.lean"
if cmp -s verification/RenderFinalize.lean "$scratch/RenderFinalizeInvalid.lean"; then
  echo 'Render finalize mutation did not change the line number' >&2
  exit 1
fi
if (cd verification && lean -DwarningAsError=true "$scratch/RenderFinalizeInvalid.lean") \
    > "$scratch/RenderFinalizeInvalid.log" 2>&1; then
  echo 'Lean accepted a LINE pragma that names the wrong line' >&2
  exit 1
fi
grep -Fq "'PegHs.RenderFinalize.finalize_line_numbers' depends on axioms: [propext, sorryAx" \
  "$scratch/RenderFinalizeInvalid.log" || {
  cat "$scratch/RenderFinalizeInvalid.log" >&2
  exit 1
}

printf 'Render finalize: %s grammars, %s restore markers, %s GHC tokens accepted after finalize, %s modules lexed apart before it, 4 exact source checks, 1 rejected mutation, 0 sorry axioms.\n' \
  "$grammars" "$markers" "$tokens" "$apart"
