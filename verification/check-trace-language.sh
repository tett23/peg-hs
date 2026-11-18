#!/bin/sh
# ADR 0097 invariant 3: the GHC tracer (TraceGeneratedModule.hs, built by
# check-ghc-parser-trace.sh) reads a generated module under the flags that
# GHC's driver gives it when a package compiles it: the packages'
# default-language, GHC2021, and then the module's header pragmas, where
# %language puts its extensions. The Lean certificates of the self-hosted
# parsers and of the Extensions fixture are built from its traces, so the
# lexer and the parser that they record must be the ones under those flags.
#
# This check fails if a package that compiles the traced modules uses another
# default-language or default extensions, and if the tracer ignores a
# LANGUAGE pragma: for each probe, the module that peg-hs generates and the
# same module without the probed LANGUAGE line must get the opposite verdicts,
# and other lexer tokens for an extension of the lexer.
set -eu
cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
ghc=${GHC:-ghc-9.10.3}
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

# The base language of the tracer is the default-language of every package.
grep -Fq '(base, baseLeft, baseMessages) <- parseDynamicFlagsCmdLine session [noLoc "-XGHC2021"]' \
  verification/TraceGeneratedModule.hs || {
  echo 'the tracer no longer starts from GHC2021' >&2
  exit 1
}
# The packages that compile the traced modules: peg-grammar compiles the
# self-hosted parsers, and the tests of peg-codegen compile the fixtures.
cabals=0
for cabal in packages/peg-grammar/peg-grammar.cabal packages/peg-codegen/peg-codegen.cabal; do
  if grep -Eiq '^ *(default-extensions|default-language|language) *:' "$cabal"; then
    if grep -Ei '^ *(default-extensions|default-language|language) *:' "$cabal" |
        grep -Eiv '^ *default-language: *GHC2021 *$' >&2; then
      echo "$cabal: a component compiles with another language than GHC2021" >&2
      exit 1
    fi
  fi
  cabals=$((cabals + 1))
done

probe="$scratch/trace-language"
rm -rf "$probe"
mkdir -p "$probe"

# check_probe NAME EXTENSION VERDICT STAGE: generate $probe/NAME.hpeg; VERDICT
# is the tracer's verdict on the generated module (accept or reject). Without
# the LANGUAGE line of EXTENSION, the verdict must be the other one. STAGE is
# lexer when EXTENSION must also change GHC's lexer tokens, parser otherwise.
probes=0
check_probe() {
  name=$1
  extension=$2
  verdict=$3
  stage=$4
  out="$probe/$name.hs"
  "$peg" gen "$probe/$name.hpeg" -o "$out" >/dev/null
  [ "$(grep -Fxc "{-# LANGUAGE $extension #-}" "$out")" -eq 1 ] || {
    echo "$name: the generated module has no LANGUAGE $extension line" >&2
    exit 1
  }
  grep -Fvx "{-# LANGUAGE $extension #-}" "$out" > "$probe/$name.without.hs"
  sed -n 's/^%language //p' "$probe/$name.hpeg" | tr ',' '\n' |
    sed -e 's/^ *//' -e 's/ *$//' -e '/^$/d' -e 's/^/-X/' > "$probe/$name.options.expected"
  for text in hs without.hs; do
    file="$probe/$name.$text"
    [ "$text" = hs ] && file=$out
    if "$tracer" "$libdir" "$file" "$probe/$name.$text.options" \
        2> "$probe/$name.$text.trace" > "$probe/$name.$text.result"; then
      result=accept
    else
      result=reject
    fi
    grep '^LEXID ' "$probe/$name.$text.trace" > "$probe/$name.$text.ids" || true
    expected=$verdict
    if [ "$text" = without.hs ]; then
      [ "$verdict" = accept ] && expected=reject || expected=accept
    fi
    [ "$result" = "$expected" ] || {
      echo "$name.$text: GHC's parser should $expected the module; it did not" >&2
      exit 1
    }
  done
  cmp "$probe/$name.options.expected" "$probe/$name.hs.options" || {
    echo "$name: the tracer applied other header options than the grammar's %language" >&2
    exit 1
  }
  if grep -Fxq -- "-X$extension" "$probe/$name.without.hs.options"; then
    echo "$name: the tracer still read $extension without its LANGUAGE line" >&2
    exit 1
  fi
  if [ "$stage" = lexer ] && cmp -s "$probe/$name.hs.ids" "$probe/$name.without.hs.ids"; then
    echo "$name: $extension changed no lexer token; the probe does not show the pragma" >&2
    exit 1
  fi
  probes=$((probes + 1))
}

# A lexer extension that the module needs: magic# is one name with MagicHash,
# and the name magic and the operator # without it.
cat > "$probe/Magic.hpeg" <<'GRAMMAR'
%module Probe.Language.Magic
%language MagicHash
%{
magic# :: Int
magic# = 1
}%
S :: Int
S <- 'a' { magic# }
GRAMMAR
check_probe Magic MagicHash accept lexer

# A lexer extension that breaks the module: Arrows makes proc a keyword.
cat > "$probe/Arrows.hpeg" <<'GRAMMAR'
%module Probe.Language.Arrows
%language Arrows
%{
proc :: Int
proc = 1
}%
S :: Int
S <- 'a' { proc }
GRAMMAR
check_probe Arrows Arrows reject lexer

# A parser extension: a do block as an argument needs BlockArguments.
cat > "$probe/Block.hpeg" <<'GRAMMAR'
%module Probe.Language.Block
%language BlockArguments
S :: Maybe Int
S <- 'a' { id do pure 1 }
GRAMMAR
check_probe Block BlockArguments accept parser

# Turning off an extension of the base language: GHC2021 has
# ImportQualifiedPost, so the module reads without the line only if the tracer
# starts from GHC2021.
cat > "$probe/Qualified.hpeg" <<'GRAMMAR'
%module Probe.Language.Qualified
%language NoImportQualifiedPost
%{
import Data.Char qualified as C
}%
S :: Bool
S <- 'a' { C.isDigit '1' }
GRAMMAR
check_probe Qualified NoImportQualifiedPost reject parser

# A tracer that parses under the base flags only, as the tracer did before it
# applied the header pragmas, must fail the MagicHash probe.
mutant="$probe/mutant"
mkdir -p "$mutant"
cp "$scratch/PegTraceParser.hi" "$mutant/PegTraceParser.hi"
sed 's/state = initParserState (initParserOpts flags) buffer location/state = initParserState (initParserOpts base) buffer location/' \
  verification/TraceGeneratedModule.hs > "$mutant/TraceGeneratedModule.hs"
if cmp -s verification/TraceGeneratedModule.hs "$mutant/TraceGeneratedModule.hs"; then
  echo 'the mutation of the tracer changed nothing' >&2
  exit 1
fi
"$ghc" -package ghc -outputdir "$mutant" -c -fforce-recomp \
  -o "$mutant/TraceGeneratedModule.o" "$mutant/TraceGeneratedModule.hs" > "$mutant/build.log" 2>&1
"$ghc" -package ghc "$mutant/TraceGeneratedModule.o" "$scratch/PegTraceParser.o" \
  -o "$mutant/trace-generated-module" >> "$mutant/build.log" 2>&1
if "$mutant/trace-generated-module" "$libdir" "$probe/Magic.hs" > /dev/null 2>&1; then
  echo 'a tracer that ignores the LANGUAGE pragmas accepted the MagicHash probe' >&2
  exit 1
fi

printf 'Trace language: %s cabal files on GHC2021, %s LANGUAGE probes read by the tracer, 1 rejected mutation.\n' \
  "$cabals" "$probes"
