#!/bin/sh
set -eu

scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cabal=${CABAL:-cabal}
peg=$("$cabal" list-bin exe:peg-hs)

for fixture in Sum Indent Link RecoverVoidSyntax Extensions; do
  input="packages/peg-codegen/test/fixtures/$fixture.hpeg"
  grammar="$scratch/$fixture.hpeg"
  output="$scratch/$fixture.hs"
  if [ "$fixture" = Extensions ]; then
    awk '/^%language / && !added { print $0 ", NoTraditionalRecordSyntax"; added = 1; next } { print }' \
      "$input" > "$grammar"
  else
    awk '/^%module / { print; print "%language NoTraditionalRecordSyntax"; next } { print }' \
      "$input" > "$grammar"
  fi
  "$peg" gen --debug-entry "$grammar" -o "$output"
  if grep -Eq "^  \\{ peg'|\\{PegRt\\.cfgTabstop" "$output"; then
    echo "record syntax remains in $fixture" >&2
    exit 1
  fi
  grep -Fq "peg'withTabstop (PegRt.cfgTabstop peg'config) peg'cfg" "$output"
  if [ "$fixture" = Indent ]; then
    grep -Fq "peg'config = peg'withTabstop 2 PegRt.defaultConfig" "$output"
  fi
  "$cabal" exec -- ghc-9.10.3 -fno-code -fforce-recomp -package peg-runtime \
    -outputdir "$scratch" "$output"
  if [ "$fixture" = Indent ]; then
    mkdir -p "$scratch/Fixture"
    cp "$output" "$scratch/Fixture/Indent.hs"
    "$cabal" exec -- runghc-9.10.3 -i"$scratch" -package=peg-runtime \
      verification/NoRecordRuntime.hs
  fi
done
