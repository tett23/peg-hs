#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass a temporary verification directory}
peg=${PEG_HS:-$("${CABAL:-cabal}" list-bin exe:peg-hs)}
lexer=${GHC_LEXER_X:?set GHC_LEXER_X to pinned GHC 9.10.3 Lexer.x}
mkdir -p "$scratch"

if command -v sha256sum >/dev/null 2>&1; then
  digest=$(sha256sum "$lexer" | cut -d ' ' -f 1)
else
  digest=$(shasum -a 256 "$lexer" | cut -d ' ' -f 1)
fi
[ "$digest" = bb643c1706c6f6745d3529f94eeace6396ce39e9fc10793afadbb667275920de ] || {
  echo 'GHC Lexer.x digest changed' >&2
  exit 1
}

invalid=0
for op in '..' '::' '=' '\' '|' '<-' '->' '=>'; do
  printf '%%module Probe.Operator\n%%export (%s)\nStart <- '\''a'\''\n' "$op" \
    > "$scratch/Operator.hpeg"
  if "$peg" gen "$scratch/Operator.hpeg" -o "$scratch/Operator.hs" \
      > "$scratch/Operator.log" 2>&1; then
    echo "peg-hs accepted GHC reserved operator $op" >&2
    exit 1
  fi
  grep -Fq '%export expects export items' "$scratch/Operator.log" || {
    cat "$scratch/Operator.log" >&2
    exit 1
  }
  invalid=$((invalid + 1))
done
for op in '-<' '>-' '-<<' '>>-'; do
  printf '%%module Probe.Operator\n%%language Arrows\n%%export (%s)\nStart <- '\''a'\''\n' "$op" \
    > "$scratch/Operator.hpeg"
  if "$peg" gen "$scratch/Operator.hpeg" -o "$scratch/Operator.hs" \
      > "$scratch/Operator.log" 2>&1; then
    echo "peg-hs accepted Arrows reserved operator $op" >&2
    exit 1
  fi
  grep -Fq '%export expects export items' "$scratch/Operator.log" || {
    cat "$scratch/Operator.log" >&2
    exit 1
  }
  invalid=$((invalid + 1))
done

valid=0
for op in '-<' '>-' '-<<' '>>-'; do
  printf '%%module Probe.Operator\n%%export (%s)\n%%{\n(%s) = const\n}%%\nStart <- '\''a'\''\n' "$op" "$op" \
    > "$scratch/Operator.hpeg"
  "$peg" gen "$scratch/Operator.hpeg" -o "$scratch/Operator.hs" \
    > "$scratch/Operator.log"
  ghc-9.10.3 -fno-code -fforce-recomp \
    -odir "$scratch" -hidir "$scratch" \
    -i"$(pwd)/packages/peg-runtime/src" \
    "$scratch/Operator.hs" > "$scratch/Operator.ghc.log" 2>&1
  valid=$((valid + 1))
done
cat > "$scratch/Operator.hpeg" <<'SOURCE'
%module Probe.Operator
%language Arrows, NoArrows
%export (-<)
%{
(-<) = const
}%
Start <- 'a'
SOURCE
"$peg" gen "$scratch/Operator.hpeg" -o "$scratch/Operator.hs" \
  > "$scratch/Operator.log"
ghc-9.10.3 -fno-code -fforce-recomp \
  -odir "$scratch" -hidir "$scratch" \
  -i"$(pwd)/packages/peg-runtime/src" \
  "$scratch/Operator.hs" > "$scratch/Operator.ghc.log" 2>&1
valid=$((valid + 1))
printf 'Export operators: %s reserved inputs rejected, %s permitted modules compiled.\n' \
  "$invalid" "$valid"
