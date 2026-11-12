#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass a temporary output directory}
happy=${HAPPY:-happy}
ghc=${GHC:-ghc-9.10.3}
peg=${PEG_HS:-}

[ "$($ghc --numeric-version)" = 9.10.3 ] || {
  echo 'GHC 9.10.3 is required' >&2
  exit 1
}
[ "$($happy --numeric-version)" = 2.1.7 ] || {
  echo 'Happy 2.1.7 is required' >&2
  exit 1
}
if [ -z "$peg" ]; then
  peg=$("${CABAL:-cabal}" list-bin exe:peg-hs)
fi
mkdir -p "$scratch"

if [ -n "${GHC_PARSER_Y:-}" ]; then
  cp "$GHC_PARSER_Y" "$scratch/Parser.y"
else
  : "${GHC_SOURCE:?set GHC_PARSER_Y to Parser.y or GHC_SOURCE to a ghq checkout of ghc/ghc}"
  git -C "$GHC_SOURCE" show ghc-9.10.3-release:compiler/GHC/Parser.y > "$scratch/Parser.y"
fi
digest=$(shasum -a 256 "$scratch/Parser.y" | cut -d ' ' -f 1)
[ "$digest" = 331304d8f4007fc7c329e48d56f98e0ebe502bc51b1b443d0ec923febca83952 ] || {
  echo "unexpected GHC Parser.y SHA-256: $digest" >&2
  exit 1
}

"$happy" -agc --strict -i"$scratch/Parser.info" -d "$scratch/Parser.y" -o "$scratch/Parser.generated.hs"
[ "$(grep -c '^module GHC.Parser$' "$scratch/Parser.generated.hs")" -eq 1 ] || {
  echo 'the generated parser module declaration changed' >&2
  exit 1
}
sed 's/^module GHC.Parser$/module PegTraceParser/' "$scratch/Parser.generated.hs" > "$scratch/PegTraceParser.hs"
"$ghc" -package ghc -c -fforce-recomp -outputdir "$scratch" "$scratch/PegTraceParser.hs"
"$ghc" -package ghc -i"$scratch" -c -fforce-recomp -o "$scratch/TraceGeneratedModule.o" \
  verification/TraceGeneratedModule.hs
"$ghc" -package ghc "$scratch/TraceGeneratedModule.o" "$scratch/PegTraceParser.o" \
  -o "$scratch/trace-generated-module"
libdir=$("$ghc" --print-libdir)

for grammar in Peg PegSyntax; do
  "$peg" gen "packages/peg-grammar/grammar/$grammar.hpeg" -o "$scratch/$grammar.hs"
  "$scratch/trace-generated-module" "$libdir" "$scratch/$grammar.hs" 2> "$scratch/$grammar.trace" \
    > "$scratch/$grammar.result"
  [ "$(cat "$scratch/$grammar.result")" = parsed-no-diagnostics ] || {
    echo "$grammar: GHC parser did not finish cleanly" >&2
    exit 1
  }
  [ "$(head -n 1 "$scratch/$grammar.trace")" != LOCAL ] || {
    echo "$grammar: local probe marker leaked into the trace" >&2
    exit 1
  }
  grep -q '^state: 0,' "$scratch/$grammar.trace" || {
    echo "$grammar: the Happy trace has no initial state" >&2
    exit 1
  }
  grep -q 'action: accept\.' "$scratch/$grammar.trace" || {
    echo "$grammar: the Happy trace has no accept action" >&2
    exit 1
  }
  grep -q '{-# LINE ' "$scratch/$grammar.hs" || {
    echo "$grammar: the generated module has no LINE pragma" >&2
    exit 1
  }
  printf '%s: %s trace lines, accepted without diagnostics\n' "$grammar" "$(wc -l < "$scratch/$grammar.trace" | tr -d ' ')"
done
printf 'GHC 9.10.3, Happy 2.1.7, Parser.y SHA-256 %s\n' "$digest"
