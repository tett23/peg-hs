#!/bin/sh
# Ties RenderPrinting.lean to Codegen.exprCodeU and to GHC 9.10.3's lexer:
# the printer's source is fixed, the reserved words of the model are those of
# Lexer.x, the model prints the same text as exprCodeU for every expression of
# the repository's grammars, each text occurs in the finalized module that
# generate returns, and GHC's lexer passes the parser the model's terminal IDs
# for each text. Pass check.sh's work directory: it must hold the compiled
# Lean modules up to RenderPrinting and the GHC parser trace driver
# (check-ghc-parser-trace.sh).
set -eu

cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
source_file=packages/peg-codegen/src/Peg/Codegen.hs
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# 1. The source that RenderPrinting models. A change to a span requires
# reviewing the model and the probe, then updating the hash.
span() {
  sed -n "$1" "$source_file" > "$work/span"
  [ -s "$work/span" ] || { echo "empty source span: $1" >&2; exit 1; }
  actual=$(git hash-object "$work/span")
  [ "$actual" = "$2" ] || { echo "changed source span $1: $actual" >&2; exit 1; }
}
span '/^exprCodeU ::/,/^      pure (f <> " (" <> e <> ")")$/p' f7d526a42ae7bf687b5aabcf401c438f2baf478a
span '/^itemStmt ::/,/^      else e$/p' fd3ee95a6fe7f76af715ac1b95f1e53e7b3635f4
span '/^passThroughOf ::/,/^          pure (s : rest, v)$/p' c94f42ee0eb42df0aeafcc226ae59274ed8b4485
span '/^doBlock ::/,/^doBlock stmts =/p' e909b59dee7b66c59cbb0fea655850b75e265ae9
span '/^fresh ::/,/^fresh =/p' 11f9fc1529e483db64680a257039e7562db4128f
span '/^ruleVar ::/,/^ruleVar n =/p' 149be80a6eaa923b3d72425db7fdc8415ea130a4
span '/^showT ::/,/^hsString =/p' 9e8c6710cb645353d64931875cf9e310aed29c1b

# 2. reservedWordsFM of GHC 9.10.3's Lexer.x is RenderPrinting.reservedWords.
lexer=${GHC_LEXER_X:-"$lean_objects/Lexer.x"}
digest=$(shasum -a 256 "$lexer" | cut -d ' ' -f 1)
[ "$digest" = bb643c1706c6f6745d3529f94eeace6396ce39e9fc10793afadbb667275920de ] || {
  echo 'GHC Lexer.x digest changed' >&2
  exit 1
}
awk '/^reservedWordsFM = listToUFM \$/ { on = 1; next } on && /^ *\]/ { exit } on' "$lexer" |
  sed -n 's/^[[:space:]]*\[\{0,1\}([[:space:]]*"\([^"]*\)".*/\1/p' > "$work/reserved-ghc"
[ "$(wc -l < "$work/reserved-ghc")" -gt 40 ] || { echo 'cannot read reservedWordsFM' >&2; exit 1; }

# 3. The probe: the real exprCodeU, and Peg.Codegen under another name for
# the functions it does not export.
sed -e 's/^module Peg.Codegen$/module CodegenInternal where/' -e '/^  ( Options (..)$/,/^  ) where$/d' \
  "$source_file" > "$work/CodegenInternal.hs"
grammars=$("${CABAL:-cabal}" exec -v0 -- runghc-9.10.3 -package=peg-grammar -package=directory -package=filepath \
  --ghc-arg=-i"$work" --ghc-arg=-Wall --ghc-arg=-Werror --ghc-arg=-Wno-unused-top-binds \
  verification/RenderPrintingProbe.hs "$work")

(cd verification &&
  LEAN_PATH="$work:$lean_objects" lean -DwarningAsError=true -R "$work" \
    -o "$work/RenderPrintingProbeCases.olean" "$work/RenderPrintingProbeCases.lean" &&
  LEAN_PATH="$work:$lean_objects" lean --run RenderPrintingProbe.lean reserved > "$work/reserved-lean" &&
  LEAN_PATH="$work:$lean_objects" lean --run RenderPrintingProbe.lean text > "$work/lean-text" &&
  LEAN_PATH="$work:$lean_objects" lean --run RenderPrintingProbe.lean lexids > "$work/lean-lexids")
diff -u "$work/reserved-ghc" "$work/reserved-lean"
diff -u "$work/haskell-text" "$work/lean-text"

# 4. GHC's lexer on the printed texts.
"$lean_objects/trace-generated-module" "$(ghc-9.10.3 --print-libdir)" "$work/P.hs" \
  > "$work/P.result" 2> "$work/P.trace"
[ "$(cat "$work/P.result")" = parsed-no-diagnostics ] || { echo 'GHC rejected the probe module' >&2; exit 1; }
sed -n 's/^LEXID //p' "$work/P.trace" > "$work/ghc-lexids"
diff -u "$work/lean-lexids" "$work/ghc-lexids"
printf 'Printing: %s; %s texts agree with exprCodeU and occur in the generated modules; %s terminal IDs agree with GHC 9.10.3; %s reserved words.\n' \
  "$grammars" "$(wc -l < "$work/lean-text" | tr -d ' ')" "$(wc -l < "$work/ghc-lexids" | tr -d ' ')" \
  "$(wc -l < "$work/reserved-lean" | tr -d ' ')"
