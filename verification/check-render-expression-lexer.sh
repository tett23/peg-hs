#!/bin/sh
set -eu

cd "$(dirname "$0")"
scratch=${1:?pass the shared temporary verification directory}
lexer=${GHC_LEXER_X:-}
if [ -z "$lexer" ]; then
  : "${GHC_SOURCE:?provide GHC_SOURCE or GHC_LEXER_X for the GHC lexer}"
  lexer="$scratch/Lexer.x"
  git -C "$GHC_SOURCE" show ghc-9.10.3-release:compiler/GHC/Parser/Lexer.x > "$lexer"
fi
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
[ -f "$LEAN_PATH/RenderExpression.olean" ] || {
  echo 'RenderExpression.olean is missing' >&2
  exit 1
}
[ -x "$scratch/trace-generated-module" ] || {
  echo 'GHC parser trace driver is missing' >&2
  exit 1
}

if command -v sha256sum >/dev/null 2>&1; then
  digest=$(sha256sum "$lexer" | cut -d ' ' -f 1)
else
  digest=$(shasum -a 256 "$lexer" | cut -d ' ' -f 1)
fi
[ "$digest" = bb643c1706c6f6745d3529f94eeace6396ce39e9fc10793afadbb667275920de ] || {
  echo 'GHC Lexer.x digest changed' >&2
  exit 1
}

for line in \
  '@varid     = $small $idchar*' \
  '@conid     = $large $idchar*' \
  '@qual = (@conid \.)+' \
  '@qvarid = @qual @varid' \
  '@qmdo   = @qual "mdo"' \
  '@qdo                                      { qdo_token ITdo }' \
  '@qmdo    / { ifExtension RecursiveDoBit } { qdo_token ITmdo }' \
  '@qdo    = @qual "do"' \
  '@qvarid                       { idtoken qvarid }' \
  '@varid                        { varid }' \
  '( "do",             ITdo Nothing,    0 )'; do
  grep -Fq "$line" "$lexer" || {
    echo "missing GHC lexer rule: $line" >&2
    exit 1
  }
done

lean -DwarningAsError=true -o "$scratch/RenderExpressionLexer.olean" \
  RenderExpressionLexer.lean > "$scratch/RenderExpressionLexer.log"
if grep -q 'sorryAx' "$scratch/RenderExpressionLexer.log"; then
  cat "$scratch/RenderExpressionLexer.log" >&2
  exit 1
fi

cat > "$scratch/RenderExpressionLexProbe.hs" <<'SOURCE'
module LexProbe where
x = PegRt.choice [peg'rule'Foo, PegRt.many (PegRt.anyChar)]
y = do { x; y }
SOURCE
"$scratch/trace-generated-module" "$(ghc-9.10.3 --print-libdir)" \
  "$scratch/RenderExpressionLexProbe.hs" \
  > "$scratch/RenderExpressionLexProbe.result" \
  2> "$scratch/RenderExpressionLexProbe.trace"
[ "$(cat "$scratch/RenderExpressionLexProbe.result")" = parsed-no-diagnostics ] || {
  echo 'GHC rejected lexical probe' >&2
  exit 1
}
grep '^token: ' "$scratch/RenderExpressionLexProbe.trace" |
  sed 's/^token: //' > "$scratch/RenderExpressionLexProbe.actual"
cat > "$scratch/RenderExpressionLexProbe.expected" <<'TOKENS'
ITmodule
ITconid "LexProbe"
ITwhere
ITvocurly
ITvarid "x"
ITequal
ITqvarid ("PegRt","choice")
ITobrack
ITvarid "peg'rule'Foo"
ITcomma
ITqvarid ("PegRt","many")
IToparen
ITqvarid ("PegRt","anyChar")
ITcparen
ITcbrack
ITsemi
ITvarid "y"
ITequal
ITdo Nothing
ITocurly
ITvarid "x"
ITsemi
ITvarid "y"
ITccurly
ITsemi
ITeof
TOKENS
diff -u "$scratch/RenderExpressionLexProbe.expected" \
  "$scratch/RenderExpressionLexProbe.actual"
printf 'GHC lexer source: 8 rules; ASCII class and delimiters: 11 Lean theorems; concrete probe: 26 tokens.\n'
