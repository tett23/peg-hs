#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass a temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
[ -f "$LEAN_PATH/Pragmas.olean" ] || { echo 'Pragmas.olean is missing' >&2; exit 1; }
peg=${PEG_HS:-$("${CABAL:-cabal}" list-bin exe:peg-hs)}
mkdir -p "$scratch"
(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderExpressionBoundary.olean" RenderExpressionBoundary.lean) \
  > "$scratch/RenderExpressionBoundary.log"
if grep -q 'sorryAx' "$scratch/RenderExpressionBoundary.log"; then
  cat "$scratch/RenderExpressionBoundary.log" >&2
  exit 1
fi

cat > "$scratch/ProbeQQ.hs" <<'SOURCE'
{-# LANGUAGE TemplateHaskell #-}
module ProbeQQ (qq) where
import Language.Haskell.TH.Quote
qq :: QuasiQuoter
qq = QuasiQuoter { quoteExp = \_ -> [| 'x' |], quotePat = undefined, quoteType = undefined, quoteDec = undefined }
SOURCE
cat > "$scratch/Comment.hpeg" <<'SOURCE'
%module Probe.Comment
%start Start
Start :: Char
Start <- . { 'x' -- a trailing comment
}
SOURCE
cat > "$scratch/ArgComment.hpeg" <<'SOURCE'
%module Probe.ArgComment
%start Start
K(v :: Char) :: Char
K <- . { v }
Start :: Char
Start <- K('x' -- a trailing comment
)
SOURCE
cat > "$scratch/Pragma.hpeg" <<'SOURCE'
%module Probe.Pragma
%start Start
Start :: Char
Start <- . { {-# SCC "mark" #-} 'x' }
SOURCE
cat > "$scratch/TypeComment.hpeg" <<'SOURCE'
%module Probe.TypeComment
%start Start
K(v :: Char -- type comment
) :: Char
K <- . { v }
Start :: Char
Start <- K('x')
SOURCE
cat > "$scratch/Layout.hpeg" <<'SOURCE'
%module Probe.Layout
%start Start
Start :: Char
Start <- . { let
  x = 'x'
  in x }
SOURCE
cat > "$scratch/Quasiquote.hpeg" <<'SOURCE'
%module Probe.Quasiquote
%language QuasiQuotes
%{
import ProbeQQ (qq)
}%
%start Start
Start :: Char
Start <- . { [qq|anything|] }
SOURCE

cat > "$scratch/FunctionField.hpeg" <<'SOURCE'
%module Probe.FunctionField
%deriving
Pair <- F F
F :: Int->Int
F <- 'x' { id }
SOURCE

cat > "$scratch/FieldComment.hpeg" <<'SOURCE'
%module Probe.FieldComment
%deriving
Pair <- F F
F :: Int -- field comment
F <- 'x' { 1 }
SOURCE

for name in Comment ArgComment TypeComment Pragma Layout Quasiquote FunctionField FieldComment; do
  "$peg" gen "$scratch/$name.hpeg" -o "$scratch/$name.hs" \
    > "$scratch/$name.generate.log"
  ghc-9.10.3 -fno-code -fforce-recomp \
    -odir "$scratch" -hidir "$scratch" \
    -i"$(pwd)/packages/peg-runtime/src" -i"$scratch" \
    "$scratch/$name.hs" > "$scratch/$name.ghc.log" 2>&1
done

# Show the regression test is sensitive to the line break that protects ')'.
awk '/-- a trailing comment/ {
       printf "%s", $0
       getline; getline; getline
       print $0
       next
     }
     { print }' "$scratch/ArgComment.hs" > "$scratch/ArgCommentBroken.hs"
if ghc-9.10.3 -fno-code -fforce-recomp \
    -odir "$scratch" -hidir "$scratch" \
    -i"$(pwd)/packages/peg-runtime/src" \
    "$scratch/ArgCommentBroken.hs" > "$scratch/ArgCommentBroken.ghc.log" 2>&1; then
  echo 'GHC accepted the removed line-comment boundary' >&2
  exit 1
fi
grep -q 'parse error on input' "$scratch/ArgCommentBroken.ghc.log" || {
  cat "$scratch/ArgCommentBroken.ghc.log" >&2
  exit 1
}
printf 'Fragment boundaries: 5 Lean theorems, 8 GHC compilations, 1 rejected newline mutation.\n'
