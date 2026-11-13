#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass a temporary verification directory}
peg=${PEG_HS:-$("${CABAL:-cabal}" list-bin exe:peg-hs)}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
for module in Header RenderExpression RenderModuleGHC; do
  [ -f "$LEAN_PATH/$module.olean" ] || {
    echo "$module.olean is missing" >&2
    exit 1
  }
done
mkdir -p "$scratch"
lexer=${GHC_LEXER_X:-"$LEAN_PATH/Lexer.x"}
cat verification/CheckModuleNameChars.hs > "$scratch/CheckModuleNameChars.hs"
sed -n '/^adjustChar ::/,/^[ ]*_other *-> non_graphic/p' "$lexer" >> "$scratch/CheckModuleNameChars.hs"
runghc-9.10.3 "$scratch/CheckModuleNameChars.hs"

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderModuleNames.olean" RenderModuleNames.lean) \
  > "$scratch/RenderModuleNames.log"
if grep -q 'sorryAx' "$scratch/RenderModuleNames.log"; then
  cat "$scratch/RenderModuleNames.log" >&2
  exit 1
fi

cat > "$scratch/RenderModuleNames.expected" <<'SOURCE'
entryName :: Maybe Text -> Text
entryName = ("parse" <>) . maybe "" id
SOURCE
sed -n '/^entryName ::/,/^entryName =/p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderModuleNames.actual"
diff -u "$scratch/RenderModuleNames.expected" "$scratch/RenderModuleNames.actual"
cat > "$scratch/RenderModuleNames.expected" <<'SOURCE'
ruleVar :: Text -> Text
ruleVar n = "peg'rule'" <> n
SOURCE
sed -n '/^ruleVar ::/,/^ruleVar n =/p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderModuleNames.actual"
diff -u "$scratch/RenderModuleNames.expected" "$scratch/RenderModuleNames.actual"

cat > "$scratch/InvalidQdo.hpeg" <<'SOURCE'
%module Probe.InvalidQdo
%export Q.do
Start :: ()
Start <- 'a'
SOURCE
cat > "$scratch/InvalidQmdo.hpeg" <<'SOURCE'
%module Probe.InvalidQmdo
%language RecursiveDo
%export Q.mdo
Start :: ()
Start <- 'a'
SOURCE
for name in InvalidQdo InvalidQmdo; do
  if "$peg" gen "$scratch/$name.hpeg" -o "$scratch/$name.hs" \
      > "$scratch/$name.log" 2>&1; then
    echo "$name: peg-hs accepted a GHC keyword in the export list" >&2
    exit 1
  fi
  grep -Fq '%export expects export items' "$scratch/$name.log" || {
    cat "$scratch/$name.log" >&2
    exit 1
  }
done

cat > "$scratch/Q.hs" <<'SOURCE'
module Q (mdo) where
mdo :: ()
mdo = ()
SOURCE
cat > "$scratch/QualifiedMdo.hpeg" <<'SOURCE'
%module Probe.QualifiedMdo
%language QualifiedDo
%export Q.mdo
%{
import qualified Q
}%
Start :: ()
Start <- 'a'
SOURCE
cat > "$scratch/UnicodeNames.hpeg" <<'SOURCE'
%module Probe.UnicodeNames
%start do
do <- where
where <- Δ
Δ <- 漢
漢 <- A'
A' <- 'a'
SOURCE
cat > "$scratch/UnicodeModule.hpeg" <<'SOURCE'
%module Δ.Ω'
Start <- 'a'
SOURCE
for name in QualifiedMdo UnicodeNames UnicodeModule; do
  "$peg" gen "$scratch/$name.hpeg" -o "$scratch/$name.hs" \
    > "$scratch/$name.generate.log"
  ghc-9.10.3 -fno-code -fforce-recomp \
    -odir "$scratch" -hidir "$scratch" \
    -i"$(pwd)/packages/peg-runtime/src" -i"$scratch" \
    "$scratch/$name.hs" > "$scratch/$name.ghc.log" 2>&1
done

printf 'Module names and exports: 5 Lean theorems, 1114112 character classifications, 2 invalid inputs rejected, 3 generated modules compiled.\n'
