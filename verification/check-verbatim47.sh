#!/bin/sh
set -eu

cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean -DwarningAsError=true \
  -o "$work/VerbatimChunks.olean" VerbatimChunks.lean
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean -DwarningAsError=true \
  -o "$work/Verbatim47Data.olean" Verbatim47Data.lean
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean --run CheckVerbatim47Data.lean \
  > "$work/verbatim47.actual"
for grammar in Peg PegSyntax; do
  sed -n '/^%{$/,/^}%$/p' "../packages/peg-grammar/grammar/$grammar.hpeg" \
    > "$work/verbatim47.source"
  printf '\n' >> "$work/verbatim47.source"
  cmp "$work/verbatim47.source" "$work/verbatim47.actual"
done
printf '1 kernel delimiter certificate and 2 source blocks checked\n'
