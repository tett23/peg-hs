#!/bin/sh
set -eu

cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean -DwarningAsError=true \
  -o "$work/ConcreteFileCertificates.olean" ConcreteFileCertificates.lean
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean --run CheckConcreteFileCertificates.lean \
  > "$work/first-top-item.actual"
sed -n '9,15p' ../packages/peg-grammar/grammar/Peg.hpeg \
  > "$work/first-top-item.source"
cmp "$work/first-top-item.source" "$work/first-top-item.actual"
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean --run CheckConcreteFileCertificates.lean syntax \
  > "$work/syntax-first-top-item.actual"
sed -n '9,15p' ../packages/peg-grammar/grammar/PegSyntax.hpeg \
  > "$work/syntax-first-top-item.source"
cmp "$work/syntax-first-top-item.source" "$work/syntax-first-top-item.actual"
LEAN_PATH=$work${LEAN_PATH:+:$LEAN_PATH} lean --run CheckConcreteFileCertificates.lean whitespace \
  > "$work/whitespace.actual"
for grammar in Peg PegSyntax; do
  head -n 8 "../packages/peg-grammar/grammar/$grammar.hpeg" > "$work/whitespace.source"
  cmp "$work/whitespace.source" "$work/whitespace.actual"
done
printf '2 kernel certificates and 2 source windows checked\n'
