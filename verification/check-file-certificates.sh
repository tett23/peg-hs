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
printf '1 kernel certificate and 1 source window checked\n'
