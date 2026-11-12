#!/bin/sh
set -eu

: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"

for grammar in Peg PegSyntax; do
  source="packages/peg-grammar/grammar/$grammar.hpeg"
  [ "$(grep -c '^InlineSp <-' "$source")" -eq 1 ]
  [ "$(grep -c '^Comment <-' "$source")" -eq 1 ]
  grep -Fqx "InlineSp <- [ \\t]*" "$source"
  grep -Fqx "Comment <- '#' (!'\\n' .)*" "$source"
done

(cd verification && lean -DwarningAsError=true Lexical.lean)
