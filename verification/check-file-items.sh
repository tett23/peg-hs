#!/bin/sh
set -eu

cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
mkdir -p "$work/item-certificates"
item_work=$work/item-certificates
export LEAN_PATH="$item_work:$work${LEAN_PATH:+:$LEAN_PATH}"

./check-verbatim47.sh "$work"
lean -DwarningAsError=true -o "$work/VerbatimItem47.olean" VerbatimItem47.lean
lean -DwarningAsError=true -o "$work/ItemSourceSplit.olean" ItemSourceSplit.lean
# Peg: Peg.hpeg under the Peg grammar. Syntax: PegSyntax.hpeg under its own
# rule table. SyntaxAsPeg: PegSyntax.hpeg under the Peg grammar, which is the
# grammar parseTops uses for every hpeg file (ADR 0097 invariant 1).
lean -DwarningAsError=true --run SplitMetaFile.lean \
  ../packages/peg-grammar/grammar/Peg.hpeg \
  ../packages/peg-grammar/grammar/PegSyntax.hpeg "$item_work" \
  > "$item_work/manifest.log"

# Item 47 is the shared verbatim block, certified once by VerbatimItem47.
item_count=0
for source in "$item_work"/PegItem*.lean "$item_work"/SyntaxItem*.lean \
    "$item_work"/SyntaxAsPegItem*.lean; do
  case "$source" in */PegItem47.lean|*/SyntaxItem47.lean|*/SyntaxAsPegItem47.lean) continue;; esac
  lean -DwarningAsError=true -R "$item_work" \
    -o "${source%.lean}.olean" "$source"
  item_count=$((item_count + 1))
done
[ "$item_count" -eq 532 ]

for grammar in Peg Syntax SyntaxAsPeg; do
  lean -DwarningAsError=true -R "$item_work" \
    -o "$item_work/${grammar}Pieces.olean" "$item_work/${grammar}Pieces.lean"
done
lean -DwarningAsError=true -R "$item_work" --run CheckItemSources.lean

step_count=0
for source in "$item_work"/PegStep*.lean "$item_work"/SyntaxStep*.lean \
    "$item_work"/SyntaxAsPegStep*.lean; do
  lean -DwarningAsError=true -R "$item_work" \
    -o "${source%.lean}.olean" "$source"
  step_count=$((step_count + 1))
done
[ "$step_count" -eq 535 ]

for grammar in Peg Syntax SyntaxAsPeg; do
  case "$grammar" in Peg) total=143;; Syntax|SyntaxAsPeg) total=196;; esac
  start=$(( ((total - 1) / 20) * 20 ))
  while [ "$start" -ge 0 ]; do
    lean -DwarningAsError=true -R "$item_work" \
      -o "$item_work/${grammar}Chain${start}.olean" \
      "$item_work/${grammar}Chain${start}.lean"
    start=$((start - 20))
  done
  lean -DwarningAsError=true -R "$item_work" \
    -o "$item_work/${grammar}Full.olean" "$item_work/${grammar}Full.lean"
done
lean -DwarningAsError=true -o "$work/CertifiedPublicFiles.olean" CertifiedPublicFiles.lean
printf '%s local certificates, %s full-input steps, 3 FileResult proofs checked\n' \
  "$item_count" "$step_count"
