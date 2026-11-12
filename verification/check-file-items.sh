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
lean -DwarningAsError=true --run SplitMetaFile.lean \
  ../packages/peg-grammar/grammar/Peg.hpeg \
  ../packages/peg-grammar/grammar/PegSyntax.hpeg "$item_work" \
  > "$item_work/manifest.log"

item_count=0
for source in "$item_work"/PegItem*.lean "$item_work"/SyntaxItem*.lean; do
  case "$source" in */PegItem47.lean|*/SyntaxItem47.lean) continue;; esac
  lean -DwarningAsError=true -R "$item_work" \
    -o "${source%.lean}.olean" "$source"
  item_count=$((item_count + 1))
done
[ "$item_count" -eq 337 ]

for grammar in Peg Syntax; do
  lean -DwarningAsError=true -R "$item_work" \
    -o "$item_work/${grammar}Pieces.olean" "$item_work/${grammar}Pieces.lean"
done
lean -DwarningAsError=true -R "$item_work" --run CheckItemSources.lean

step_count=0
for source in "$item_work"/PegStep*.lean "$item_work"/SyntaxStep*.lean; do
  lean -DwarningAsError=true -R "$item_work" \
    -o "${source%.lean}.olean" "$source"
  step_count=$((step_count + 1))
done
[ "$step_count" -eq 339 ]

for grammar in Peg Syntax; do
  case "$grammar" in Peg) total=143;; Syntax) total=196;; esac
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
lean -DwarningAsError=true CertifiedPublicFiles.lean
printf '%s local certificates, %s full-input steps, 2 FileResult proofs checked\n' \
  "$item_count" "$step_count"
