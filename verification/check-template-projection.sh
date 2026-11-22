#!/bin/sh
# root ADR 0097 I2: classification inputs must survive the template view.
set -eu
cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of compiled Lean modules}
shared_path="$lean_objects${LEAN_PATH:+:$LEAN_PATH}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
(cd verification && LEAN_PATH="$shared_path" lean -DwarningAsError=true \
  -o "$lean_objects/TemplateProjectionProof.olean" TemplateProjectionProof.lean)
for mutation in annotation constructor; do
  mutant="$work/$mutation"
  mkdir -p "$mutant"
  case "$mutation" in
    annotation) sed 's/annotation := r.annotation.map locNat/annotation := none/' \
      verification/PublicGeneration.lean > "$mutant/PublicGeneration.lean" ;;
    constructor) sed 's/constructor := a.constructor.map Prod.snd/constructor := none/' \
      verification/PublicGeneration.lean > "$mutant/PublicGeneration.lean" ;;
  esac
  cmp -s verification/PublicGeneration.lean "$mutant/PublicGeneration.lean" && exit 1
  (cd verification && LEAN_PATH="$shared_path" lean -DwarningAsError=true -R "$mutant" \
    -o "$mutant/PublicGeneration.olean" "$mutant/PublicGeneration.lean") > "$mutant/build.log" 2>&1 || {
    cat "$mutant/build.log" >&2; exit 1;
  }
  if (cd verification && LEAN_PATH="$mutant:$shared_path" lean -DwarningAsError=true \
    TemplateProjectionProof.lean) > "$mutant/rejected.log" 2>&1; then
    echo "root ADR 0097 I2: accepted discarded template $mutation" >&2; exit 1
  fi
  grep -E 'TemplateProjectionProof.lean:[0-9]+:[0-9]+: error: (Tactic|unsolved goals)' \
    "$mutant/rejected.log" > /dev/null || { cat "$mutant/rejected.log" >&2; exit 1; }
done
echo 'root ADR 0097 I2: template projection preserves annotations and constructors; 2 mutants rejected.'
