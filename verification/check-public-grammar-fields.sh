#!/bin/sh
# root ADR 0097 I3: retain the source fields needed by the renderer.
set -eu
cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of compiled Lean modules}
shared_path="$lean_objects${LEAN_PATH:+:$LEAN_PATH}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
(cd verification && LEAN_PATH="$shared_path" lean -DwarningAsError=true \
  -o "$lean_objects/PublicGrammarFieldsProof.olean" PublicGrammarFieldsProof.lean)
for mutation in exports env tabstop deriving type parameter; do
  mutant="$work/$mutation"
  mkdir -p "$mutant"
  case "$mutation" in
    exports) pattern='g.exports.map eLocated'; replacement='[]' ;;
    env) pattern='g.env.map eLocated'; replacement='none' ;;
    tabstop) pattern='g.tabstop.map fun p => .Located (eLoc p.1) p.2'; replacement='none' ;;
    deriving) pattern='g.derivingClasses.map fun p => .Located (eLoc p.1) (p.2.map eLocated)'; replacement='none' ;;
    type) pattern='(eLocated r.type)'; replacement='(.Located (eLoc ⟨0, 0, 0⟩) r.type.2)' ;;
    parameter) pattern='p.1 (eLocated p.2)'; replacement='p.1 (.Located (eLoc ⟨0, 0, 0⟩) p.2.2)' ;;
  esac
  # These are literal fragments, so escape sed's regular-expression dots.
  escaped=$(printf '%s' "$pattern" | sed 's/\./\\./g')
  sed "s/$escaped/$replacement/" verification/PublicGeneration.lean > "$mutant/PublicGeneration.lean"
  cmp -s verification/PublicGeneration.lean "$mutant/PublicGeneration.lean" && exit 1
  (cd verification && LEAN_PATH="$shared_path" lean -DwarningAsError=true -R "$mutant" \
    -o "$mutant/PublicGeneration.olean" "$mutant/PublicGeneration.lean") > "$mutant/build.log" 2>&1 || {
    cat "$mutant/build.log" >&2; exit 1;
  }
  if (cd verification && LEAN_PATH="$mutant:$shared_path" lean -DwarningAsError=true \
    PublicGrammarFieldsProof.lean) > "$mutant/rejected.log" 2>&1; then
    echo "root ADR 0097 I3: accepted discarded grammar field $mutation" >&2; exit 1
  fi
  grep -E 'PublicGrammarFieldsProof.lean:[0-9]+:[0-9]+: error: (Tactic|unsolved goals)' \
    "$mutant/rejected.log" > /dev/null || { cat "$mutant/rejected.log" >&2; exit 1; }
done
echo 'root ADR 0097 I3: renderer input fields preserved; 6 mutants rejected.'
