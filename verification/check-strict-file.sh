#!/bin/sh
set -eu
cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
source=../packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs
runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$source" > "$work/TranslatedStrictFile.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedStrictFile.olean" "$work/TranslatedStrictFile.lean"
lean -DwarningAsError=true -o "$work/SelfHostedFileProof.olean" SelfHostedFileProof.lean
lean -DwarningAsError=true -o "$work/StrictSpaceChar.olean" StrictSpaceChar.lean
lean -DwarningAsError=true -o "$work/StrictComment.olean" StrictComment.lean
lean -DwarningAsError=true -o "$work/StrictWhitespace.olean" StrictWhitespace.lean

# A different but supported call still translates; it must lose the File derivation.
sed "/^peg'rule'File =$/,/^$/s/PegRt.many (peg'rule'TopItem)/PegRt.many (peg'rule'Ws)/" \
  "$source" > "$work/ChangedStrictFile.hs"
runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$work/ChangedStrictFile.hs" > "$work/ChangedStrictFile.lean"
cat >> "$work/ChangedStrictFile.lean" <<'LEAN'
open PegHs.MetaExecution in
example : translatedStrictFile = (context false []).rules (startRule false) := by rfl
LEAN
if lean -DwarningAsError=true "$work/ChangedStrictFile.lean" > "$work/changed-strict-file.log" 2>&1; then
  echo 'accepted a different repeated rule in File' >&2
  exit 1
fi
grep -Fq 'Tactic `rfl` failed' "$work/changed-strict-file.log" || { cat "$work/changed-strict-file.log" >&2; exit 1; }
# A supported alternative may be re-ordered in the generated code.
# Translation must preserve that priority and disagree with the original grammar.
sed "/^peg'rule'TopOne =$/,/^$/{
  s/peg'rule'Verbatim/TEMP_ALTERNATIVE/
  s/peg'rule'Directive/peg'rule'Verbatim/
  s/TEMP_ALTERNATIVE/peg'rule'Directive/
}" "$source" > "$work/ChangedTopOne.hs"
runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$work/ChangedTopOne.hs" > "$work/ChangedTopOne.lean"
cat >> "$work/ChangedTopOne.lean" <<'LEAN'
open PegHs.MetaExecution in
example : translatedStrictTopOne = (context false []).rules 2 := by rfl
LEAN
if lean -DwarningAsError=true "$work/ChangedTopOne.lean" > "$work/changed-top-one.log" 2>&1; then
  echo 'accepted a different ordered choice in TopOne' >&2
  exit 1
fi
grep -Fq 'Tactic `rfl` failed' "$work/changed-top-one.log" || { cat "$work/changed-top-one.log" >&2; exit 1; }
