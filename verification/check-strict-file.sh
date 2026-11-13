#!/bin/sh
set -eu
cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
runghc-9.10.3 -Werror ExtractVerbatimBody.hs ../packages/peg-grammar/src/Peg/Grammar/Assemble.hs \
  ../packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs \
  ../packages/peg-grammar/src/Peg/Grammar/SelfHostedSyntax.hs > "$work/TranslatedVerbatimBody.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedVerbatimBody.olean" "$work/TranslatedVerbatimBody.lean"
lean -DwarningAsError=true VerbatimValue.lean
runtime=../packages/peg-runtime/src/Peg/Runtime/Internal.hs
runghc-9.10.3 -Werror ExtractRuntimeChoice.hs "$runtime" > "$work/TranslatedRuntimeChoice.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedRuntimeChoice.olean" "$work/TranslatedRuntimeChoice.lean"
lean -DwarningAsError=true -o "$work/RuntimeChoiceProof.olean" RuntimeChoiceProof.lean
source=../packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs
runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$source" > "$work/TranslatedStrictFile.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedStrictFile.olean" "$work/TranslatedStrictFile.lean"
lean -DwarningAsError=true -o "$work/SelfHostedFileProof.olean" SelfHostedFileProof.lean
lean -DwarningAsError=true -o "$work/StrictSpaceChar.olean" StrictSpaceChar.lean
lean -DwarningAsError=true -o "$work/StrictInlineSpace.olean" StrictInlineSpace.lean
lean -DwarningAsError=true -o "$work/StrictIdentifier.olean" StrictIdentifier.lean
lean -DwarningAsError=true -o "$work/StrictDirective.olean" StrictDirective.lean
lean -DwarningAsError=true -o "$work/StrictComment.olean" StrictComment.lean
lean -DwarningAsError=true -o "$work/StrictWhitespace.olean" StrictWhitespace.lean
lean -DwarningAsError=true -o "$work/StrictWhitespaceScan.olean" StrictWhitespaceScan.lean
lean -DwarningAsError=true StrictParameterGuards.lean
lean -DwarningAsError=true -o "$work/StrictWhitespaceLexical.olean" StrictWhitespaceLexical.lean
lean -DwarningAsError=true -o "$work/DirectiveFailure.olean" DirectiveFailure.lean
lean -DwarningAsError=true -o "$work/DirectiveSuccess.olean" DirectiveSuccess.lean
lean -DwarningAsError=true -o "$work/DirectiveAssembly.olean" DirectiveAssembly.lean
lean -DwarningAsError=true DirectiveSequence.lean
lean -DwarningAsError=true -o "$work/DirectiveSourceDiagnostic.olean" DirectiveSourceDiagnostic.lean
sh check-directive-arity.sh "$work"

# Recognition is unchanged if File discards the collected values.
sed "/^peg'rule'File =$/,/^$/s/PegPrelude.pure peg'v0/PegPrelude.pure []/" "$source" > "$work/DroppedFileItems.hs"
if runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$work/DroppedFileItems.hs" > /dev/null 2>"$work/dropped-file-items.log"; then
  echo 'accepted a File action discarding its items' >&2
  exit 1
fi
grep -Fq 'unsupported or missing generated rule File' "$work/dropped-file-items.log"

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
sed "/^peg'rule'IdentStart =$/,/^$/s/isIdentStart (firstChar c)/isIdentChar (firstChar c)/" \
  "$source" > "$work/ChangedIdentStart.hs"
if runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$work/ChangedIdentStart.hs" > /dev/null 2>"$work/changed-ident-start.log"; then
  echo 'accepted the continuation predicate for the initial identifier character' >&2
  exit 1
fi
grep -Fq 'unsupported or missing generated rule IdentStart' "$work/changed-ident-start.log"
# The generated label message must also be preserved by the translation.
sed "/^peg'rule'Verbatim =$/,/^$/s/unterminated %{ block/incorrect diagnostic/" \
  "$source" > "$work/ChangedVerbatim.hs"
runghc-9.10.3 -Werror ExtractSelfHostedFile.hs "$work/ChangedVerbatim.hs" > "$work/ChangedVerbatim.lean"
cat >> "$work/ChangedVerbatim.lean" <<'LEAN'
open PegHs.MetaExecution in
example : translatedStrictVerbatim = (context false []).rules 11 := by rfl
LEAN
if lean -DwarningAsError=true "$work/ChangedVerbatim.lean" > "$work/changed-verbatim.log" 2>&1; then
  echo 'accepted a changed unterminated block diagnostic' >&2
  exit 1
fi
grep -Fq 'Tactic `rfl` failed' "$work/changed-verbatim.log" || { cat "$work/changed-verbatim.log" >&2; exit 1; }
