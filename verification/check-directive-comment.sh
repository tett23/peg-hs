#!/bin/sh
set -eu
cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
source=../packages/peg-grammar/src/Peg/Grammar/Assemble.hs
# Source of the mode switch, offset projection and whitespace stripping.
sed -n '/^directiveArg name raw =/p; /^directiveComment name raw$/,/^  where$/p; /^stringDirectives =/p' "$source" > "$work/directive-switch.actual"
cat > "$work/directive-switch.expected" <<'HS'
directiveArg name raw = T.strip (fst (directiveComment name raw))
directiveComment name raw
  | name == "env" = (raw, "")
  | name `elem` stringDirectives = T.splitAt (outside 0 (T.unpack raw)) raw
  | otherwise = T.break (== '#') raw
  where
stringDirectives = ["expect", "message"]
HS
cmp "$work/directive-switch.expected" "$work/directive-switch.actual"
lean -DwarningAsError=true -o "$work/DirectiveArgument.olean" DirectiveArgument.lean
runghc-9.10.3 -Werror ExtractDirectiveComment.hs "$source" > "$work/TranslatedDirectiveComment.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedDirectiveComment.olean" "$work/TranslatedDirectiveComment.lean"
lean -DwarningAsError=true -o "$work/DirectiveCommentProof.olean" DirectiveCommentProof.lean

# The quote opens a string in the real scanner. Translating a supported but
# incorrect outside-to-outside transition must change the result at '#'.
sed '/^    outside n =/,/^    inside n =/s/inside (n + 1) rest/outside (n + 1) rest/' "$source" > "$work/WrongDirective.hs"
runghc-9.10.3 -Werror ExtractDirectiveComment.hs "$work/WrongDirective.hs" > "$work/WrongDirective.lean"
cat >> "$work/WrongDirective.lean" <<'LEAN'
open PegHs.DirectiveArgument in
example : translatedOffset false 0 ['"', '#', '"'] = 3 := by decide
LEAN
if lean -DwarningAsError=true "$work/WrongDirective.lean" > "$work/wrong-directive.log" 2>&1; then
  echo 'accepted an incorrect quote transition' >&2
  exit 1
fi
grep -Fq 'decide' "$work/wrong-directive.log"
