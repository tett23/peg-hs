#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
# Include the actual start rule, runtime EOF check and public diagnostic mapping.
digest=$({
  sed -n '/^parse peg.input =/,/^$/p' packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs
  sed -n '/^runParser cfg mkStore start input =/,/^  pure (res, s)$/p' packages/peg-runtime/src/Peg/Runtime/Internal.hs
  sed -n -e '/^parseGrammar src =/p' -e '/^parseTops src =/,/^      \[\] -> Nothing$/p' packages/peg-grammar/src/Peg/Grammar/Parser.hs
} | shasum -a 256 | cut -d ' ' -f 1)
[ "$digest" = 773092a6a37731bbf7066869360e8d6ea4452ccb914b32daa975672a81814caf ] || { echo 'review the public parse entry proof' >&2; exit 1; }

control=$(sed -n -e '/^instance Monad (P r s)/,/^$/p' -e '/^choice ps =/,/^$/p' \
  -e '/^many p =/,/^$/p' -e '/^skipMany p =/,/^$/p' -e '/^optional p =/,/^$/p' \
  -e '/^andP p =/,/^$/p' -e '/^notP p =/,/^$/p' -e '/^labeledWith wrap /,/^$/p' \
  packages/peg-runtime/src/Peg/Runtime/Internal.hs | shasum -a 256 | cut -d ' ' -f 1)
[ "$control" = a4040f9c6cec51f3fd7cd3a2ad3564bd47d17a65693c98c9673c70938a633ce7 ] || { echo 'review strict label propagation' >&2; exit 1; }

work=${1:?pass the Lean object directory}
runtime=packages/peg-runtime/src/Peg/Runtime/Internal.hs
parser=packages/peg-grammar/src/Peg/Grammar/Parser.hs
awk -f verification/translate-public-entry.awk "$runtime" "$parser" > "$work/TranslatedEntry.lean"
(cd verification && lean --root="$work" -DwarningAsError=true \
  -o "$work/TranslatedEntry.olean" "$work/TranslatedEntry.lean" &&
  lean -DwarningAsError=true -o "$work/PublicEntryProof.olean" PublicEntryProof.lean)
sed 's/Ok j x | j == ctxLen ctx/Ok j x | j <= ctxLen ctx/' "$runtime" > "$work/ChangedRuntime.hs"
if awk -f verification/translate-public-entry.awk "$work/ChangedRuntime.hs" "$parser" > /dev/null; then
  echo 'entry translation accepted a changed EOF guard' >&2
  exit 1
fi
sed 's/in Left \[Diagnostic (Loc 0 (posLine p) (posColumn p)) msg\]/in Left []/' "$parser" > "$work/ChangedParser.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$work/ChangedParser.hs" > /dev/null; then
  echo 'entry translation accepted an empty public diagnostic list' >&2
  exit 1
fi
