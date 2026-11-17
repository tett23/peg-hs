#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
work=${1:?pass the Lean object directory}
runtime=packages/peg-runtime/src/Peg/Runtime/Internal.hs
assembly=packages/peg-grammar/src/Peg/Grammar/Assemble.hs
parser=packages/peg-grammar/src/Peg/Grammar/Parser.hs

# The generated entry runs the File rule under defaultConfig. runParser and
# defaultConfig are translated by ExtractRuntimeCore.hs, and the control
# combinators that propagate labels are proved in RuntimeCoreProof.lean
# (check-runtime-core.sh). The awk below translates parseTops; the text of
# its diagnostic is a parameter of the proofs.
sed -n '/^parse peg.input =/,/^$/p' packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs > "$work/public-entry.source"
printf '%s\n' "parse peg'input =" \
  "  Prelude.fst (PegRt.runParser peg'config (peg'newStore) peg'rule'File peg'input)" '' \
  > "$work/public-entry.expected"
diff -u "$work/public-entry.expected" "$work/public-entry.source"
grep -Fqx "peg'config = PegRt.defaultConfig" packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs

awk -f verification/translate-public-entry.awk "$runtime" "$parser" "$assembly" > "$work/TranslatedEntry.lean"
(cd verification && lean --root="$work" -DwarningAsError=true \
  -o "$work/TranslatedEntry.olean" "$work/TranslatedEntry.lean" &&
  lean -DwarningAsError=true -o "$work/PublicEntryProof.olean" PublicEntryProof.lean)
sed 's/Ok j x | j == ctxLen ctx/Ok j x | j <= ctxLen ctx/' "$runtime" > "$work/ChangedRuntime.hs"
if awk -f verification/translate-public-entry.awk "$work/ChangedRuntime.hs" "$parser" "$assembly" > /dev/null; then
  echo 'entry translation accepted a changed EOF guard' >&2
  exit 1
fi
sed 's/in Left \[Diagnostic (Loc 0 (posLine p) (posColumn p)) msg\]/in Left []/' "$parser" > "$work/ChangedParser.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$work/ChangedParser.hs" "$assembly" > /dev/null; then
  echo 'entry translation accepted an empty public diagnostic list' >&2
  exit 1
fi

sed 's/parseTops src >>= assemble/assemble src/' "$parser" > "$work/ChangedAssembly.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$work/ChangedAssembly.hs" "$assembly" > /dev/null; then
  echo 'entry translation accepted bypassing parseTops' >&2
  exit 1
fi

sed 's/es -> Left (sortOn diagLoc es)/es -> Left []/' "$assembly" > "$work/EmptyAssemblyErrors.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$parser" "$work/EmptyAssemblyErrors.hs" > /dev/null; then
  echo 'entry translation accepted discarding assembly diagnostics' >&2
  exit 1
fi

sed 's/Nothing -> single "module"/Nothing -> single "start"/' "$assembly" > "$work/ChangedModuleSelection.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$parser" "$work/ChangedModuleSelection.hs" > /dev/null; then
  echo 'entry translation accepted selecting the start rule as the module' >&2
  exit 1
fi

sed 's/(l, "library", _) <- directives/(l, "module", _) <- directives/' "$assembly" > "$work/ChangedLibraryLookup.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$parser" "$work/ChangedLibraryLookup.hs" > /dev/null; then
  echo 'entry translation accepted a changed library directive lookup' >&2
  exit 1
fi

sed 's/TDirective l n _ a <- items/TDirective l n _ a <- reverse items/' "$assembly" > "$work/ReversedDirectives.hs"
if awk -f verification/translate-public-entry.awk "$runtime" "$parser" "$work/ReversedDirectives.hs" > /dev/null; then
  echo 'entry translation accepted reversing top-level items' >&2
  exit 1
fi
