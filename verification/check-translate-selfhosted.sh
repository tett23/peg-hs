#!/bin/sh
# ADR 0097: the generated parser Peg.Grammar.SelfHosted is translated into
# Lean from GHC's syntax tree by TranslateHaskell.hs (no reading of its text),
# with the runtime table of HsPegRuntime.lean, and SelfHostedTranslatedProof
# shows the values of its start rules File, TopItem and TopOne. Pass the
# directory of the compiled Lean modules (check.sh's work directory, with
# HsPrelude, AssembleTranslated and TranslatedRuntimeCore compiled); the
# script writes PositionTranslated, TranslatedRuntimeForms, HsPegRuntime,
# SelfHostedTranslated and the proof there.
#
# 1. Peg.Runtime.Position (the line and column of `here`) is translated by
#    TranslateHaskell.hs (translate-position.hints).
# 2. The runtime forms that the generated code uses around the combinators
#    (capture, predicate, withCol, getOffset, spanFrom) are translated by
#    ExtractRuntimeCore.hs, as the rest of the runtime.
# 3. SelfHosted.hs is translated (translate-selfhosted.hints): its 59 rules,
#    the functions of its header, and the functions of Peg.Grammar.Assemble
#    from the translation of check-translate-assemble.sh.
#
# Mutants: three changes of SelfHosted.hs outside the translator's subset (a
# tuple section, a runtime function outside the table, a library function
# outside the table) stop the translation; two changes that translate and
# compile (TopOne's alternatives reordered, File returning no items) are
# rejected by the proof.
set -eu

cd "$(dirname "$0")/.."
lean_objects=${1:?pass the directory of the compiled Lean modules}
ghc=${GHC:-ghc-9.10.3}
[ "$($ghc --numeric-version)" = 9.10.3 ] || {
  echo 'GHC 9.10.3 is required' >&2
  exit 1
}
libdir=$("$ghc" --print-libdir)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

mkdir -p "$work/build"
# The record updates of GHC's syntax tree miss its extension constructors.
"$ghc" -package ghc -O0 -Wall -Werror -Wno-incomplete-record-updates -outputdir "$work/build" \
  verification/TranslateHaskell.hs -o "$work/translate" > "$work/build.log" 2>&1 || {
  cat "$work/build.log" >&2
  exit 1
}

compile() {
  (cd verification && LEAN_PATH="$lean_objects" lean -DwarningAsError=true -R "$(dirname "$1")" \
    -o "$lean_objects/$(basename "$1" .lean).olean" "$1")
}

# 1. Positions.
"$work/translate" "$libdir" packages/peg-runtime/src packages/peg-runtime/src/Peg/Runtime/Position.hs \
  PositionTranslated verification/translate-position.hints posIn lineIndex > "$lean_objects/PositionTranslated.lean"
compile "$lean_objects/PositionTranslated.lean"

# 2. The runtime forms, and the runtime table.
runghc-9.10.3 -Werror verification/ExtractRuntimeCore.hs packages/peg-runtime/src/Peg/Runtime/Internal.hs forms \
  > "$lean_objects/TranslatedRuntimeForms.lean"
compile "$lean_objects/TranslatedRuntimeForms.lean"
compile "$PWD/verification/HsPegRuntime.lean"

# root ADR 0097 I3: the generated runtime table and its abstraction proofs
# must coexist in Audit.lean without duplicate declarations.
cat > "$lean_objects/RuntimeFormsImportCheck.lean" <<'LEAN'
import RuntimeForms
import HsPegRuntime
LEAN
compile "$lean_objects/RuntimeFormsImportCheck.lean"

# 3. The generated parser.
translate() {
  "$work/translate" "$libdir" "$1/peg-grammar/src:$1/peg-runtime/src" \
    "$1/peg-grammar/src/Peg/Grammar/SelfHosted.hs" SelfHostedTranslated verification/translate-selfhosted.hints \
    "peg'rule'File"
}
mkdir -p "$work/src"
cp -R packages/peg-grammar packages/peg-runtime "$work/src/"
translate "$work/src" > "$lean_objects/SelfHostedTranslated.lean"
compile "$lean_objects/SelfHostedTranslated.lean"
compile "$PWD/verification/SelfHostedTranslatedProof.lean"

# 4. Mutants.
source=packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs
mutant() {
  rm -rf "$work/mutant"
  mkdir -p "$work/mutant"
  cp -R packages/peg-grammar packages/peg-runtime "$work/mutant/"
  sed "$1" "$source" > "$work/mutant/peg-grammar/src/Peg/Grammar/SelfHosted.hs"
  if cmp -s "$source" "$work/mutant/peg-grammar/src/Peg/Grammar/SelfHosted.hs"; then
    echo "the mutant $2 changes nothing" >&2
    exit 1
  fi
}
rejected=0
untranslated() {
  if translate "$work/mutant" > "$work/mutant.lean" 2> "$work/mutant.err"; then
    echo "the translator took $1" >&2
    exit 1
  fi
  grep -q "$2" "$work/mutant.err" || {
    cat "$work/mutant.err" >&2
    exit 1
  }
  rejected=$((rejected + 1))
}
mutant "/^peg'rule'File =\$/,/^\$/s/PegPrelude.pure peg'v0\$/PegPrelude.pure (fst ((, ()) peg'v0))/" tuple-section
untranslated 'a tuple section' 'unsupported: a tuple section'
mutant "/^peg'rule'File =\$/,/^\$/s/PegRt.notP (PegRt.anyChar)/PegRt.notP (PegRt.voidP PegRt.anyChar)/" runtime
untranslated 'a runtime function outside its table' 'Peg.Runtime.Internal.voidP outside the runtime table'
mutant "s/^firstChar = T.foldr const ' '\$/firstChar = T.foldl (flip const) ' '/" library
untranslated 'a library function outside its table' 'unsupported: the name Data.Text.foldl'
unproved() {
  translate "$work/mutant" > "$work/mutant/SelfHostedTranslated.lean"
  mkdir -p "$work/mutant/olean"
  (cd verification &&
    LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true -R "$work/mutant" \
      -o "$work/mutant/olean/SelfHostedTranslated.olean" "$work/mutant/SelfHostedTranslated.lean")
  if (cd verification && LEAN_PATH="$work/mutant/olean:$lean_objects" lean -DwarningAsError=true \
    SelfHostedTranslatedProof.lean > "$work/mutant-proof.log" 2>&1); then
    echo "the proof took $1" >&2
    exit 1
  fi
  grep -q "$2" "$work/mutant-proof.log" || {
    cat "$work/mutant-proof.log" >&2
    exit 1
  }
  rejected=$((rejected + 1))
}
mutant "/^peg'rule'TopOne =\$/,/^\$/{
  s/peg'rule'Verbatim/TEMP_ALTERNATIVE/
  s/peg'rule'Directive/peg'rule'Verbatim/
  s/TEMP_ALTERNATIVE/peg'rule'Directive/
}" top-one-order
unproved 'TopOne with its alternatives reordered' "peg'memo'TopOne"
mutant "/^peg'rule'File =\$/,/^\$/s/PegPrelude.pure peg'v0\$/PegPrelude.pure []/" file-items
unproved 'File without its items' "peg'memo'File"
printf 'SelfHosted.hs translated from the GHC syntax tree; %s mutants rejected.\n' "$rejected"
