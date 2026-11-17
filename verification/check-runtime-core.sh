#!/bin/sh
# Translate the strict runtime of Peg.Runtime.Internal into Lean and check
# the memo, control, terminal and entry theorems about the translation.
set -eu
cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
runtime=../packages/peg-runtime/src/Peg/Runtime/Internal.hs

lean -DwarningAsError=true -o "$work/RuntimeCore.olean" RuntimeCore.lean
runghc-9.10.3 -Werror ExtractRuntimeCore.hs "$runtime" > "$work/TranslatedRuntimeCore.lean"
lean -DwarningAsError=true -R "$work" -o "$work/TranslatedRuntimeCore.olean" "$work/TranslatedRuntimeCore.lean"
lean -DwarningAsError=true -o "$work/RuntimeCoreProof.olean" RuntimeCoreProof.lean

# A line that the dictionary does not know stops the translation.
reject() {
  sed "$2" "$runtime" > "$work/RejectedRuntime.hs"
  if runghc-9.10.3 -Werror ExtractRuntimeCore.hs "$work/RejectedRuntime.hs" > /dev/null 2> "$work/rejected.log"; then
    echo "runtime translation accepted $1" >&2
    exit 1
  fi
  grep -Eq 'unsupported line in|runtime declaration changed' "$work/rejected.log" || {
    cat "$work/rejected.log" >&2
    exit 1
  }
}
reject 'a changed EOF check' 's/Ok j x | j == ctxLen ctx/Ok j x | j <= ctxLen ctx/'
reject 'dropped seed dependencies' 's/writeSTRef (ctxDeps c) (IS.union savedDeps d)/writeSTRef (ctxDeps c) savedDeps/'
reject 'a choice that stops at an ordinary failure' 's/          Fail -> restoreErrors c saved >> go rest/          Fail -> pure Fail/'
reject 'a memo hit that evaluates the body' 's/        Just e -> replay c e/        Just _ -> (\\(r, _, _, _) -> r) <$> evalBody c name i body/'
reject 'a changed Entry' 's/^data Entry a = Entry !(Res a) !Failure !ErrSlice !IntSet$/data Entry a = Entry !(Res a) !Failure !ErrSlice/'

# A deleted line still translates. The proofs must then fail.
mkdir -p "$work/mutant"
lose() {
  awk -v header="$2" -v line="$3" '
    index($0, header) == 1 { inside = 1 }
    inside && $0 == "" { inside = 0 }
    inside && $0 == line { dropped++; next }
    { print }
    END { if (dropped != 1) exit 1 }
  ' "$runtime" > "$work/MutantRuntime.hs"
  runghc-9.10.3 -Werror ExtractRuntimeCore.hs "$work/MutantRuntime.hs" > "$work/mutant/TranslatedRuntimeCore.lean"
  # Run from verification/ so that elan selects lean-toolchain.
  LEAN_PATH="$work" lean -R "$work/mutant" -o "$work/mutant/TranslatedRuntimeCore.olean" \
    "$work/mutant/TranslatedRuntimeCore.lean" > "$work/mutant-translation.log" 2>&1 || {
    cat "$work/mutant-translation.log" >&2
    exit 1
  }
  if LEAN_PATH="$work/mutant:$work" lean -DwarningAsError=true RuntimeCoreProof.lean > "$work/mutant.log" 2>&1; then
    echo "runtime proofs accepted $1" >&2
    exit 1
  fi
  # The proof must fail on its own terms, not because a module is missing.
  grep -Fq 'error:' "$work/mutant.log"
  if grep -Eq 'unknown (constant|identifier|module|package)|object file' "$work/mutant.log"; then
    cat "$work/mutant.log" >&2
    exit 1
  fi
}
lose 'a memo hit that does not replay the failure' 'replay c (Entry r f errs d) =' '  mergeFail c f'
lose 'a body started with the caller failure record' 'evalBody c name i body =' '  writeSTRef (ctxFail c) NoFailure'
lose 'a negative lookahead that reports its failures' 'notP p =' '  writeSTRef (ctxFail c) saved'
lose 'an entry that skips the EOF diagnostic position' 'runParser cfg mkStore start input =' '      mergeFail ctx (Failure j (S.singleton ExpectedEnd))'
echo 'Checked the runtime translation, 5 rejected edits and 4 deletions the proofs reject.'
