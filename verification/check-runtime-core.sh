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

# SelfHostedRuntime.lean restates predicate, which the translation leaves out.
# The generated predicates ignore the column (ExtractSelfHostedFile.hs reads
# `PegRt.predicate (\_col -> ...)` only).
cat > "$work/predicate.source" <<'SOURCE'
predicate :: (Int -> Bool) -> P r s ()
predicate f = P $ \c i ->
  pure (if f (colAt c i) then Ok i () else Fail)
SOURCE
sed -n '/^predicate ::/,/^$/p' "$runtime" | sed '$d' | diff -u "$work/predicate.source" -

# RuntimeForms.lean restates the forms that ExtractSelfHostedFile.hs leaves
# out of the bodies: Span, getOffset, spanFrom, withCol and capture.
cat > "$work/forms.source" <<'SOURCE'
data Span = Span
  { spanStart :: !Pos
  , spanEnd :: !Pos
  }
  deriving (Eq, Ord, Show)
capture :: P r s a -> P r s Text
capture p = P $ \c i ->
  unP p c i >>= \case
    Ok j _ -> pure (Ok j (slice (ctxInput c) i j))
    bad -> pure (failed bad)
withCol :: (Int -> P r s a) -> P r s a
withCol f = P $ \c i -> unP (f (colAt c i)) c i
getOffset :: P r s Int
getOffset = P $ \_ i -> pure (Ok i i)
spanFrom :: Int -> P r s Span
spanFrom start = P $ \c i -> pure (Ok i (Span (posAt c start) (posAt c i)))
SOURCE
for name in 'data Span' capture withCol getOffset spanFrom; do
  case $name in
    'data Span') start='^data Span = Span$' ;;
    *) start="^$name ::" ;;
  esac
  sed -n "/$start/,/^\$/p" "$runtime" | sed '$d'
done | diff -u "$work/forms.source" -
lean -DwarningAsError=true -o "$work/RuntimeForms.olean" RuntimeForms.lean
echo 'Checked the runtime translation, 5 rejected edits, 4 deletions the proofs reject, predicate and the left-out forms.'
