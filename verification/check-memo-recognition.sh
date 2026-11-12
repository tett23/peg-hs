#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
source_file=${1:-packages/peg-runtime/src/Peg/Runtime/Internal.hs}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM

# Exact bodies are pinned: an added branch or side effect must be reviewed
# before the Lean projection can be trusted again. The predicates below cover
# strict-mode error suppression, entry construction/replay, both key shapes,
# and undo during left-recursion growth.
check_body() {
  label=$1
  start=$2
  stop=$3
  expected=$4
  if ! awk -v start="$start" -v stop="$stop" '
    index($0,start)==1 { starts++; active=1 }
    index($0,stop)==1 && active { stops++; active=0 }
    active { print }
    END { if (starts != 1 || stops != 1) exit 1 }
  ' "$source_file" > "$work/body"; then
    echo "memo source boundary changed: $label" >&2
    exit 1
  fi
  actual=$(shasum -a 256 "$work/body" | cut -d ' ' -f 1)
  if [ "$actual" != "$expected" ]; then
    echo "memo source body changed: $label" >&2
    exit 1
  fi
}

check_body mergeFailure 'mergeFailure ::' '-- | The result of running a parser' 105ce02a37e6f33ac1358e1b86867dcf2085fd0c9dabef345811c6a343a2f774
check_body saveErrors 'saveErrors ::' 'restoreErrors ::' 7d6cd08dc47f8c4d0fc157b981870b24508f9378e8bda7f3385b041f05fb0848
check_body evalBody 'evalBody ::' '-- The errors recorded since' 02b7720eddbba7bcffab139ded423437078e6d6dd8c3b2477580e5cae1f709d1
check_body newErrors 'newErrors ::' '-- Add the errors of a slice' 247cd7b07e4a1d1784714c79c55b360053c01f6653a973a0245a0c95ca16d97d
check_body appendSlice 'appendSlice ::' '-- Replay a memo entry' e0ed8ef17964def4425957e5ab20a6adf932aa90dda8ca5cbd546232c3de59aa
check_body replay 'replay ::' '-- Record how to remove' ebe8d3fe2c2424c230ca3d9543a2748bd2e0a200cea15c51c765dd98342aefa6
check_body logUndo 'logUndo ::' '-- End an iteration' 23eedf96bf43fdb09f28a993f51e7361309b8a7bec421ba4a5b0f56317209677
check_body endIteration 'endIteration ::' '-- | Memoise a rule that does not take part' f4a22f64ef2fe9099c4b09a78552ca192dfa4f14d6f7f3b10d421f8fc06afbac
check_body memo 'memo ::' '-- | Memoise a rule with arguments' 31207ef13e1db4e649a112ef171fcbb30a1478c86d6b28eaf8a434c3015dab0c
check_body memoArg 'memoArg ::' '-- | A rule that is not memoised' 18cb782ba5492e00f36203974aff424a23f5937ed72414b897d635293e124c8d
grep -Fqx '  ctx <- newCtx cfg {cfgRecover = False} mkStore input' "$source_file"
grep -Fqx 'defaultConfig = Config {cfgMemo = True, cfgDiscard = True, cfgDiscardAll = False, cfgCount = False, cfgTabstop = 0, cfgRecover = False}' "$source_file"

LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}" lean -DwarningAsError=true -o "$work/MemoRecognition.olean" verification/MemoRecognition.lean
LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}" lean -DwarningAsError=true verification/MemoRecognitionTests.lean
echo 'Checked 10 memo source bodies, 2 strict/default guards, and 9 Lean boundary cases.'
