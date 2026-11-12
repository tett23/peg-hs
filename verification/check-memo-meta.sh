#!/bin/sh
set -eu

work=${1:?pass the verification scratch directory with CallTables.olean}
test -f "$work/CallTables.olean"
cabal=${CABAL:-cabal}
generated_dir=${GENERATED_DIR:-packages/peg-grammar/src/Peg/Grammar}

extract_plan() {
  "$cabal" exec -v0 -- runghc-9.10.3 -package=peg-grammar \
    verification/ExtractMemoPlan.hs "$1" > "$2"
}

extract_wrappers() {
  awk '
    $1 ~ /^PegRt\.(memo|memoArg|memoLR|nomemo)$/ {
      kind = substr($1, 7)
      if (kind == "nomemo") {
        name = $2
      } else {
        name = $3
        gsub(/"/, "", name)
        quote = sprintf("%c", 39)
        if ($2 != "peg" quote "memo" quote name) exit 1
      }
      gsub(/"/, "", name)
      if (name !~ /^[A-Za-z_][A-Za-z_0-9]*$/) exit 1
      print name "\t" kind
    }
  ' "$1" > "$2"
}

for pair in 'Peg SelfHosted' 'PegSyntax SelfHostedSyntax'; do
  set -- $pair
  grammar=$1
  generated=$2
  extract_plan "packages/peg-grammar/grammar/$grammar.hpeg" "$work/$grammar.memo-plan"
  extract_wrappers "$generated_dir/$generated.hs" "$work/$grammar.memo-wrappers"
  diff -u "$work/$grammar.memo-plan" "$work/$grammar.memo-wrappers"
  if grep -E 'memoLR|nomemo' "$work/$grammar.memo-plan"; then
    echo "$grammar unexpectedly needs a left-recursion seed or disables memo" >&2
    exit 1
  fi
  awk -F '\t' -v name="$grammar" '
    $2 == "memo" { ordinary++ }
    $2 == "memoArg" { arguments++ }
    END { printf "%s: %d memo, %d memoArg, 0 memoLR\n", name, ordinary, arguments }
  ' "$work/$grammar.memo-plan"
done

(cd verification && LEAN_PATH="$work" lean -DwarningAsError=true \
  -o "$work/MemoMetaNoLR.olean" MemoMetaNoLR.lean)

# Exercise the exact generated wrappers and runtime with memo on and off.
# These examples complement the Lean call-order and table proofs; they do not
# establish stability for every possible input.
peg=$("$cabal" list-bin exe:peg-hs)
mkdir -p "$work/memo-probe/Peg/Grammar"
"$peg" gen --debug-entry packages/peg-grammar/grammar/Peg.hpeg \
  -o "$work/memo-probe/Peg/Grammar/SelfHosted.hs"
"$peg" gen --debug-entry packages/peg-grammar/grammar/PegSyntax.hpeg \
  -o "$work/memo-probe/Peg/Grammar/SelfHostedSyntax.hs"
"$cabal" exec -v0 -- runghc-9.10.3 -i"$work/memo-probe" \
  -package=peg-grammar -package=peg-runtime verification/MemoMetaProbe.hs
