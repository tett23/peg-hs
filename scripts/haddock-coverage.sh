#!/bin/sh
# Every exposed module of the published packages is fully documented
# (ADR 0009, ADR 0044). Reads the output of cabal haddock, which reports the
# coverage of each module, and fails if a module is below 100% or if the
# output has no coverage at all.
#   cabal haddock PACKAGES... 2>&1 | scripts/haddock-coverage.sh
set -eu
out=$(cat)
printf '%s\n' "$out"
report=$(printf '%s\n' "$out" | grep -E '^ *[0-9]+% \(' || true)
if [ -z "$report" ]; then
  echo "haddock-coverage: no coverage in the output of haddock" >&2
  exit 1
fi
missing=$(printf '%s\n' "$report" | grep -vE '^ *100% \(' || true)
if [ -n "$missing" ]; then
  echo "haddock-coverage: modules not fully documented:" >&2
  printf '%s\n' "$missing" >&2
  exit 1
fi
echo "haddock-coverage: $(printf '%s\n' "$report" | wc -l | tr -d ' ') modules, all 100%"
