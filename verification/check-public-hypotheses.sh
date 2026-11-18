#!/bin/sh
# ADR 0097: the hypotheses of the public theorems and the predicates that the
# public entry functions depend on must be those of public-hypotheses.allow
# (PublicHypotheses.lean reads them from the types and definitions). A list
# without one of its lines must fail, so that a new hypothesis fails CI.
set -eu
cd "$(dirname "$0")"
work=${1:?pass the Lean object directory}
export LEAN_PATH="$work/item-certificates:$work"

lean -DwarningAsError=true PublicHypotheses.lean

grep -v '^#' public-hypotheses.allow | sed '1d' > "$work/public-hypotheses.short"
grep '^#' public-hypotheses.allow >> "$work/public-hypotheses.short"
if PUBLIC_HYPOTHESES_ALLOW="$work/public-hypotheses.short" \
  lean -DwarningAsError=true PublicHypotheses.lean > "$work/public-hypotheses.log" 2>&1; then
  echo 'PublicHypotheses accepted a hypothesis missing from the list' >&2
  exit 1
fi
grep -Fq 'not allowed:' "$work/public-hypotheses.log" || { cat "$work/public-hypotheses.log" >&2; exit 1; }

# A reason that is no row of ADR 0097 is refused.
awk -F '\t' 'BEGIN { OFS = "\t" } !done && $2 ~ /^UNRESOLVED/ { $2 = "because"; done = 1 } { print }' \
  public-hypotheses.allow > "$work/public-hypotheses.reason"
if PUBLIC_HYPOTHESES_ALLOW="$work/public-hypotheses.reason" \
  lean -DwarningAsError=true PublicHypotheses.lean > "$work/public-hypotheses.log" 2>&1; then
  echo 'PublicHypotheses accepted a reason that is no row of ADR 0097' >&2
  exit 1
fi
grep -Fq 'is not a row of ADR 0097' "$work/public-hypotheses.log" || { cat "$work/public-hypotheses.log" >&2; exit 1; }
printf 'Checked the hypotheses of the public theorems.\n'
