#!/bin/sh
# ADR 0097 test design: every theorem must have its axioms listed by Audit.lean.
# Fail unless each module that states a theorem is in Audit.lean's module list.
set -eu
cd "$(dirname "$0")"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

sed -n '/-- audited modules begin/,/-- audited modules end/p' Audit.lean |
  grep -o '`[A-Za-z0-9_]*' | tr -d '`' | sort > "$work/listed"
[ -s "$work/listed" ] || { echo 'Audit.lean has no module list' >&2; exit 1; }
if [ -n "$(uniq -d "$work/listed")" ]; then
  echo 'Audit.lean lists a module twice' >&2
  exit 1
fi

# Modules written by hand. Audit.lean audits its own theorems.
grep -lE '^[[:space:]]*(private |protected )?(theorem|lemma) ' -- *.lean |
  sed 's/\.lean$//' | grep -vx Audit | sort > "$work/required"

# Generators that write theorems, and the module whose audit covers them. The
# item certificates written by SplitMetaFile are many small modules; each one
# is a premise of a FileResult proof that CertifiedPublicFiles uses, so the
# axioms of its public theorems include theirs.
cat > "$work/generators" <<'TABLE'
ExtractCallOrder.hs CallTables
ExtractConcreteTerminals.hs ConcreteTables
ExtractFile.hs FileTrees
ExtractSemanticClasses.hs GhcPredicates
ExtractSignatures.hs ExtractedSignatures
extract-happy-trace.awk DerivationPeg DerivationPegSyntax
SplitMetaFile.lean CertifiedPublicFiles
TABLE
grep -lE '"[^"]*(theorem|lemma) ' -- *.hs *.awk *.lean | sort > "$work/writers"
cut -d ' ' -f 1 "$work/generators" | sort > "$work/known"
unknown=$(comm -23 "$work/writers" "$work/known")
if [ -n "$unknown" ]; then
  printf 'add these theorem generators to check-audit-coverage.sh:\n%s\n' "$unknown" >&2
  exit 1
fi
cut -d ' ' -f 2- "$work/generators" | tr ' ' '\n' >> "$work/required"
sort -u "$work/required" -o "$work/required"

missing=$(comm -23 "$work/required" "$work/listed")
if [ -n "$missing" ]; then
  printf 'modules with theorems missing from Audit.lean:\n%s\n' "$missing" >&2
  exit 1
fi
printf '%s modules with theorems are audited\n' "$(wc -l < "$work/required" | tr -d ' ')"
