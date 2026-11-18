#!/bin/sh
# Writes Mermaid figures of how the theorems of ADR 0097 use one another.
#
#   verification/proof-graph.sh [-d DEPTH] LEAN_PATH OUT_DIR
#
# LEAN_PATH holds the compiled modules (the directory that check.sh compiles
# into, and its item-certificates directory). OUT_DIR receives overview.md and
# invariant1.md to invariant3.md. In the per-invariant figures, the theorems at
# most DEPTH uses (default 2) away from a public entry, and the theorems that
# README.md names in the chain tables, stay as nodes; the other theorems are
# folded into dashed edges. ProofGraph.lean describes the graph.
set -eu

usage() {
  echo "usage: $0 [-d DEPTH] LEAN_PATH OUT_DIR" >&2
  exit 2
}

depth=2
while getopts d: opt; do
  case $opt in
    d) depth=$OPTARG ;;
    *) usage ;;
  esac
done
shift $((OPTIND - 1))
[ $# -eq 2 ] || usage
lean_path=$1
mkdir -p "$2"
out=$(cd "$2" && pwd)
cd "$(dirname "$0")"
# The rows of the tables under "### 不変条件 N" in the section
# "公開の入口から結論までの定理の連なり": invariant, name, file.
# A row may name several theorems and as many places, in the same order.
awk '
/^## / { insec = index($0, "公開の入口から結論までの定理の連なり") > 0; k = "" }
insec && /^### 不変条件 [0-9]/ { k = substr($0, length("### 不変条件 ") + 1, 1) }
insec && k != "" && /^\| [0-9]+ \|/ {
  split($0, col, "|")
  nl = split(col[4], locs, "、")
  i = 0
  s = col[3]
  while (match(s, /`[^`]+`/)) {
    i++
    name = substr(s, RSTART + 1, RLENGTH - 2)
    s = substr(s, RSTART + RLENGTH)
    loc = locs[i <= nl ? i : nl]
    gsub(/^ +| +$/, "", loc)
    sub(/:.*/, "", loc)
    printf "%s\t%s\t%s\n", k, name, loc
  }
}' README.md |
  LEAN_PATH=$lean_path lean --run ProofGraph.lean proof-graph-stages.tsv - "$depth" "$out" \
  PublicGeneration PublicGenerationGHC CommittedModuleDerivations CertifiedPublicFiles
