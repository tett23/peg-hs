#!/bin/sh
# Copies the editor grammars that releases carry to a directory (ADR 0073):
# the TextMate grammar, the tree-sitter grammar with its generated parser
# and queries, the license and a README. The files are listed, so that
# node_modules, a built parser.so and the tests stay out; a new file goes
# here and to editors/test/pack.txt.
#
#   scripts/pack-editors.sh OUT
set -eu

if [ $# -ne 1 ]; then
  echo "usage: $0 OUT" >&2
  exit 2
fi
out=$1
root=$(cd "$(dirname "$0")/.." && pwd)

copy() {
  # copy SOURCE DEST, both relative to the repository and to OUT
  mkdir -p "$out/$(dirname "$2")"
  cp "$root/$1" "$out/$2"
}

copy LICENSE LICENSE
copy editors/README.md README.md
copy editors/textmate/hpeg.tmLanguage.json textmate/hpeg.tmLanguage.json
for f in \
  grammar.js package.json tree-sitter.json \
  queries/folds.scm queries/highlights.scm queries/indents.scm \
  queries/injections.scm queries/locals.scm \
  src/grammar.json src/node-types.json src/parser.c src/scanner.c \
  src/tree_sitter/alloc.h src/tree_sitter/array.h src/tree_sitter/parser.h
do
  copy "editors/tree-sitter-hpeg/$f" "tree-sitter-hpeg/$f"
done
