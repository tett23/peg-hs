#!/bin/sh
# Regenerate the golden data of ADR 0022 with the reference implementation.
# Requires Lua 5.5.1 built with LUA_COMPAT_GLOBAL (the default).
set -eu
cd "$(dirname "$0")"
version=$(lua -v 2>&1)
case "$version" in
  "Lua 5.5.1 "*) ;;
  *) echo "Lua 5.5.1 is required, found: $version" >&2; exit 1 ;;
esac
data=../../data/lua-5.5.1-tests
lua trace.lua 2000 1 > trace.tsv
lua eval.lua 2000 2 > eval.tsv
files=$(cd "$data" && ls *.lua)
# shellcheck disable=SC2086
lua mutate.lua "$data" 20 3 $files > mutations.tsv
echo "regenerated"
