#!/bin/sh
# Reproduce SEC-01 only inside a disposable directory.
#
# Usage: sh docs/audits/reproduce-symlink.sh /absolute/path/to/peg-hs
set -eu

exe=$1
[ -x "$exe" ] || { echo "not an executable: $exe" >&2; exit 2; }
root=$(mktemp -d "${TMPDIR:-/tmp}/peg-audit-XXXXXX")
trap 'rm -rf "$root"' EXIT

mkdir "$root/repo" "$root/outside"
victim=$root/outside/Victim.hpeg
printf "%%module M\nS :: ()\nS <-   'a'    { () }\n" > "$victim"
cp "$victim" "$root/before.hpeg"
ln -s "$root/outside" "$root/repo/linked"

set +e
(cd "$root/repo" && "$exe" fmt) 2> "$root/stderr"
status=$?
set -e

if cmp -s "$root/before.hpeg" "$victim"; then changed=false; else changed=true; fi
echo "case: directory symlink escape"
echo "exit: $status"
echo "outside_changed: $changed"
echo "--- before"; cat "$root/before.hpeg"
echo "--- after"; cat "$victim"
echo "--- stderr"; cat "$root/stderr"
