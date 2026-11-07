#!/bin/sh
# Builds the example of peg-hooks and checks how it is built again
# (ADR 0085). The example is copied to WORKDIR/calc, and the copy is
# changed; the example itself is not.
#
#   examples/hooks/test.sh WORKDIR
#
# CABAL names cabal (default: cabal). The first build builds Cabal from
# Hackage, for the setup script, and takes some minutes.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
work=${1:?usage: examples/hooks/test.sh WORKDIR}
cabal=${CABAL:-cabal}

mkdir -p "$work"
work=$(cd "$work" && pwd)
pkg=$work/calc
log=$work/build.log
rm -rf "$pkg"
mkdir -p "$pkg"
(cd "$here" && cp -R calc.cabal Setup.hs SetupHooks.hs grammar src "$pkg/")
sed "s|\.\./\.\./packages|$root/packages|" "$here/cabal.project" > "$pkg/cabal.project"
cd "$pkg"

failures=0
pass() { echo "ok: $1"; }
fail() {
  echo "FAIL: $1"
  sed 's/^/  | /' "$log"
  failures=$((failures + 1))
}

# Changes FILE with the sed script, and stops if nothing changed.
edit() {
  sed "$2" "$1" > "$1.new"
  if cmp -s "$1" "$1.new"; then
    echo "test.sh: $2 does not change $1" >&2
    exit 2
  fi
  mv "$1.new" "$1"
}

restore() {
  for f in "$@"; do
    cp "$here/$f" "$pkg/$f"
  done
}

build() { "$cabal" build exe:calc > "$log" 2>&1; }

run() { printf '%s\n' "$1" | "$("$cabal" list-bin exe:calc)" 2>> "$log"; }

start=$(date +%s)
if build; then
  pass "the first build ($(($(date +%s) - start)) seconds)"
else
  fail "the first build"
  exit 1
fi
out=$(run '1 + 2 * 3')
if [ "$out" = 'Add (Num 1) (Mul (Num 2) (Num 3))' ]; then
  pass "1 + 2 * 3 parses"
else
  fail "1 + 2 * 3 gives: $out"
fi
# The rule of the package itself, joined with <>, wrote Calc.Greeting.
if grep -q '^calc: an expression on a line$' "$log"; then
  pass "the hook of the package runs with pegSetupHooks"
else
  fail "the greeting of Calc.Greeting is missing"
fi

if build && ! grep -q 'Compiling Calc.Parser' "$log"; then
  pass "a build without changes does not compile Calc.Parser"
else
  fail "a build without changes"
fi

edit grammar/Calc.hpeg 's/{ Add l r }/{ Add r l }/'
if build && grep -q 'Compiling Calc.Parser' "$log"; then
  out=$(run '1 + 2 * 3')
  if [ "$out" = 'Add (Mul (Num 2) (Num 3)) (Num 1)' ]; then
    pass "a change of the grammar changes the parser"
  else
    fail "after a change of the grammar, 1 + 2 * 3 gives: $out"
  fi
else
  fail "a change of the grammar does not compile Calc.Parser"
fi
restore grammar/Calc.hpeg

edit grammar/Calc.hpeg "s/^Sp <- ' '\*\$/Sp <- ' '* Missing/"
if ! build && grep -q '^grammar/Calc\.hpeg:[0-9]*:[0-9]*: error: ' "$log" && ! grep -q 'GHC-' "$log"; then
  pass "an error of the grammar stops the build"
else
  fail "an error of the grammar"
fi
restore grammar/Calc.hpeg

edit grammar/Calc.hpeg 's/{ Num (read (T.unpack d)) }/{ Num d }/'
if ! build && grep -q 'grammar/Calc\.hpeg:[0-9]*:[0-9]*: error: \[GHC-' "$log"; then
  pass "a type error of an action is at the grammar"
else
  fail "a type error of an action"
fi
restore grammar/Calc.hpeg

# The module is named in the .cabal file too: cabal runs only the rules
# whose modules a component lists in autogen-modules.
edit SetupHooks.hs 's/"Calc\.Parser"/"Calc.Other"/'
edit calc.cabal 's/Calc\.Parser/Calc.Other/g'
if ! build && grep -q '^grammar/Calc\.hpeg:[0-9]*:[0-9]*: error: .*Calc\.Other' "$log"; then
  pass "a module name other than %module stops the build"
else
  fail "a module name other than %module"
fi
restore SetupHooks.hs calc.cabal

if "$cabal" check > "$log" 2>&1; then
  pass "cabal check"
else
  fail "cabal check"
fi

rm -rf "$work/sdist"
if "$cabal" sdist --output-directory "$work/sdist" > "$log" 2>&1; then
  tar -tzf "$work"/sdist/calc-*.tar.gz > "$log"
  if grep -q 'grammar/Calc\.hpeg$' "$log" && grep -q 'SetupHooks\.hs$' "$log" && ! grep -q 'Parser\.hs$' "$log"; then
    pass "the source tarball has the grammar and not the generated module"
  else
    fail "the files of the source tarball"
  fi
else
  fail "cabal sdist"
fi

if [ "$failures" -ne 0 ]; then
  echo "$failures failed"
  exit 1
fi
echo "all passed"
