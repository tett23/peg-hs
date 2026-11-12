#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
# Include the actual start rule, runtime EOF check and public diagnostic mapping.
digest=$({
  sed -n '/^parse peg.input =/,/^$/p' packages/peg-grammar/src/Peg/Grammar/SelfHosted.hs
  sed -n '/^runParser cfg mkStore start input =/,/^  pure (res, s)$/p' packages/peg-runtime/src/Peg/Runtime/Internal.hs
  sed -n -e '/^parseGrammar src =/p' -e '/^parseTops src =/,/^      \[\] -> Nothing$/p' packages/peg-grammar/src/Peg/Grammar/Parser.hs
} | shasum -a 256 | cut -d ' ' -f 1)
[ "$digest" = 773092a6a37731bbf7066869360e8d6ea4452ccb914b32daa975672a81814caf ] || { echo 'review the public parse entry proof' >&2; exit 1; }
