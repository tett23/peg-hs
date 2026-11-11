#!/bin/sh
set -eu

source_file=${1:-packages/peg-codegen/src/Peg/Codegen.hs}
lean_file=verification/Guard.lean

# The extractor accepts exactly this Haskell syntax. Unknown forms fail.
extracted=$(awk '
  BEGIN { quote = sprintf("%c", 39); double_quote = sprintf("%c", 34) }
  /^generate opts g0 = do$/ {
    if (++guard_count != 1) exit 1
    if (getline <= 0 ||
        $0 != "  if any (any isControlChar) [optSourceName opts, optOutputName opts]") exit 1
    if (getline <= 0) exit 1
    count = split($0, diagnostic, double_quote)
    if (count != 3 ||
        diagnostic[1] != "    then Left [Diagnostic (Loc 0 1 1) " ||
        diagnostic[3] != "]" ||
        diagnostic[2] !~ /^[A-Za-z ]+$/) exit 1
    message = diagnostic[2]
    if (getline <= 0 || $0 != "    else pure ()") exit 1
  }
  /^isControlChar :: Char -> Bool$/ {
    if (++control_count != 1) exit 1
    if (getline <= 0) exit 1
    count = split($0, part, quote)
    if (count != 5 ||
        part[1] != "isControlChar c = c < " ||
        part[3] != " || c == " ||
        part[5] != "" ||
        part[2] !~ /^\\x[0-9A-Fa-f][0-9A-Fa-f]$/ ||
        part[4] !~ /^\\x[0-9A-Fa-f][0-9A-Fa-f]$/) exit 1
    expression = "  n < 0x" tolower(substr(part[2], 3)) \
                 " || n == 0x" tolower(substr(part[4], 3))
  }
  END {
    if (guard_count != 1 || control_count != 1 || message == "" || expression == "")
      exit 1
    print expression
    print "    some " double_quote message double_quote
  }
' "$source_file") || {
  echo 'Unsupported Haskell file-name guard; update its Lean translation.' >&2
  exit 1
}

lean_expression=$(awk '
  /^private def translatedIsControlChar / { if (++found != 1) exit 1; getline; print }
  END { if (found != 1) exit 1 }
' "$lean_file") || exit 1
lean_diagnostic=$(awk '
  /^private def fileNameDiagnostic / {
    if (++found != 1) exit 1
    getline
    getline
    print
  }
  END { if (found != 1) exit 1 }
' "$lean_file") || exit 1
translated=$(printf '%s\n%s' "$lean_expression" "$lean_diagnostic")
if [ "$extracted" != "$translated" ]; then
  echo 'The Haskell guard differs from the Lean translation.' >&2
  exit 1
fi
