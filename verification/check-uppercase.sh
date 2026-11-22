#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
work=${1:?pass the Lean object directory}
: "${LEAN_PATH:?set LEAN_PATH to the Lean object directory}"
runghc-9.10.3 -Wall -Werror verification/ExtractUpperCase.hs > "$work/uppercase-ranges"
sed -n '/^def ranges : List (Nat × Nat × Nat) := \[$/,/^]$/p' verification/UpperCase.lean |
  sed '1d;$d' > "$work/uppercase-committed"
diff -u "$work/uppercase-ranges" "$work/uppercase-committed"
runghc-9.10.3 -Wall -Werror verification/ExtractUpperCase.hs --classifications > "$work/character-classifications"
cat > "$work/CharacterClassificationProbe.lean" <<'LEAN'
import HsPrelude

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected classification data")
  let mut checked := 0
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.isEmpty then continue
    let [some n, some symbol, some punctuation] := (line.splitOn " ").map String.toNat?
      | throw (IO.userError s!"invalid classification row {line}")
    let c := HsChar.ofNat n
    unless c.isSymbol == (symbol == 1) && c.isPunctuation == (punctuation == 1) do
      throw (IO.userError s!"root ADR 0097 I2: character classification mismatch at {n}")
    checked := checked + 1
  unless checked > 0 do throw (IO.userError "no character classifications checked")
  IO.println s!"root ADR 0097 I2: checked {checked} category boundary classifications."
LEAN
(cd verification && lean --run "$work/CharacterClassificationProbe.lean" "$work/character-classifications")
for kind in symbol punctuation; do
  mutant="$work/uppercase-mutant-$kind"
  mkdir -p "$mutant"
  case "$kind" in
    symbol) sed 's/c.generalCategory = .MathSymbol/c.generalCategory = .NotAssigned/' verification/HsPrelude.lean > "$mutant/HsPrelude.lean" ;;
    punctuation) sed 's/c.generalCategory = .ConnectorPunctuation/c.generalCategory = .MathSymbol/' verification/HsPrelude.lean > "$mutant/HsPrelude.lean" ;;
  esac
  cmp -s verification/HsPrelude.lean "$mutant/HsPrelude.lean" && exit 1
  (cd verification && lean -DwarningAsError=true -R "$mutant" -o "$mutant/HsPrelude.olean" "$mutant/HsPrelude.lean")
  if (cd verification && LEAN_PATH="$mutant:$LEAN_PATH" lean --run "$work/CharacterClassificationProbe.lean" "$work/character-classifications") > "$mutant/rejected.log" 2>&1; then
    echo "Accepted the $kind classification mutation" >&2
    exit 1
  fi
  grep -Fq 'root ADR 0097 I2: character classification mismatch at' "$mutant/rejected.log" || {
    cat "$mutant/rejected.log" >&2
    exit 1
  }
done
runghc-9.10.3 -Wall -Werror verification/ExtractUpperCase.hs --pairs > "$work/uppercase-haskell"
cat > "$work/UpperCaseProbe.lean" <<'LEAN'
import UpperCase

def main : IO Unit := do
  for n in [:0x110000] do
    let upper := PegHs.UpperCase.ofCode n
    if upper != n then IO.println s!"{n} {upper}"
LEAN
(cd verification && lean --run "$work/UpperCaseProbe.lean") > "$work/uppercase-lean"
diff -u "$work/uppercase-haskell" "$work/uppercase-lean"
printf 'root ADR 0097 I2: compared all 1114112 character uppercase mappings with GHC 9.10.3.\n'
