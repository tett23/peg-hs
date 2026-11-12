#!/bin/sh
# Check both actual GHC parse traces against the separately extracted grammar.
set -eu
cd "$(dirname "$0")"
work=${1:?pass the temporary verification directory}
export LEAN_PATH="$work"
for module in HaskellDerivation TraceChunks LayoutDerivation; do
  lean -DwarningAsError=true -o "$work/$module.olean" "$module.lean"
done
runghc-9.10.3 ExtractHappyGrammar.hs "$work/Parser.info" "$work/Parser.generated.hs" "$work/rows" > "$work/GHCGrammar.lean"
compile() {
  lean -DwarningAsError=true -R "$work" -o "$work/$1.olean" "$work/$1.lean"
}
compile GHCGrammar
./check-render-expression-ghc.sh "$work"
./check-render-module-ghc.sh "$work"
./check-render-declarations-ghc.sh "$work"
./check-render-declaration-binders.sh "$work"
for name in Peg PegSyntax; do
  awk -v module="$name" -f extract-happy-trace.awk "$work/rows" "$work/$name.ids" "$work/$name.trace" > "$work/Derivation$name.lean"
  compile "Derivation$name"
done
lean -DwarningAsError=true AuditGHC.lean

# Change the first terminal of the already checked Peg certificate. Check just
# its first segment so later segments cannot mask the expected failure.
awk '
  /^def input0 / { if (!sub(/:= \[19,/, ":= [20,")) exit 1 }
  { print }
  /^theorem lexerChecked0 / { print "end Peg"; found=1; exit }
  END { if (!found) exit 1 }
' "$work/DerivationPeg.lean" > "$work/InvalidTerminal.lean"
if compile InvalidTerminal > "$work/InvalidTerminal.log" 2>&1; then
  echo "Lean accepted the changed module token" >&2
  exit 1
fi
grep -Fq 'Tactic `rfl` failed' "$work/InvalidTerminal.log" || { cat "$work/InvalidTerminal.log" >&2; exit 1; }
