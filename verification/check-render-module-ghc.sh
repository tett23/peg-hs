#!/bin/sh
set -eu

cd "$(dirname "$0")/.."
scratch=${1:?pass the shared temporary verification directory}
: "${LEAN_PATH:?set LEAN_PATH to the shared Lean object directory}"
[ -f "$LEAN_PATH/GHCGrammar.olean" ] || { echo 'GHCGrammar.olean is missing' >&2; exit 1; }
[ -f "$LEAN_PATH/LayoutDerivation.olean" ] || { echo 'LayoutDerivation.olean is missing' >&2; exit 1; }

(cd verification && lean -DwarningAsError=true \
  -o "$scratch/RenderModuleGHC.olean" RenderModuleGHC.lean) \
  > "$scratch/RenderModuleGHC.log"
if grep -q 'sorryAx' "$scratch/RenderModuleGHC.log"; then
  cat "$scratch/RenderModuleGHC.log" >&2
  exit 1
fi

cat > "$scratch/RenderModuleSource.expected" <<'SOURCE'
        ++ [ "module " <> unLoc (grammarModule g)
      , "  ( " <> T.intercalate "\n  , " exports
      , "  ) where"
      , ""
      ]
        ++ ["import qualified Prelude as PegPrelude" | usesPegPrelude]
        ++ [ "import qualified Peg.Runtime.Internal as PegRt"
           ]
        ++ ["import Prelude" | not (importsPrelude g)]
        ++ [""]
        ++ map verbatimBlock (grammarVerbatim g)
        ++ decls
SOURCE
sed -n '/^        ++ \[ "module "/,/^        ++ decls/p' \
  packages/peg-codegen/src/Peg/Codegen.hs > "$scratch/RenderModuleSource.actual"
diff -u "$scratch/RenderModuleSource.expected" "$scratch/RenderModuleSource.actual"

for name in Peg PegSyntax; do
  [ -f "$scratch/$name.trace" ] || { echo "$name.trace is missing" >&2; exit 1; }
  [ -f "$scratch/$name.tokens" ] || { echo "$name.tokens is missing" >&2; exit 1; }
  tail -n 5 "$scratch/$name.trace" | grep -Fq 'reduce (rule 835)' || {
    echo "$name: missing EOF close -> error" >&2
    exit 1
  }
  tail -n 3 "$scratch/$name.trace" | grep -Fq 'reduce (rule 66)' || {
    echo "$name: missing virtual body reduction" >&2
    exit 1
  }
  tail -n 2 "$scratch/$name.trace" | grep -Fq 'reduce (rule 61)' || {
    echo "$name: missing module reduction" >&2
    exit 1
  }
  tail -n 1 "$scratch/$name.trace" | grep -Fq 'action: accept.' || {
    echo "$name: missing acceptance" >&2
    exit 1
  }
done

sed 's/have r61 : productions 61 =/have r61 : productions 62 =/' \
  verification/RenderModuleGHC.lean > "$scratch/RenderModuleGHCInvalid.lean"
if (cd verification && lean -DwarningAsError=true \
    "$scratch/RenderModuleGHCInvalid.lean") \
    > "$scratch/RenderModuleGHCInvalid.log" 2>&1; then
  echo 'Lean accepted a changed module production' >&2
  exit 1
fi
grep -Eq 'error: Tactic `decide` failed|error: Tactic `decide` proved that' \
  "$scratch/RenderModuleGHCInvalid.log" || {
  cat "$scratch/RenderModuleGHCInvalid.log" >&2
  exit 1
}
printf 'Module frame: 18 Lean theorems, 2 real module traces, 1 rejected production mutation.\n'
