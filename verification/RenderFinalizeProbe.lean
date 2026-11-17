import RenderFinalize

/-
Runs the Lean models of RenderFinalize on real inputs for
check-render-finalize.sh:

  finalize SHOWN K FILE      prints `finalize SHOWN (restoreMarker K)` of FILE
  header SOURCE PRUNED LANG* prints the header lines, each followed by '\n'
                             (PRUNED is `pruned` or `full`)
-/

open PegHs.RenderFinalize

def main (args : List String) : IO UInt32 := do
  match args with
  | ["finalize", shown, k, file] =>
    let t ← IO.FS.readFile file
    IO.print (finalize shown (restoreMarker k.toNat!) t)
    pure 0
  | "header" :: source :: pruned :: languages =>
    IO.print (textUnlines (headerLines source languages (pruned == "pruned")))
    pure 0
  | _ =>
    IO.eprintln "usage: finalize SHOWN K FILE | header SOURCE PRUNED LANGUAGE..."
    pure 2
