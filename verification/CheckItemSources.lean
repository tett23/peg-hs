import PegPieces
import SyntaxPieces

private def checkSource (path : String) (pieceSource : List Char) : IO Unit := do
  let actual ← IO.FS.readFile ⟨path⟩
  unless pieceSource == actual.toList do
    throw (IO.userError s!"generated pieces differ from {path}")
  IO.println s!"{path}: {pieceSource.length} characters match generated pieces"

def main (paths : List String) : IO Unit := do
  let (peg, syntaxPath) ← match paths with
    | [] => pure ("../packages/peg-grammar/grammar/Peg.hpeg",
        "../packages/peg-grammar/grammar/PegSyntax.hpeg")
    | [peg, syntaxPath] => pure (peg, syntaxPath)
    | _ => throw (IO.userError "expected zero or two grammar paths")
  checkSource peg PegHs.MetaPieces.Peg.source
  checkSource syntaxPath PegHs.MetaPieces.Syntax.source
