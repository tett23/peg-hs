import FileTopItems

open PegHs.EnvironmentEval PegHs.MetaExecution

private def split (mode : Bool) (path : String) : IO Unit := do
  let source ← IO.FS.readFile ⟨path⟩
  let input := source.toList
  let ctx := context mode input
  let some (.ok afterWs wsEnv) := runFuel ctx 12000 (.call 0 4) input.length {}
    | throw (IO.userError s!"Ws did not succeed: {path}")
  let mut remaining := afterWs
  let mut env := { wsEnv with resultDepth := 0 }
  let mut count := 0
  IO.println s!"{path}: chars={input.length} wsEnd={input.length - afterWs}"
  for _ in [:input.length + 1] do
    match runFuel ctx 12000 (.call 1 1) remaining env with
    | some (.ok rest inner) =>
      unless rest < remaining do
        throw (IO.userError s!"TopItem did not consume at {remaining}: {path}")
      IO.println s!"item={count} start={input.length - remaining} end={input.length - rest}"
      count := count + 1
      env := { inner with resultDepth := max env.resultDepth inner.resultDepth }
      remaining := rest
    | some .fail => break
    | some (.throwLabel pos name _) =>
      throw (IO.userError s!"TopItem threw {name} at {pos}: {path}")
    | none => throw (IO.userError s!"TopItem ran out of fuel: {path}")
  unless remaining == 0 do
    throw (IO.userError s!"TopItem stopped before EOF at {remaining}: {path}")
  unless runFuel ctx 12000 (.terminal 0) 0 env == some .fail do
    throw (IO.userError s!"EOF test failed: {path}")
  IO.println s!"{path}: items={count} remaining={remaining}"

def main (paths : List String) : IO Unit := do
  match paths with
  | [peg, syntaxPath] =>
    split false peg
    split true syntaxPath
  | _ => throw (IO.userError "expected Peg.hpeg and PegSyntax.hpeg")
