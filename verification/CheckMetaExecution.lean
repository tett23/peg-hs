import MetaExecution

open PegHs.EnvironmentEval PegHs.MetaExecution

private def check (source : String) (expected : String) : IO Unit := do
  let chars := source.toList
  for (make, start) in [(peg, MetaTerminal1.startRule), (syntaxPeg, MetaTerminal2.startRule)] do
    let ctx := make chars
    let actual := match runFuel ctx 12000 (ctx.rules start) chars.length {} with
      | some (.ok 0 _) => "ok"
      | some (.ok rest _) => s!"remaining {rest}"
      | some (.throwLabel _ name _) => name
      | some .fail => "fail"
      | none => "fuel exhausted"
    let agrees := if expected == "error" then
      actual != "ok" && actual != "fuel exhausted" && !actual.startsWith "remaining "
      else actual == expected
    unless agrees do
      throw (IO.userError s!"input length {chars.length}: expected {expected}, got {actual}")

def main (paths : List String) : IO Unit := do
  if let "--compare" :: [manifest] := paths then
    for line in (← IO.FS.readFile ⟨manifest⟩).splitOn "\n" do
      if !line.isEmpty then
        let expected := line.takeWhile (· != ' ')
        check (← IO.FS.readFile ⟨(line.drop (expected.toString.length + 1)).toString⟩) expected.toString
    return
  for n in [255, 256, 257] do
    check ("Start <- " ++ String.ofList (List.replicate n '&') ++ "'x'\n")
      (if n ≤ 256 then "ok" else "nest")
  for path in paths do
    check (← IO.FS.readFile ⟨path⟩) "ok"
    IO.println s!"Both extracted metagrammars accepted {path}"
