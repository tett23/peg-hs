import TotalFile

open PegHs.EnvironmentEval PegHs.MetaExecution

private def check (source : String) (expected : String) : IO Unit := do
  let chars := source.toList
  for mode in [false, true] do
    let actual := match (recognizeFile mode chars).val with
      | .ok 0 _ => "ok"
      | .ok rest _ => s!"remaining {rest}"
      | .throwLabel _ name _ => name
      | .fail => "fail"
    let agrees := if expected == "error" then
      actual != "ok" && !actual.startsWith "remaining "
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
