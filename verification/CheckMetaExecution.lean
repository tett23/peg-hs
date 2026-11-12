import TotalFile

open PegHs.EnvironmentEval PegHs.MetaExecution

private def check (source : String) (expected : String) : IO Unit := do
  let chars := source.toList
  for mode in [false, true] do
    let diagnostic : PegHs.PublicParsing.Failure → String
      | .ordinary => "fail"
      | .expectedEnd pos => s!"expected end at byte {pos}"
      | .labelled name _ => name
    let result := parseFile mode source diagnostic
    let actual := match result with
      | .ok () => "ok"
      | .error ds => String.intercalate ", " ds
    let agrees := match result with
      | .ok () => expected == "ok"
      | .error [msg] => expected == "error" || msg == expected
      | .error _ => false
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
