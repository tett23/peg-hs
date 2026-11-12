import TotalFile

open PegHs.EnvironmentEval PegHs.MetaExecution

private def check (source : String) (strictExpected syntaxExpected : String) : IO Unit := do
  let chars := source.toList
  for mode in [false, true] do
    let expected := if mode then syntaxExpected else strictExpected
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
      throw (IO.userError s!"syntax mode {mode}, input length {chars.length}: expected {expected}, got {actual}")

def main (paths : List String) : IO Unit := do
  if let "--compare" :: [manifest] := paths then
    for line in (← IO.FS.readFile ⟨manifest⟩).splitOn "\n" do
      if !line.isEmpty then
        let strict := line.takeWhile (· != ' ')
        let rest := line.drop (strict.toString.length + 1)
        let syntaxExpected := rest.takeWhile (· != ' ')
        let file := rest.drop (syntaxExpected.toString.length + 1)
        check (← IO.FS.readFile ⟨file.toString⟩) strict.toString syntaxExpected.toString
    return
  for n in [255, 256, 257] do
    let expected := if n ≤ 256 then "ok" else "nest"
    check ("Start <- " ++ String.ofList (List.replicate n '&') ++ "'x'\n")
      expected expected
  for path in paths do
    check (← IO.FS.readFile ⟨path⟩) "ok" "ok"
    IO.println s!"Both extracted metagrammars accepted {path}"
