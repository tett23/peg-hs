import PredicateBindings
import EnvironmentDepth

open PegHs PegHs.EnvironmentEval PegHs.MetagrammarPredicates

private def inputs (rules : Nat → Body) (terms : Nat → Option ConcreteTerminal.Terminal)
    (preds : Array Site) (actions : Array (String × String × DepthAction))
    (calls : Array EnvironmentDepth.CallSite) (source : List Char) : Inputs :=
  let sites := preds.map fun site => (classifySite site).map fun kind => (kind, site.2.1)
  { rules, terms, input := source
    classes := GhcPredicates.classes
    sites := fun id => sites[id]?.join
    actions := fun id => actions[id]?.map (·.2.2)
    predicateEnv := fun id env => match sites[id]?.join with
      | some (kind, _) => PredicateBindings.predicateEnv kind env
      | none => { captured := [], depth := env.depth }
    hooks := EnvironmentDepth.hooks (fun id => calls[id]?) (fun _ _ _ => none) }

private def peg := inputs MetaTerminal1.environmentBody MetaTerminal1.termById
  MetaTerminal1.predicateSites MetaTerminal1.depthActions MetaTerminal1.callSites
private def syntaxPeg := inputs MetaTerminal2.environmentBody MetaTerminal2.termById
  MetaTerminal2.predicateSites MetaTerminal2.depthActions MetaTerminal2.callSites

private def check (source : String) (expected : String) : IO Unit := do
  let chars := source.toList
  for make in [peg, syntaxPeg] do
    let ctx := make chars
    let actual := match runFuel ctx 12000 (ctx.rules 0) chars.length {} with
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
