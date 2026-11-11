import Parsing

open PegVerification

def verdict (result : Result) : String :=
  match result with
  | .ok [] => "ok"
  | .ok _ => "fail"
  | .error none => "fail"
  | .error (some label) => "throw:" ++ label

def main : IO Unit := do
  let tests : List (String × Expr × List Char) :=
    [ ("choiceThrow", .choice (.label "inner" (.char 'a')) (.char 'b'), ['b'])
    , ("aheadLabel", .ahead (.label "inner" (.char 'a')), ['b'])
    , ("nestedLabel", .label "outer" (.label "inner" (.char 'a')), ['b'])
    , ("normalChoice", .choice (.char 'a') (.char 'b'), ['b'])
    , ("notLabel", .seq (.notAhead (.label "inner" (.char 'a'))) (.char 'b'), ['b'])
    , ("predicate", .predicate true, [])
    ]
  for (name, expression, input) in tests do
    IO.println s!"{name} {verdict (run expression input)}"
