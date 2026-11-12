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
    , ("anyChar", .any, ['x'])
    , ("manyZero", .seq (.many (.predicate true)) (.char 'b'), ['b'])
    , ("skipManyZero", .seq (.many (.predicate true)) (.char 'b'), ['b'])
    , ("manyFail", .seq (.many (.char 'a')) (.char 'b'), ['a', 'a', 'a', 'b'])
    , ("skipManyFail", .seq (.many (.char 'a')) (.char 'b'), ['a', 'a', 'a', 'b'])
    , ("manyThrow", .many (.label "inner" (.char 'a')), ['b'])
    , ("skipManyThrow", .many (.label "inner" (.char 'a')), ['b'])
    , ("manyLateZero", .seq (.many (.choice (.char 'a') (.predicate true))) (.char 'b'), ['a', 'a', 'a', 'b'])
    , ("manyLateThrow", .many (.choice (.char 'a') (.label "stop" (.char 'c'))), ['a', 'a', 'a', 'b'])
    ]
  for (name, expression, input) in tests do
    IO.println s!"{name} {verdict (run expression input)}"
