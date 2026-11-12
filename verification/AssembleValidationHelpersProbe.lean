import AssembleValidationHelpers

open PegHs.AssembleValidationHelpers

def splitCases : List String :=
  ["", "A,B", " A , B ", "A(B,C), D", "A[B,C],D", "A,,B", ",A,",
   "A\t,B", "A\u00a0,B", "A(x,(y,z)),B", "A),B"]

def stringCases : List (String × String) :=
  [("expect", "S \"hello\""), ("expect", "S \"\""),
   ("message", "S \"x\""), ("expect", "S \"a\\n\""),
   ("expect", "S \"\\u{41}\""), ("expect", "S \"\\u{}\""),
   ("expect", "S \"\\q\""), ("expect", "S \"unterminated"),
   ("expect", "S \"ok\" extra"), ("expect", "bad-name \"x\""),
   ("expect", "S \"\\u{110000}\""), ("expect", "S \"\\u{d800}\""),
   ("expect", "S \"x\\u{1F600}\""), ("expect", "S \"a\\t\""),
   ("expect", "S\u00a0\"x\"")]

def main : IO Unit := do
  for s in splitCases do
    IO.println ("split:" ++ String.intercalate "|" (splitExports s))
  for (directive, arg) in stringCases do
    match stringArg (· == "S") directive arg with
    | .ok name => IO.println ("string:OK:" ++ name)
    | .error msg => IO.println ("string:ERR:" ++ msg)
