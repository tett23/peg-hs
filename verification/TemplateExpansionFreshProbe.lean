import TemplateExpansionFresh

open PegHs.TemplateExpansion

def numbers : List Nat :=
  [0, 1, 9, 10, 99, 100, 9223372036854775807, 9223372036854775808, 10^100]

def cases : List (List String × List String × Nat) :=
  [([], [], 0), (["T'0"], [], 0), (["T'0"], ["T'1"], 0),
   (["T'0", "T'1", "T'2"], [], 0), (["T'0"], ["T'5"], 5),
   (["Other'0", "T'0"], ["T'2", "T'1"], 0)]

def main : IO Unit := do
  for n in numbers do
    IO.println (decimalName "T" n)
  for (original, generated, start) in cases do
    match boundedSearch "T" original generated start with
    | some k => IO.println (decimalName "T" k)
    | none => IO.println "MISSING"
