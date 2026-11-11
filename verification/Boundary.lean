import Parsing

def main : IO Unit := do
  for count in [0, 1, 254, 255, 256, 257, 258] do
    let accepted := (List.range count).all PegVerification.withinDepth
    IO.println s!"{count} {if accepted then "accept" else "reject"}"
