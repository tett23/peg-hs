import Whitespace

open PegVerification

def main : IO Unit := do
  let spaces := (List.range 0x110000).filter fun n =>
    (n < 0xd800 || 0xe000 ≤ n) && ghcIsSpace (Char.ofNat n)
  IO.println s!"count={spaces.length}"
  IO.println (String.intercalate " " (spaces.map toString))
