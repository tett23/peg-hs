import FileTops

/-!
Prints, for each file of the manifest that FileTopsProbe.hs writes, the items
that `PegHs.FileTops.runTops` finds, in the format of FileTopsProbe.hs: the
kind and the location of the `Top` that the item's alternative builds, or
`reject`. `runTops_sound` and `invariant1_tops_unique` make this list the
item list of the derivation. A fuel that does not suffice prints `reject`,
which differs from what the Haskell side prints for an accepted file.

The location is that of `l:Here` in the alternative: the start of the item
for `Directive` and `Declaration`; for `Verbatim` the position after `%{`,
moved to the start of the next line when the block starts with a newline
(`verbatimBody`).
-/

open PegHs.FileTops

/-- Line and column (from 1, in characters) of an offset, as `posIn` counts them. -/
def position (input : List Char) (offset : Nat) : Nat × Nat :=
  let before := input.take offset
  (before.count '\n' + 1, (before.reverse.takeWhile (· != '\n')).length + 1)

def render (input : List Char) (item : Item) : String :=
  let offset := input.length - item.start
  let show2 (p : Nat × Nat) := s!"{p.1}:{p.2}"
  match item.kind with
  | .directive => "directive " ++ show2 (position input offset)
  | .declaration => "declaration " ++ show2 (position input offset)
  | .verbatim =>
    let (line, col) := position input (offset + 2)
    if input[offset + 2]? == some '\n' then s!"verbatim {line + 1}:1"
    else s!"verbatim {line}:{col}"

def main (args : List String) : IO Unit := do
  let [manifest] := args | throw (IO.userError "usage: FileTopsProbe MANIFEST")
  for line in (← IO.FS.readFile ⟨manifest⟩).splitOn "\n" do
    if !line.isEmpty then
      match line.splitOn "\t" with
      | [name, path] =>
        let input := (← IO.FS.readFile ⟨path⟩).toList
        IO.println s!"case {name}"
        match runTops input (8 * input.length + 4096) with
        | none => IO.println "reject"
        | some items =>
          IO.println s!"ok {items.length}"
          for item in items do
            IO.println (render input item)
      | _ => throw (IO.userError s!"bad manifest line: {line}")
