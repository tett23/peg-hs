import Parsing
import TotalFile
import AssembleValidation
import CheckGroupsModel

/-!
The Lean side of the boundary rows of ADR 0097 (the table of its invariants
section). Each line is named by its row's invariants and compared, by
check.sh, with the line that Boundary.hs prints from the public entries:
- rows 1 and 2: the extracted metagrammar on the input (MetaExecution.parseFile,
  the translated parseTops on the recognizer) and, for the empty file, the
  AssembleValidation model on no top item;
- row 3: the depth predicate of Parsing;
- row 4: CheckGroupsModel's `check` on the grammar that `assemble` builds from
  `%module M` and `S <- Absent`. PublicGeneration.invariant2_undefined_reference_public
  carries this rejection to the public entry.
Row 5 is BoundaryDerivations.lean; row 6 is the GHC check in check.sh.
-/

open PegHs

def failure : PublicParsing.Failure → String := fun _ => "parse error"

def parsed (source : String) : String :=
  match MetaExecution.parseFile false source failure with
  | .ok () => "accept"
  | .error _ => "reject"

def undefinedReference : CheckGroups.Grammar where
  library := none
  start := none
  entries := []
  noMemo := []
  languages := []
  syntaxLoc := none
  tokens := []
  trivia := []
  inline := []
  recovers := []
  safe := []
  expects := []
  messages := []
  verbatim := []
  rules := [⟨"S", ⟨0, 2, 1⟩, [], 0, none,
    [⟨⟨0, 2, 6⟩, [(⟨0, 2, 6⟩, none, .ref ⟨0, 2, 6⟩ "Absent" [])], none, none⟩]⟩]

def oracle : CheckGroups.Oracle :=
  ⟨⟨[], [], [], []⟩, fun _ _ => [], fun c => c.isUpper, fun c => c.toUpper⟩

def main : IO Unit := do
  IO.println s!"ADR 0097 I1, I2: empty file: parse {parsed ""}"
  match AssembleValidation.assemble [] with
  | .ok () => IO.println "ADR 0097 I1, I2: empty file: generate ok"
  | .error es => for e in es do IO.println s!"ADR 0097 I1, I2: empty file: generate {e}"
  IO.println s!"ADR 0097 I1, I2: minimal grammar: parse {parsed "%module M\nS <- 'a'\n"}"
  IO.println s!"ADR 0097 I1, I2: trailing character: parse {parsed "%module M\nS <- 'a'\n]"}"
  for count in [0, 1, 254, 255, 256, 257, 258] do
    let accepted := (List.range count).all PegVerification.withinDepth
    IO.println s!"ADR 0097 I1, I2: depth {count}: {if accepted then "accept" else "reject"}"
  match CheckGroups.check undefinedReference oracle with
  | .ok _ => IO.println "ADR 0097 I2: undefined reference: ok"
  | .error ds =>
    for (d : LabelCheck.Diagnostic) in ds do
      IO.println s!"ADR 0097 I2: undefined reference: {d.loc.file}:{d.loc.line}:{d.loc.col} {d.msg}"
