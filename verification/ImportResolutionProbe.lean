import ImportResolution

-- The Lean side of the differential probe of `resolveImports`.
-- check-import-resolution.sh appends `cases` and `main`, written by
-- ImportResolutionProbe.hs, and compares the output with that of Haskell.

open PegHs.ImportResolution

-- `Loc`: file, line, column.
structure PLoc where
  file : Nat
  line : Nat
  column : Nat

structure PDiag where
  loc : PLoc
  message : String

-- A rule: its name, `ruleLoc` and `ruleRefs`.
structure PRule where
  name : String
  loc : PLoc
  refs : List String

structure Case where
  name : String
  isLibrary : Bool
  rootRules : List PRule
  directiveNames : List String
  imports : List (PLoc × String)
  libraries : List (String × Library PDiag PRule)

-- The derived `Ord Loc`.
def locLE (a b : PLoc) : Bool :=
  a.file < b.file || (a.file == b.file &&
    (a.line < b.line || (a.line == b.line && a.column ≤ b.column)))

def renderLoc (l : PLoc) : String := s!"{l.file}:{l.line}:{l.column}"

def runCase (c : Case) : List String :=
  let lookupLibrary (p : String) : Library PDiag PRule :=
    match c.libraries.lookup p with
    | some l => l
    | none => .noText
  let result := resolve c.isLibrary ⟨⟨0, 1, 1⟩, "missing %module directive"⟩ c.rootRules
    c.directiveNames c.imports lookupLibrary
    (fun i d => { d with loc := { d.loc with file := i } })
    (fun i r => { r with loc := { r.loc with file := i } })
    (fun l p => ⟨l, "cannot import " ++ p ++ ": no such file"⟩)
    (fun l p => ⟨l, p ++ " is not a library: it has no %library directive"⟩)
    (fun a b => locLE a.loc b.loc) PRule.name (fun r => r.loc.file) PRule.refs
    (fun r => ⟨r.loc, "duplicate definition of " ++ r.name⟩)
  match result with
  | .error ds => (c.name ++ " error") :: ds.map (fun d => "  " ++ renderLoc d.loc ++ ": " ++ d.message)
  | .ok rs => (c.name ++ " ok") :: rs.map (fun r => "  " ++ r.name ++ " " ++ renderLoc r.loc)

