import CheckGroupsProbeCases

/-!
Prints what CheckGroupsModel computes for the grammars of CheckGroupsProbe.hs,
in the format of its `expect` mode. The oracle of each grammar is built from
the tables that the probe writes: `classify`, `codeVariables` of each piece
of code, and `isUpper` and `toUpper` of the characters of the names.
-/

open PegHs.CheckGroups
open PegHs.LabelCheck (Loc Diagnostic)

def hexLower (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def esc (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c.toNat < 32 || c.toNat > 126 then "\\u{" ++ hexLower c.toNat ++ "}"
    else c.toString) ++ "\""

def showL (l : Loc) : String := toString l.file ++ ":" ++ toString l.line ++ ":" ++ toString l.col

-- `S.toList`: distinct and ascending.
def names (xs : List String) : String :=
  ",".intercalate ((xs.eraseDups.mergeSort (fun a b => decide (a ≤ b))).map esc)

def diags (tag : String) (ds : List Diagnostic) : List String :=
  ds.map fun d => tag ++ " " ++ showL d.loc ++ " " ++ esc d.msg

def oracle (d : Data) : Oracle :=
  { classes := ⟨d.units, d.unknown, d.generated, d.dataTypes⟩
    codeVariables := fun l c => ((d.codes.find? (fun e => e.1.1 == l && e.1.2 == c)).map (·.2)).getD []
    isUpper := fun c => d.upper.contains c.toNat
    toUpper := fun c => match d.toUpper.find? (·.1 == c.toNat) with
      | some (_, u) => Char.ofNat u
      | none => c }

def report (name : String) (g : Grammar) (d : Data) : List String :=
  let o := oracle d
  let c := o.classes
  let nullable := nullableRules g.rules
  ["case " ++ name] ++
  (match check g o with
    | .error ds => diags "error" ds
    | .ok a => ["ok " ++ esc a.start, "lr " ++ names a.leftRecursive, "nullable " ++ names a.nullable,
        "units " ++ names a.units]) ++
  diags "library" (checkLibrary g o) ++
  ["nullable-rec " ++ names (nullableRulesWith (recovery g) g.rules),
   "lr-rec " ++ names (leftRecursiveRules (recovery g) g.rules)] ++
  (g.rules.flatMap fun r =>
    diags ("repetition " ++ esc r.name) (repetitionErrors nullable r) ++
    diags ("alt " ++ esc r.name) (altErrors true c.units (discardingRules g) (valuedRules g c) c.unknown r) ++
    diags ("altlib " ++ esc r.name) (altErrors false c.units (discardingRules g) (valuedRules g c) c.unknown r) ++
    diags ("binding " ++ esc r.name) (bindingReferenceErrors o.codeVariables r)) ++
  diags "constructor" (constructorErrors g c o.isUpper) ++
  diags "syntax-name" (syntaxNameErrors g o) ++
  diags "hygiene" (g.verbatim.flatMap hygieneErrors)

def main : IO Unit := do
  for (n, g, d) in cases do
    for line in report n g d do
      IO.println line
