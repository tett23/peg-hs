import TemplateExpansionWholeData

-- The model's side of the probe: the grammars that
-- TemplateExpansionWholeProbe.hs parsed, expanded by `expandTemplatesRun`
-- and written as the Haskell side writes the real `expandTemplates`.
open PegHs.TemplateExpansionWhole PegHs.TemplateSubstitution

def env : Env where
  idents := fun s => ((identTable.find? (·.1 == s)).map (·.2)).getD ["?missing " ++ s]
  instanceType := fun _ _ => "?"

mutual
def render : Expr → String
  | .lit _ w => "(lit " ++ w ++ ")"
  | .charClass w => "(class " ++ w ++ ")"
  | .any => "any"
  | .ref l n args => "(ref@" ++ toString l ++ " " ++ n ++ " [" ++ ",".intercalate args ++ "])"
  | .group alts => "(group " ++ " / ".intercalate (renderAlts alts) ++ ")"
  | .star x => "(star " ++ render x ++ ")"
  | .plus x => "(plus " ++ render x ++ ")"
  | .opt x => "(opt " ++ render x ++ ")"
  | .and x => "(and " ++ render x ++ ")"
  | .not x => "(not " ++ render x ++ ")"
  | .capture x => "(capture " ++ render x ++ ")"
  | .label l x n => "(label@" ++ toString l ++ " " ++ render x ++ " " ++ n ++ ")"
  | .predicate b c => "(pred " ++ (if b then "T" else "F") ++ " {" ++ c ++ "})"
  | .template l n args vals =>
    "(template@" ++ toString l ++ " " ++ n ++ " [" ++ " ".intercalate (renderArgs args) ++ "] [" ++
      ",".intercalate vals ++ "])"
  | .discard x => "(discard " ++ render x ++ ")"

def renderArgs : List Expr → List String
  | [] => []
  | a :: as => render a :: renderArgs as

def renderItems : List Item → List String
  | [] => []
  | (b, e) :: is => ((b.map (· ++ ":")).getD "" ++ render e) :: renderItems is

def renderAlts : List (List Item) → List String
  | [] => []
  | items :: alts => " ".intercalate (renderItems items) :: renderAlts alts
end

def renderRule (r : Rule) : List String :=
  ("rule " ++ r.name ++ " @" ++ toString r.location ++ " params=" ++
    ",".intercalate (r.params.map fun p => p.1 ++ ":" ++ p.2) ++ " tparams=" ++
    ",".intercalate (r.templateParams.map fun p => p.1 ++ (p.2.map ("::" ++ ·)).getD "") ++
    " annotation=" ++ (r.annotation.map toString).getD "-") ::
  r.alts.flatMap fun a =>
    ("  alt " ++ (a.action.map fun t => "{" ++ t ++ "}").getD "-" ++
      " constructor=" ++ a.constructor.getD "-") ::
      (renderItems a.items).map ("    " ++ ·)

def project (name : String) : Option (Except (List Diagnostic) Grammar) → List String
  | none => ["case " ++ name, "out of fuel"]
  | some (.error ds) => ("case " ++ name) :: "error" :: ds.map fun d => "  " ++ toString d.1 ++ " " ++ d.2
  | some (.ok g) => ("case " ++ name) :: "ok" :: g.rules.flatMap renderRule ++
      g.inline.map fun l => "inline " ++ toString l.1 ++ " " ++ l.2

def main : IO Unit := do
  for (name, g) in cases do
    for line in project name (expandTemplatesRun env (fun _ => []) 100000 g) do
      IO.println line
