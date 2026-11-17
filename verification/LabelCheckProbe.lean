import LabelCheckProbeCases

/-!
Prints what LabelCheckModel computes for the grammars of LabelCheckProbe.hs,
in the format of its `expect` mode. A fuel that does not suffice for a label
prints a line the Haskell side never prints, so the comparison fails.
-/

open PegHs.LabelCheck

def fuel : Nat := 1000000

def hexLower (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def esc (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\"
    else if c == '"' then "\\\""
    else if c.toNat < 32 || c.toNat > 126 then "\\u{" ++ hexLower c.toNat ++ "}"
    else c.toString) ++ "\""

def showL (l : Loc) : String := toString l.file ++ ":" ++ toString l.line ++ ":" ++ toString l.col

def located (p : Loc × String) : String := showL p.1 ++ " " ++ esc p.2

mutual
def showExpr : Expr → String
  | .lit t w => "(lit " ++ esc t ++ " " ++ esc w ++ ")"
  | .cls rs w => "(cls [" ++ ",".intercalate (rs.map fun p => toString p.1.val ++ "-" ++ toString p.2.val) ++ "] " ++ esc w ++ ")"
  | .any => "any"
  | .ref l n as => "(ref " ++ showL l ++ " " ++ esc n ++ " [" ++ ",".intercalate (as.map located) ++ "])"
  | .group alts => "(group [" ++ " | ".intercalate (showAlts alts) ++ "])"
  | .star x => "(star " ++ showExpr x ++ ")"
  | .plus x => "(plus " ++ showExpr x ++ ")"
  | .opt x => "(opt " ++ showExpr x ++ ")"
  | .and x => "(and " ++ showExpr x ++ ")"
  | .not x => "(not " ++ showExpr x ++ ")"
  | .capture x => "(capture " ++ showExpr x ++ ")"
  | .label l x n => "(label " ++ showL l ++ " " ++ showExpr x ++ " " ++ esc n ++ ")"
  | .pred b c => "(pred " ++ (if b then "true" else "false") ++ " " ++ located c ++ ")"
  | .template l n as vs => "(template " ++ showL l ++ " " ++ esc n ++ " [" ++ ",".intercalate (showList as) ++ "] [" ++ ",".intercalate (vs.map located) ++ "])"
  | .discard x => "(discard " ++ showExpr x ++ ")"
termination_by e => sizeOf e

def showItems : List Item → List String
  | [] => []
  | (l, b, e) :: is => (showL l ++ "/" ++ (match b with | some b => esc b | none => "-") ++ "/" ++ showExpr e) :: showItems is
termination_by is => sizeOf is

def showAlts : List (List Item) → List String
  | [] => []
  | a :: as => " ".intercalate (showItems a) :: showAlts as
termination_by as => sizeOf as

def showList : List Expr → List String
  | [] => []
  | e :: es => showExpr e :: showList es
termination_by es => sizeOf es
end

def sortNames (xs : List String) : List String :=
  (xs.eraseDups).mergeSort (fun a b => decide (a ≤ b))

def report (name : String) (g : Grammar) : List String :=
  let s := stripLabelsAs "Stripped" g
  let lr := leftRecursion g.rules
  ["case " ++ name] ++
  (match labelWarningsFuel fuel g with
    | some ws => ws.map (fun d => "warning " ++ showL d.loc ++ " " ++ esc d.msg)
    | none => ["the fuel does not suffice"]) ++
  ["module " ++ located s.module,
   "entries " ++ "; ".intercalate (s.entries.map located),
   "cleared " ++ toString s.recovers.length ++ " " ++ toString s.safe.length ++ " " ++ toString s.messages.length] ++
  (s.rules.flatMap fun r =>
    ("rule " ++ esc r.name ++ " " ++ ",".intercalate (r.params.map esc)) ::
      r.alts.flatMap fun a => ("alt " ++ showL a.loc) :: (showItems a.items).map (fun i => "item " ++ i)) ++
  ["others True",
   "direct " ++ ",".intercalate (sortNames lr.1),
   "other " ++ ",".intercalate (sortNames lr.2.1),
   "growing " ++ ",".intercalate (g.rules.flatMap fun r =>
     ((List.range r.alts.length).filter (lr.2.2 r.name)).map fun i => r.name ++ ":" ++ toString i),
   "nullable " ++ ",".intercalate (sortNames (nullableRules g.rules))]

def main : IO Unit := do
  for (n, g) in cases do
    for line in report n g do
      IO.println line
