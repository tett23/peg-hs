import RenderPrintingProbeCases

/-!
Runs RenderPrinting's model on the trees of RenderPrintingProbe.hs.

With `text`, prints `render` of each tree in the format of the probe's
`expect` mode. With `lexids`, prints the terminal IDs that GHC's lexer should
pass to the parser for the probe's `module` mode: `module P where` and an
opening virtual brace, then `x = TEXT` for each tree with `lexModel`'s word,
each followed by a virtual semicolon. A tree that is not `valid`, or whose text
`lexModel` does not lex, prints a line that the other side never prints.
With `reserved`, prints RenderPrinting.reservedWords, one per line.
-/

open PegHs.RenderPrinting PegHs.CFG

def esc (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '\\' then "\\\\" else if c == '\n' then "\\n" else c.toString)

def ids (ts : List Symbol) : List String :=
  ts.map fun
    | .terminal n => toString n
    | .nonterminal n => s!"nonterminal {n}"

-- module, CONID, where, the virtual opening brace.
def header : List String := ["19", "118", "25", "103"]

-- VARID and '=' before each tree, and the virtual semicolon that the layout
-- rule puts at the start of the next line.
def declaration (e : PExpr) : List String :=
  if valid e then
    match lexModel (render e) with
    | some ts => ["117", "77"] ++ ids ts ++ ["113"]
    | none => ["unlexed " ++ esc (render e)]
  else ["invalid " ++ esc (render e)]

def main (args : List String) : IO Unit := do
  match args with
  | ["text"] => for e in cases do IO.println ("text " ++ esc (render e))
  | ["lexids"] =>
    for line in header ++ (cases.map declaration).flatten do IO.println line
  | ["reserved"] => for w in reservedWords do IO.println w
  | _ => throw (IO.userError "usage: RenderPrintingProbe (text|lexids|reserved)")
