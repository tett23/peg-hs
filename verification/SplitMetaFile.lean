import FileTopItems
import FastWindow
import Verbatim47Data

open PegHs.EnvironmentEval PegHs.MetaExecution

private def certificate (moduleName : String) (mode : Bool) (window : List Char)
    (startChar endChar remaining : Nat)
    (needsFit : Bool) : String :=
  let consumed := endChar - startChar
  let body := window.take consumed
  let piece := toString (repr body.head!) ++ " :: " ++
    toString (repr (String.ofList (body.drop 1))) ++ ".toList"
  let lookahead := toString (repr (String.ofList (window.drop consumed))) ++ ".toList"
  let modeText := if mode then "true" else "false"
  let header := "import FastWindow\nimport MetaExecution\nopen PegHs.EnvironmentEval PegHs.MetaExecution\nnamespace PegHs.MetaCertificate." ++ moduleName ++ "\ndef piece : List Char := " ++ piece ++ "\ndef lookahead : List Char := " ++ lookahead ++ "\ndef window : List Char := piece ++ lookahead\ndef startChar : Nat := " ++ toString startChar ++ "\ndef endChar : Nat := " ++ toString endChar ++ "\nset_option maxRecDepth 20000\nset_option maxHeartbeats 0\n"
  let check := "theorem invariant1_item_check : windowCheck (context " ++ modeText ++
    " window) 12000 (.call 1 1) window.length {} (.ok " ++ toString remaining ++
    " {}) = true := by decide +kernel\n"
  let run := "theorem invariant1_item_run : runFuel (context " ++ modeText ++
    " window) 12000 (.call 1 1) window.length {} = some (.ok " ++
    toString remaining ++ " {}) := " ++
    (if needsFit then "((windowCheck_iff _ _ _ _ _ _).mp invariant1_item_check).2\n"
      else "by decide +kernel\n")
  let fit := "theorem invariant1_item_fit : readsFit (context " ++ modeText ++
    " window) 12000 (.call 1 1) window.length {} = true := " ++
    "((windowCheck_iff _ _ _ _ _ _).mp invariant1_item_check).1\n"
  header ++ (if needsFit then check else "") ++ run ++ (if needsFit then fit else "") ++
    "end PegHs.MetaCertificate." ++ moduleName ++ "\n"

private def pieceTable (mode : Bool) (ranges : Array (Nat × Nat)) : String := Id.run do
  let name := if mode then "Syntax" else "Peg"
  let mut lines := #["import InitialWhitespace", "import Verbatim47Data"]
  for i in [:ranges.size] do
    if i != 47 then
      lines := lines.push ("import " ++ name ++ "Item" ++ toString i)
  lines := lines.push "set_option maxRecDepth 20000"
  lines := lines.push "set_option maxHeartbeats 0"
  lines := lines.push ("namespace PegHs.MetaPieces." ++ name)
  for i in [:ranges.size] do
    if i == 0 then
      lines := lines.push ("def piece0Rest : List Char := PegHs.MetaCertificate." ++
        name ++ "Item0.piece.tail")
      lines := lines.push "def piece0 : List Char := '%' :: piece0Rest"
    else if i == 47 then
      lines := lines.push
        "def piece47 : List Char := ['%', '{'] ++ PegHs.MetaExecution.Verbatim47Data.suffix0 ++ ['\\n', '\\n']"
    else
      lines := lines.push ("def piece" ++ toString i ++ " : List Char := PegHs.MetaCertificate." ++
        name ++ "Item" ++ toString i ++ ".piece")
  lines := lines.push ("def suffix" ++ toString ranges.size ++ " : List Char := []")
  for j in [:ranges.size] do
    let i := ranges.size - 1 - j
    lines := lines.push ("def suffix" ++ toString i ++ " : List Char := piece" ++
      toString i ++ " ++ suffix" ++ toString (i + 1))
  lines := lines.push "def extra : List Char := piece0Rest ++ suffix1"
  lines := lines.push "def source : List Char := PegHs.MetaExecution.wsWindow ++ extra"
  lines := lines.push "def pre0 : List Char := PegHs.MetaExecution.initialComments"
  lines := lines.push "theorem split0 : source = pre0 ++ suffix0 := by\n  simp [source, pre0, PegHs.MetaExecution.wsWindow, extra, suffix0, piece0, List.append_assoc]"
  for i in [:ranges.size] do
    lines := lines.push ("def pre" ++ toString (i + 1) ++ " : List Char := pre" ++
      toString i ++ " ++ piece" ++ toString i)
    lines := lines.push ("theorem split" ++ toString (i + 1) ++
      " : source = pre" ++ toString (i + 1) ++ " ++ suffix" ++
      toString (i + 1) ++ " := by\n  simpa only [pre" ++ toString (i + 1) ++
      ", suffix" ++ toString i ++ ", List.append_assoc] using split" ++ toString i)
  lines := lines.push ("end PegHs.MetaPieces." ++ name)
  return String.intercalate "\n" lines.toList ++ "\n"

private def verbatimStepCertificate (mode : Bool) : String :=
  let grammarName := if mode then "Syntax" else "Peg"
  let modeText := if mode then "true" else "false"
  String.intercalate "\n" [
    "import VerbatimItem47",
    "import " ++ grammarName ++ "Pieces",
    "open PegHs.EnvironmentEval PegHs.MetaExecution PegHs.MetaPieces." ++ grammarName,
    "namespace PegHs.MetaStep." ++ grammarName ++ "Step47",
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 0",
    "theorem step : Derives (context " ++ modeText ++
      " source) (.call 1 1) suffix47.length {} (.ok suffix48.length {}) := by",
    "  let rest := suffix48.tail",
    "  have follows : suffix48 = 'F' :: rest := by rfl",
    "  have pieceEq : piece47 = verbatimItem47 := rfl",
    "  have sourceEq : source = pre47 ++ verbatimItem47 ++ ('F' :: rest) := by",
    "    calc",
    "      source = pre47 ++ suffix47 := split47",
    "      _ = pre47 ++ (piece47 ++ suffix48) := rfl",
    "      _ = pre47 ++ (verbatimItem47 ++ ('F' :: rest)) := by rw [pieceEq, follows]",
    "      _ = pre47 ++ verbatimItem47 ++ ('F' :: rest) := by rw [List.append_assoc]",
    "  have h := invariant1_verbatim_item47 " ++ modeText ++ " pre47 rest",
    "  rw [← sourceEq] at h",
    "  have beginEq : verbatimItem47.length + ('F' :: rest).length = suffix47.length := by",
    "    rw [suffix47, List.length_append, pieceEq, follows]",
    "  have endEq : ('F' :: rest).length = suffix48.length := by rw [follows]",
    "  rw [beginEq, endEq] at h",
    "  exact h",
    "#print axioms step",
    "end PegHs.MetaStep." ++ grammarName ++ "Step47", ""]

private def stepCertificate (mode : Bool) (index rest : Nat) (final : Bool) : String :=
  if index == 47 then verbatimStepCertificate mode else
  let grammarName := if mode then "Syntax" else "Peg"
  let modeText := if mode then "true" else "false"
  let item := grammarName ++ "Item" ++ toString index
  let piece := grammarName ++ "Pieces"
  let header := "import ItemSourceSplit\nimport " ++ piece ++ "\nimport " ++ item ++
    "\nopen PegHs.EnvironmentEval PegHs.MetaExecution PegHs.MetaPieces." ++ grammarName ++
    "\nnamespace PegHs.MetaStep." ++ grammarName ++ "Step" ++ toString index ++
    "\nset_option maxRecDepth 20000\nset_option maxHeartbeats 0\n"
  let cert := "PegHs.MetaCertificate." ++ item ++ "."
  let suffix := "suffix" ++ toString index
  let next := "suffix" ++ toString (index + 1)
  let pre := "pre" ++ toString index
  let body := if final then
    "private theorem windowEq : " ++ suffix ++ " = " ++ cert ++
      "window := by simp [" ++ suffix ++ ", piece" ++ toString index ++
      ", " ++ next ++ ", " ++ cert ++ "window, " ++ cert ++ "lookahead]\n" ++
    "theorem step : Derives (context " ++ modeText ++ " source) (.call 1 1) " ++
      suffix ++ ".length {} (.ok " ++ next ++ ".length {}) := by\n" ++
    "  have split : source = " ++ pre ++ " ++ " ++ cert ++
      "window := by rw [split" ++ toString index ++ ", windowEq]\n" ++
    "  have h := invariant1_final_item_window " ++ modeText ++ " " ++ pre ++
      " " ++ cert ++ "window 12000 " ++ cert ++ "invariant1_item_run\n" ++
    "  rw [← split] at h\n  simpa [windowEq, " ++ next ++ "] using h\n"
  else
    "private theorem overlap : " ++ next ++ ".take " ++ cert ++
      "lookahead.length = " ++ cert ++ "lookahead := by decide +kernel\n" ++
    "private theorem windowEq : " ++ suffix ++ ".take " ++ cert ++
      "window.length = " ++ cert ++ "window := by\n" ++
    "  have p : piece" ++ toString index ++ " = " ++ cert ++ "piece := rfl\n" ++
    "  rw [" ++ suffix ++ ", p, " ++ cert ++ "window]\n" ++
    "  exact invariant1_window_from_parts _ _ _ overlap\n" ++
    "private theorem windowLen : " ++ cert ++ "window.length = piece" ++
      toString index ++ ".length + " ++ toString rest ++ " := by\n" ++
    "  have p : piece" ++ toString index ++ " = " ++ cert ++ "piece := rfl\n" ++
    "  have l : " ++ cert ++ "lookahead.length = " ++ toString rest ++
      " := by decide +kernel\n" ++
    "  calc\n    " ++ cert ++ "window.length = " ++ cert ++ "piece.length + " ++
      cert ++ "lookahead.length := by rw [" ++ cert ++ "window, List.length_append]\n" ++
    "    _ = piece" ++ toString index ++ ".length + " ++ toString rest ++
      " := by rw [← p, l]\n" ++
    "theorem step : Derives (context " ++ modeText ++ " source) (.call 1 1) " ++
      suffix ++ ".length {} (.ok " ++ next ++ ".length {}) := by\n" ++
    "  let window := " ++ cert ++ "window\n" ++
    "  let extra := " ++ suffix ++ ".drop window.length\n" ++
    "  have split : source = " ++ pre ++ " ++ (window ++ extra) := by\n" ++
    "    rw [split" ++ toString index ++ "]\n" ++
    "    have h := List.take_append_drop window.length " ++ suffix ++ "\n" ++
    "    rw [windowEq] at h\n    exact congrArg (" ++ pre ++ " ++ ·) h.symm\n" ++
    "  have h := invariant1_item_window " ++ modeText ++ " " ++ pre ++
      " window extra 12000 " ++ toString rest ++ " " ++ cert ++
      "invariant1_item_run " ++ cert ++ "invariant1_item_fit\n" ++
    "  rw [← split] at h\n" ++
    "  have lenTake := congrArg List.length windowEq\n" ++
    "  simp only [List.length_take] at lenTake\n" ++
    "  change (min window.length " ++ suffix ++ ".length) = window.length at lenTake\n" ++
    "  have wl : window.length = piece" ++ toString index ++
      ".length + " ++ toString rest ++ " := windowLen\n" ++
    "  have bound : window.length ≤ " ++ suffix ++ ".length := by omega\n" ++
    "  have beginEq : window.length + extra.length = " ++ suffix ++ ".length := by\n" ++
    "    simp only [extra, List.length_drop]\n    omega\n" ++
    "  have pieceEq : " ++ suffix ++ ".length = piece" ++ toString index ++
      ".length + " ++ next ++ ".length := by\n" ++
    "    simp only [" ++ suffix ++ ", List.length_append]\n" ++
    "  have endEq : " ++ toString rest ++ " + extra.length = " ++ next ++
      ".length := by omega\n" ++
    "  rw [beginEq, endEq] at h\n  exact h\n"
  header ++ body ++ "end PegHs.MetaStep." ++ grammarName ++ "Step" ++ toString index ++ "\n"

private def chainProof (mode : Bool) (count start stop : Nat) : String := Id.run do
  let grammarName := if mode then "Syntax" else "Peg"
  let modeText := if mode then "true" else "false"
  let mut lines := #["import FileItemChain", "import " ++ grammarName ++ "Pieces"]
  if stop < count then
    lines := lines.push ("import " ++ grammarName ++ "Chain" ++ toString stop)
  for i in [start:stop] do
    lines := lines.push ("import " ++ grammarName ++ "Step" ++ toString i)
  lines := lines.push ("namespace PegHs.MetaProof." ++ grammarName)
  lines := lines.push ("open PegHs.MetaExecution PegHs.MetaPieces." ++ grammarName)
  lines := lines.push "set_option maxRecDepth 20000"
  lines := lines.push "set_option maxHeartbeats 0"
  if stop == count then
    lines := lines.push ("def ends" ++ toString count ++ " : List Nat := []")
    lines := lines.push ("theorem steps" ++ toString count ++
      " : ItemSteps (context " ++ modeText ++ " source) suffix" ++ toString count ++
      ".length ends" ++ toString count ++ " := rfl")
  for j in [:stop - start] do
    let i := stop - 1 - j
    let k := toString i
    let next := toString (i + 1)
    let pieceSimp := if i == 0 || i == 47 then "piece" ++ k
      else "piece" ++ k ++ ", PegHs.MetaCertificate." ++ grammarName ++
        "Item" ++ k ++ ".piece"
    lines := lines.push ("def ends" ++ k ++ " : List Nat := suffix" ++ next ++
      ".length :: ends" ++ next)
    lines := lines.push ("private theorem progress" ++ k ++ " : suffix" ++ next ++
      ".length < suffix" ++ k ++ ".length := by\n  have positive : 0 < piece" ++
      k ++ ".length := by simp [" ++ pieceSimp ++ "]\n  simp only [suffix" ++ k ++
      ", List.length_append]\n  omega")
    lines := lines.push ("theorem steps" ++ k ++ " : ItemSteps (context " ++
      modeText ++ " source) suffix" ++ k ++ ".length ends" ++ k ++
      " := ⟨PegHs.MetaStep." ++ grammarName ++ "Step" ++ k ++
      ".step, progress" ++ k ++ ", steps" ++ next ++ "⟩")
  lines := lines.push ("end PegHs.MetaProof." ++ grammarName)
  return String.intercalate "\n" lines.toList ++ "\n"

private def finalFileProof (mode : Bool) : String :=
  let grammarName := if mode then "Syntax" else "Peg"
  let modeText := if mode then "true" else "false"
  String.intercalate "\n" [
    "import " ++ grammarName ++ "Chain0",
    "namespace PegHs.MetaProof." ++ grammarName,
    "open PegHs.MetaExecution PegHs.MetaPieces." ++ grammarName,
    "set_option maxRecDepth 20000",
    "set_option maxHeartbeats 0",
    "theorem invariant1_file_result : FileResult " ++ modeText ++
      " source (.ok 0 {}) := by",
    "  have start : suffix0.length = 1 + extra.length := by",
    "    calc",
    "      suffix0.length = piece0.length + suffix1.length := by rw [suffix0, List.length_append]",
    "      _ = 1 + (piece0Rest.length + suffix1.length) := by rw [piece0, List.length_cons]; omega",
    "      _ = 1 + extra.length := by rw [extra, List.length_append]",
    "  have h := steps0",
    "  rw [start] at h",
    "  exact invariant1_file_from_item_steps " ++ modeText ++ " extra ends0 h",
    "#print axioms invariant1_file_result",
    "end PegHs.MetaProof." ++ grammarName, ""]

private def split (mode : Bool) (path : String) (outDir : Option String) : IO Unit := do
  let source ← IO.FS.readFile ⟨path⟩
  let input := source.toList
  let ctx := context mode input
  let some (.ok afterWs wsEnv) := runFuel ctx 12000 (.call 0 4) input.length {}
    | throw (IO.userError s!"Ws did not succeed: {path}")
  let mut remaining := afterWs
  let mut env := { wsEnv with resultDepth := 0 }
  let mut count := 0
  let mut replayable := 0
  let mut ranges : Array (Nat × Nat) := #[]
  IO.println s!"{path}: chars={input.length} wsEnd={input.length - afterWs}"
  for _ in [:input.length + 1] do
    match runFuel ctx 12000 (.call 1 1) remaining env with
    | some (.ok rest inner) =>
      unless rest < remaining do
        throw (IO.userError s!"TopItem did not consume at {remaining}: {path}")
      unless env == {} && inner == {} do
        throw (IO.userError s!"TopItem environment differs at {remaining}: {path}")
      let consumed := remaining - rest
      let chooseWindow (lookahead : Nat) :=
        (input.drop (input.length - remaining)).take (consumed + lookahead)
      let short := chooseWindow 16
      let shortCtx := context mode short
      let (shortFit, shortResult) := fastWindow shortCtx 12000 (.call 1 1) short.length env
      let useShort := shortFit && shortResult == some (.ok (short.length - consumed) inner)
      let window := if useShort then short else chooseWindow 128
      let windowCtx := context mode window
      let (fitted, localResult) := if useShort then (shortFit, shortResult)
        else fastWindow windowCtx 12000 (.call 1 1) window.length env
      let isFinal := rest == 0
      if (fitted || isFinal) && localResult == some (.ok (window.length - consumed) inner) then
        replayable := replayable + 1
      else
        IO.println s!"unreplayable item={count} fit={fitted} local={repr localResult}"
      if let some dir := outDir then
        let moduleName := (if mode then "Syntax" else "Peg") ++ s!"Item{count}"
        let code := certificate moduleName mode window
          (input.length - remaining) (input.length - rest) (window.length - consumed) (!isFinal)
        IO.FS.writeFile ⟨dir ++ "/" ++ moduleName ++ ".lean"⟩ code
        let stepName := (if mode then "Syntax" else "Peg") ++ s!"Step{count}"
        IO.FS.writeFile ⟨dir ++ "/" ++ stepName ++ ".lean"⟩
          (stepCertificate mode count (window.length - consumed) isFinal)
      IO.println s!"item={count} start={input.length - remaining} end={input.length - rest}"
      ranges := ranges.push (input.length - remaining, input.length - rest)
      count := count + 1
      if count % 20 == 0 then IO.eprintln s!"{path}: checked {count} items"
      env := { inner with resultDepth := max env.resultDepth inner.resultDepth }
      remaining := rest
    | some .fail => break
    | some (.throwLabel pos name _) =>
      throw (IO.userError s!"TopItem threw {name} at {pos}: {path}")
    | none => throw (IO.userError s!"TopItem ran out of fuel: {path}")
  unless remaining == 0 do
    throw (IO.userError s!"TopItem stopped before EOF at {remaining}: {path}")
  unless runFuel ctx 12000 (.terminal 0) 0 env == some .fail do
    throw (IO.userError s!"EOF test failed: {path}")
  if let some dir := outDir then
    unless ranges.size > 0 && ranges[0]!.1 == 349 && input[349]? == some '%' &&
        ranges[ranges.size - 1]!.2 == input.length do
      throw (IO.userError s!"piece boundaries do not cover the file: {path}")
    let (verbStart, verbEnd) := ranges[47]!
    let actualVerb := (input.drop verbStart).take (verbEnd - verbStart)
    let certifiedVerb := ['%', '{'] ++ Verbatim47Data.suffix0 ++ ['\n', '\n']
    unless actualVerb == certifiedVerb do
      throw (IO.userError s!"verbatim certificate does not match item 47: {path}")
    let name := if mode then "Syntax" else "Peg"
    IO.FS.writeFile ⟨dir ++ "/" ++ name ++ "Pieces.lean"⟩
      (pieceTable mode ranges)
    for start in [0:ranges.size] do
      if start % 20 == 0 then
        let stop := min (start + 20) ranges.size
        IO.FS.writeFile ⟨dir ++ "/" ++ name ++ "Chain" ++ toString start ++ ".lean"⟩
          (chainProof mode ranges.size start stop)
    IO.FS.writeFile ⟨dir ++ "/" ++ name ++ "Full.lean"⟩
      (finalFileProof mode)
  IO.println s!"{path}: items={count} replayable={replayable} remaining={remaining}"

def main (paths : List String) : IO Unit := do
  match paths with
  | [peg, syntaxPath] =>
    split false peg none
    split true syntaxPath none
  | [peg, syntaxPath, outDir] =>
    split false peg (some outDir)
    split true syntaxPath (some outDir)
  | _ => throw (IO.userError "expected Peg.hpeg and PegSyntax.hpeg")
