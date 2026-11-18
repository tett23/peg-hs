import Lean

/-!
# The proof graph of ADR 0097

Reads the compiled modules and writes Mermaid figures of how the theorems use
one another. proof-graph.sh runs it; see the "実行方法" section of README.md.

    lean --run ProofGraph.lean STAGES CHAIN DEPTH OUT ROOT_MODULE...

- STAGES: proof-graph-stages.tsv. Each line maps a module (or a prefix ending
  in `*`) to a stage and to how the stage is tied to the implementation
  (`translated`, `model` or `certificate`).
- CHAIN: a file, or `-` for the standard input, of lines
  `N<TAB>name<TAB>module` for the theorems of the chain tables of README.md;
  `N` is the invariant.
- DEPTH: the theorems at most DEPTH uses away from a public entry stay as nodes
  in the per-invariant figures.
- OUT: the directory for overview.md and invariant1.md to invariant3.md.
- ROOT_MODULE: the modules of the public entries. Their theorems whose names
  start with `invariant` are the roots.

A node of the theorem graph is a theorem of a module outside Init, Lean, Std
and Lake, or a definition named in CHAIN. An edge `a → b` means that the value
of `a` refers to `b`, possibly through auxiliary declarations (`proof_N`,
`match_N`, `eq_N`, names with a component starting with `_`) that belong to a
theorem. The projections of a structure named `Premises` are premise nodes;
so are the hypotheses of a root whose types are universally quantified
propositions.
-/

open Lean Meta

namespace ProofGraph

def libraryRoots : List String := ["Init", "Lean", "Std", "Lake"]

def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

def auxComponent (s : String) : Bool :=
  s.startsWith "_" || s == "eq_def" || s == "induct" || s == "mutual_induct" ||
    s == "fun_cases" || s == "brecOn" || s == "below" || s == "casesOn" || s == "rec" ||
    s == "recOn" || s == "noConfusion" || s == "noConfusionType" || s == "sizeOf_spec" || s == "injEq" || s == "inj" ||
    ["proof_", "match_", "eq_", "splitter", "_unfold"].any fun p =>
      s.startsWith p && isDigits (s.drop p.length).toString

def userName (n : Name) : Name := (privateToUserName? n).getD n

def isAuxName (n : Name) : Bool :=
  let rec go : Name → Bool
    | .anonymous => false
    | .str pre s => auxComponent s || go pre
    | .num _ _ => true
  go (userName n)

/-- The declaration an auxiliary declaration belongs to: drop trailing auxiliary components. -/
def owner : Name → Name
  | n@(.str pre s) => if auxComponent s then owner pre else n
  | .num pre _ => owner pre
  | .anonymous => .anonymous

def shortName (n : Name) : String :=
  match userName n with
  | .str _ s => s
  | n => n.toString

inductive Report where
  | translated | model | certificate | unknown
  deriving BEq, Hashable, Repr, Inhabited

def Report.parse : String → Report
  | "translated" => .translated
  | "model" => .model
  | "certificate" => .certificate
  | _ => .unknown

def Report.cls : Report → String
  | .translated => "translated"
  | .model => "model"
  | .certificate => "certificate"
  | .unknown => "unknown"

def Report.label : Report → String
  | .translated => "翻訳を検証済み"
  | .model => "モデルを検証済み"
  | .certificate => "証明書を検証済み"
  | .unknown => "未分類"

structure StageRule where
  pattern : String
  stage : String
  report : Report

def StageRule.matches (r : StageRule) (m : String) : Bool :=
  if r.pattern.endsWith "*" then m.startsWith (r.pattern.dropEnd 1).toString else m == r.pattern

def unclassified : String := "未分類"

/-- The first rule that matches the module wins. -/
def stageOf (rules : Array StageRule) (m : Name) : String × Report :=
  match rules.find? (·.matches m.toString) with
  | some r => (r.stage, r.report)
  | none => (unclassified, .unknown)

def parseRules (text : String) : Array StageRule := Id.run do
  let mut out := #[]
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [p, s, r] => out := out.push { pattern := p, stage := s, report := Report.parse r }
    | _ => pure ()
  out

/-- A target of an edge: a node of the theorem graph or a premise. -/
inductive Target where
  | node (n : Name)
  | premise (label : String)
  deriving BEq, Hashable, Inhabited

structure Ctx where
  env : Environment
  moduleOf : Name → Option Name
  nodes : Std.HashSet Name

def Ctx.isProject (c : Ctx) (n : Name) : Bool :=
  match c.moduleOf n with
  | some m => !libraryRoots.contains m.getRoot.toString
  | none => false

/-- Constants and structure projections that occur in an expression. -/
def occurrences (e : Expr) : IO (Array Name × Array (Name × Nat)) := do
  let consts ← IO.mkRef (∅ : Std.HashSet Name)
  let projs ← IO.mkRef (∅ : Std.HashSet (Name × Nat))
  e.forEach fun
    | .const n _ => consts.modify (·.insert n)
    | .proj s i _ => projs.modify (·.insert (s, i))
    | _ => pure ()
  return ((← consts.get).toArray, (← projs.get).toArray)

def premiseStructure (s : Name) : Bool :=
  match s with
  | .str _ "Premises" => true
  | _ => false

def premiseLabel (s : Name) (field : String) : String :=
  s!"{shortName s}.{field}"

/-- The targets in the value of `n`, and the auxiliary declarations to look through. -/
def step (c : Ctx) (n : Name) : IO (Array Target × Array Name) := do
  let some info := c.env.find? n | return (#[], #[])
  let some value := info.value? (allowOpaque := true) | return (#[], #[])
  let mut aux := #[]
  let (consts, projs) ← occurrences value
  let mut out : Std.HashSet Target := {}
  for (s, i) in projs do
    if premiseStructure s then
      let field := (getStructureFields c.env s)[i]?.map toString |>.getD (toString i)
      out := out.insert (.premise (premiseLabel s field))
  for k in consts do
    if k == n then continue
    if let some info := c.env.getProjectionFnInfo? k then
      let s := info.ctorName.getPrefix
      if premiseStructure s then
        out := out.insert (.premise (premiseLabel s (shortName k)))
        continue
    if !c.isProject k then continue
    if c.nodes.contains k then
      out := out.insert (.node k)
      continue
    if isAuxName k then
      let o := owner k
      let throughOwner := match c.env.find? o with
        | some oi => oi.isTheorem || c.nodes.contains o
        | none => true
      if throughOwner then aux := aux.push k
  return (out.toArray, aux)

/-- Targets reachable from the value of `n` through auxiliary declarations. -/
def targetsOf (c : Ctx) (n : Name) : IO (Array Target) := do
  let mut out : Std.HashSet Target := {}
  let mut seen : Std.HashSet Name := {n}
  let mut todo := #[n]
  while !todo.isEmpty do
    let m := todo.back!
    todo := todo.pop
    let (ts, aux) ← step c m
    for t in ts do out := out.insert t
    for a in aux do
      if !seen.contains a then
        seen := seen.insert a
        todo := todo.push a
  return out.toArray

/-! ## Mermaid -/

def header : String :=
  "flowchart TD\n" ++
  "  classDef translated fill:#d9f2d9,stroke:#2e7d32,color:#000\n" ++
  "  classDef model fill:#fff2c2,stroke:#a07800,color:#000\n" ++
  "  classDef certificate fill:#d6e4ff,stroke:#1f4e9e,color:#000\n" ++
  "  classDef mixed fill:#eadcf5,stroke:#6a3d9a,color:#000\n" ++
  "  classDef unknown fill:#eeeeee,stroke:#666666,color:#000\n" ++
  "  classDef root fill:#ffffff,stroke:#000000,stroke-width:3px,color:#000\n" ++
  "  classDef premise fill:#fde2e2,stroke:#b03030,stroke-dasharray:4 3,color:#000\n"

def esc (s : String) : String :=
  s.replace "\"" "#quot;"

structure Figure where
  lines : Array String := #[]
  nodes : Nat := 0
  edges : Nat := 0

def Figure.node (f : Figure) (line : String) : Figure :=
  { f with lines := f.lines.push line, nodes := f.nodes + 1 }

def Figure.edge (f : Figure) (line : String) : Figure :=
  { f with lines := f.lines.push line, edges := f.edges + 1 }

def Figure.text (f : Figure) : String :=
  "```mermaid\n" ++ header ++ String.intercalate "\n" f.lines.toList ++ "\n```\n"

/-- Hypotheses of `n` whose types are universally quantified propositions, and whether the proof uses them. -/
def premiseArgs (env : Environment) (n : Name) : IO (Array (String × Bool)) := do
  let some info := env.find? n | return #[]
  let some value := info.value? (allowOpaque := true) | return #[]
  let go : MetaM (Array (String × Bool)) :=
    forallTelescope info.type fun xs _ => do
      let mut out := #[]
      let body := value.getLambdaBody
      let arity := value.getNumHeadLambdas
      for h : i in [0:xs.size] do
        let decl ← xs[i].fvarId!.getDecl
        if decl.type.isForall && (← isProp decl.type) then
          let used := i < arity && body.hasLooseBVar (arity - 1 - i)
          out := out.push (decl.userName.toString, used)
      return out
  let ctx : Core.Context := { fileName := "<ProofGraph>", fileMap := default }
  let (r, _) ← (go.run' {} {}).toIO ctx { env }
  return r

end ProofGraph

open ProofGraph in
def main (args : List String) : IO UInt32 := do
  let stagesPath :: chainPath :: depthText :: out :: rootModules := args
    | IO.eprintln "usage: lean --run ProofGraph.lean STAGES CHAIN DEPTH OUT ROOT_MODULE..."; return 2
  let some depth := depthText.toNat? | IO.eprintln s!"DEPTH must be a number: {depthText}"; return 2
  let rules := parseRules (← IO.FS.readFile stagesPath)
  let chainText ← if chainPath == "-" then (← IO.getStdin).readToEnd else IO.FS.readFile chainPath
  if chainText.isEmpty then IO.eprintln "no chain rows"; return 1
  let chain := chainText.splitOn "\n" |>.filterMap fun line =>
    match line.splitOn "\t" with
    | [k, name, m] => k.toNat?.map (·, name, m)
    | _ => none
  initSearchPath (← findSysroot)
  let roots := rootModules.map String.toName
  let env ← importModules (roots.map ({ module := · })).toArray {}
  let names := env.header.moduleNames
  let moduleOf (n : Name) : Option Name := (env.getModuleIdxFor? n).bind (names[·.toNat]?)
  let isProject (n : Name) : Bool := match moduleOf n with
    | some m => !libraryRoots.contains m.getRoot.toString
    | none => false
  -- Resolve the chain names to constants of the named modules.
  let mut chainNodes : Array (Nat × Name) := #[]
  let mut problems : Array String := #[]
  let mut byShort : Std.HashMap (String × Name) (Array Name) := {}
  let mut theorems : Std.HashSet Name := {}
  for (n, info) in env.constants.toList do
    if !isProject n || isAuxName n then continue
    let some m := moduleOf n | continue
    byShort := byShort.alter (shortName n, m) fun a => some ((a.getD #[]).push n)
    if info.isTheorem then theorems := theorems.insert n
  for (k, name, m) in chain do
    let file := (m.dropEnd ".lean".length).toString
    match byShort[(name, file.toName)]? with
    | some ns => for n in ns do chainNodes := chainNodes.push (k, n)
    | none =>
      let why := if names.contains file.toName then "に無い" else "を根のモジュールが import していない"
      problems := problems.push s!"README の不変条件 {k} の表の {name}: {m} {why}"
  let nodes := chainNodes.foldl (fun s (_, n) => s.insert n) theorems
  let c : Ctx := { env, moduleOf, nodes }
  -- The graph over every node.
  let mut graph : Std.HashMap Name (Array Target) := {}
  for n in nodes do
    graph := graph.insert n (← targetsOf c n)
  let nodeTargets (n : Name) : Array Name :=
    (graph.getD n #[]).filterMap fun | .node k => some k | _ => none
  let rootNodes := (nodes.toArray.filter fun n =>
    theorems.contains n && (moduleOf n).any roots.contains &&
      (shortName n).startsWith "invariant").qsort (·.toString < ·.toString)
  -- Every node reachable from the roots.
  let reachable := Id.run do
    let mut seen : Std.HashSet Name := {}
    let mut stack := rootNodes.toList
    while !stack.isEmpty do
      match stack with
      | [] => pure ()
      | n :: rest =>
        stack := rest
        if seen.contains n then continue
        seen := seen.insert n
        stack := (nodeTargets n).toList ++ stack
    seen
  let stageTable : Std.HashMap Name (String × Report) :=
    names.foldl (init := {}) fun m n => m.insert n (stageOf rules n)
  let stage (n : Name) : String × Report :=
    (moduleOf n).bind (stageTable[·]?) |>.getD (unclassified, .unknown)
  -- Unclassified modules.
  let unmapped := (reachable.toArray.filterMap fun n =>
    if (stage n).1 == unclassified then moduleOf n else none).toList.eraseDups
  for m in unmapped do problems := problems.push s!"段の無いモジュール {m}"
  IO.FS.createDirAll out
  let mut sizes : Array String := #[]
  /- Overview: roots and stages. -/
  let stages := (reachable.toArray.filter (!rootNodes.contains ·)).map (stage · |>.1)
    |>.toList.eraseDups.toArray.qsort (· < ·)
  let stageId (s : String) : String := s!"s{(stages.idxOf? s).getD 0}"
  let stageReports (s : String) : List Report :=
    (reachable.toArray.filterMap fun n =>
      if !rootNodes.contains n && (stage n).1 == s then some (stage n).2 else none)
      |>.toList.eraseDups
  let mut fig : Figure := {}
  for s in stages do
    let reps := stageReports s
    let cls := match reps with | [r] => r.cls | _ => "mixed"
    let label := String.intercalate "・" (reps.map Report.label)
    fig := fig.node s!"  {stageId s}[\"{esc s}<br/>〔{label}〕\"]:::{cls}"
  for h : i in [0:rootNodes.size] do
    fig := fig.node s!"  r{i}([\"{esc (shortName rootNodes[i])}\"]):::root"
  let mut stageEdges : Std.HashMap (String × String) Nat := {}
  let mut premiseUse : Std.HashMap (String × String) Unit := {}
  for n in reachable do
    let src := match rootNodes.idxOf? n with
      | some i => s!"r{i}"
      | none => stageId (stage n).1
    for t in graph.getD n #[] do
      match t with
      | .node k =>
        if rootNodes.contains k then
          let some j := rootNodes.idxOf? k | continue
          stageEdges := stageEdges.alter (src, s!"r{j}") (some <| ·.getD 0 + 1)
        else
          let dst := stageId (stage k).1
          if src != dst then stageEdges := stageEdges.alter (src, dst) (some <| ·.getD 0 + 1)
      | .premise p => premiseUse := premiseUse.insert (src, p) ()
  let premises := (premiseUse.toArray.map (·.1.2)).toList.eraseDups.toArray.qsort (· < ·)
  for h : i in [0:premises.size] do
    fig := fig.node s!"  p{i}\{\{\"{esc premises[i]}\"}}:::premise"
  for ((a, b), k) in stageEdges.toArray.qsort (fun x y => toString x.1 < toString y.1) do
    fig := fig.edge s!"  {a} -->|{k}| {b}"
  for ((a, p), _) in premiseUse.toArray.qsort (fun x y => toString x.1 < toString y.1) do
    fig := fig.edge s!"  {a} --o p{(premises.idxOf? p).getD 0}"
  IO.FS.writeFile (System.FilePath.mk out / "overview.md") fig.text
  sizes := sizes.push s!"overview.md: 節点 {fig.nodes}、辺 {fig.edges}、{fig.text.utf8ByteSize} バイト"
  /- One figure per invariant. -/
  for k in [1, 2, 3] do
    let pfx := s!"invariant{k}_"
    let rs := rootNodes.filter fun n => (shortName n).startsWith pfx
    -- Distances from the roots.
    let mut dist : Std.HashMap Name Nat := {}
    let mut frontier := rs.toList
    for r in rs do dist := dist.insert r 0
    let mut d := 0
    while !frontier.isEmpty do
      d := d + 1
      let mut next := []
      for n in frontier do
        for t in nodeTargets n do
          if !dist.contains t then
            dist := dist.insert t d
            next := t :: next
      frontier := next
    let wanted := chainNodes.filterMap fun (j, n) => if j == k then some n else none
    for n in wanted do
      if !dist.contains n then
        problems := problems.push s!"不変条件 {k} の表の {shortName n}（{(moduleOf n).getD .anonymous}）に根から届かない"
    let kept : Std.HashSet Name := dist.fold (init := {}) fun s n dn =>
      if dn ≤ depth || wanted.contains n then s.insert n else s
    let keptArr := kept.toArray.qsort (fun a b =>
      dist.getD a 0 < dist.getD b 0 || (dist.getD a 0 == dist.getD b 0 && a.toString < b.toString))
    let ids : Std.HashMap Name String := keptArr.zipIdx.foldl (init := {}) fun m (n, i) => m.insert n s!"t{i}"
    fig := {}
    for n in keptArr do
      let (s, r) := stage n
      let label := s!"{esc (shortName n)}<br/>{(moduleOf n).getD .anonymous}・{esc s}"
      let shape := if rs.contains n then s!"([\"{label}\"]):::root"
        else if theorems.contains n then s!"[\"{label}\"]:::{r.cls}"
        else s!"[/\"{label}\"/]:::{r.cls}"
      fig := fig.node s!"  {ids.getD n ""}{shape}"
    -- Edges between kept nodes through folded nodes.
    let mut premiseIds : Std.HashMap String String := {}
    let mut edgeLines : Array String := #[]
    for a in keptArr do
      let direct := graph.getD a #[]
      let mut seen : Std.HashSet Name := {}
      let mut found : Std.HashSet Target := {}
      let mut stack := direct.toList
      while !stack.isEmpty do
        match stack with
        | [] => pure ()
        | t :: rest =>
          stack := rest
          match t with
          | .premise _ => found := found.insert t
          | .node b =>
            if kept.contains b then found := found.insert t
            else if !seen.contains b then
              seen := seen.insert b
              stack := (graph.getD b #[]).toList ++ stack
      let foundArr := found.toArray.qsort fun x y => match x, y with
        | .node p, .node q => p.toString < q.toString
        | .node _, .premise _ => true
        | .premise _, .node _ => false
        | .premise p, .premise q => p < q
      for t in foundArr do
        let arrow := if direct.contains t then "-->" else "-.->"
        match t with
        | .node b =>
          if b != a then edgeLines := edgeLines.push s!"  {ids.getD a ""} {arrow} {ids.getD b ""}"
        | .premise p =>
          let pid ← match premiseIds[p]? with
            | some pid => pure pid
            | none =>
              let pid := s!"p{premiseIds.size}"
              premiseIds := premiseIds.insert p pid
              fig := fig.node s!"  {pid}\{\{\"{esc p}\"}}:::premise"
              pure pid
          edgeLines := edgeLines.push s!"  {ids.getD a ""} {if arrow == "-->" then "--o" else "-.-o"} {pid}"
    -- Hypotheses of the roots that are universally quantified propositions.
    for r in rs do
      for (h, used) in ← premiseArgs env r do
        let p := s!"{h}（{shortName r} の仮定）"
        let pid := s!"p{premiseIds.size}"
        premiseIds := premiseIds.insert p pid
        fig := fig.node s!"  {pid}\{\{\"{esc p}\"}}:::premise"
        edgeLines := edgeLines.push s!"  {ids.getD r ""} {if used then "--o" else "-.-o"} {pid}"
    for l in edgeLines do fig := fig.edge l
    let file := s!"invariant{k}.md"
    IO.FS.writeFile (System.FilePath.mk out / file) fig.text
    sizes := sizes.push s!"{file}: 節点 {fig.nodes}、辺 {fig.edges}、{fig.text.utf8ByteSize} バイト"
  for s in sizes do IO.println s
  for p in problems do IO.eprintln p
  return 0
