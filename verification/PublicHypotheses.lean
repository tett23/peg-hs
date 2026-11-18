import Lean
import PublicGenerationGHC
import PublicPremisesMeta
import CommittedModuleDerivations

/-!
ADR 0097: the hypotheses of the public theorems, read from their types, must
be those that public-hypotheses.allow permits.

The public theorems are the theorems named `invariant1_*`, `invariant2_*` or
`invariant3_*` declared in `publicModules`. For each, this program walks the
binders of its type and records as a hypothesis:
- a binder whose type is a proposition (`<theorem> <binder> : <type>`);
- a binder whose type is a function, an unmodelled function such as
  `ghcLex` (same form);
- every field of `Inputs` and `Premises` when a binder has one of these types
  (`Inputs.<field> : <type>`, `Premises.<field> : <type>`).
Other binders (the input text, the grammar, the module text) are the
universally quantified inputs of the theorem.

It also walks the definitions of the public entry functions (`entryFunctions`)
and the definitions and types they reach in the project, and records each
predicate of the project (a constant whose type ends in `Prop`) that a
definition depends on (`definition <function> -> <predicate>`): a public
entry defined through a judgement of a model (a search for a derivation)
rather than through the translated implementation.

Each recorded line must appear in public-hypotheses.allow, and each line of
the file must be recorded, with a reason that is a row of ADR 0097 or
`UNRESOLVED`. The number of `UNRESOLVED` lines is fixed by
`unresolvedLimit`.
-/

open Lean Meta Elab Command

def publicModules : List Name :=
  [`PublicGeneration, `PublicGenerationGHC, `CommittedModuleDerivations, `CertifiedPublicFiles]

def structured : List Name :=
  [``PegHs.PublicGeneration.Inputs, ``PegHs.PublicGeneration.Premises]

def entryFunctions : List Name :=
  [``PegHs.PublicGeneration.parse, ``PegHs.PublicGeneration.tops,
   ``PegHs.PublicGeneration.assembleTops, ``PegHs.PublicGeneration.lookupLibrary,
   ``PegHs.PublicGeneration.resolve, ``PegHs.PublicGeneration.checkStage,
   ``PegHs.PublicGeneration.inner, ``PegHs.PublicGeneration.generateWithWarnings,
   ``PegHs.PublicGeneration.publicModule, ``PegHs.PublicGeneration.generateFromSource]

-- The rows of ADR 0097 that permit a hypothesis: :33 the inputs (texts,
-- libraries, options), :38 the syntactic category of embedded code, :40 the
-- rules not checked against GHC's parser, :44 the assumptions of the
-- translator and of Haskell's evaluation, :56-:58 the antecedents of
-- invariants 1 to 3 themselves.
def reasons : List String :=
  ["ADR 0097:33", "ADR 0097:38", "ADR 0097:40", "ADR 0097:44", "ADR 0097:56", "ADR 0097:57",
   "ADR 0097:58", "UNRESOLVED"]

def unresolvedLimit : Nat := 55

def pp (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty 100000

def isPublicTheorem (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "invariant1_" || s.startsWith "invariant2_" || s.startsWith "invariant3_"
  | _ => false

def fieldLines (s : Name) : MetaM (List String) := do
  let env ← getEnv
  let short := s.componentsRev.head!.toString
  let some (.inductInfo ind) := env.find? s | throwError "not a structure {s}"
  (getStructureFields env s).toList.mapM fun f => do
    let some info := env.find? (s ++ f) | throwError "missing projection {s ++ f}"
    -- The parameters and the structure itself, not the arguments of the field.
    forallBoundedTelescope info.type (some (ind.numParams + 1)) fun _ body => do
      return s!"{short}.{f} : {← pp body}"

def theoremLines (n : Name) (type : Expr) : MetaM (List String × List Name) :=
  forallTelescope type fun xs _ => do
    let mut lines := []
    let mut structs := []
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let ty := decl.type
      match ty.getAppFn.constName? with
      | some c =>
        if structured.contains c then
          structs := c :: structs
          continue
      | none => pure ()
      if (← isProp ty) || (← whnf ty).isForall then
        lines := s!"{n} {decl.userName} : {← pp ty}" :: lines
    return (lines.reverse, structs)

def projectName (n : Name) : Bool :=
  (`PegHs).isPrefixOf n || (`Peg).isPrefixOf n

def safely (k : MetaM Bool) : MetaM Bool := try k catch _ => pure false

-- The constants that `e` computes with: proofs and the propositions that
-- binders assume (`(h : Sub known ...)`, a termination argument, also when
-- well-founded recursion packs it into `PSigma`) are skipped,
-- while a proposition that is computed with (the condition of `if h : ...`,
-- the property of a subtype) is kept.
partial def usedConstants (e : Expr) : StateRefT NameSet MetaM Unit := do
  if ← safely (isProof e) then return
  match e with
  | .const c _ => modify (·.insert c)
  | .app f a =>
    -- Well-founded recursion packs a hypothesis argument into `PSigma`.
    if e.getAppFn.constName?.any (fun c => c == ``PSigma || (`PSigma).isPrefixOf c) then
      -- Keep the data of the pack, not the predicate of its second component.
      for arg in e.getAppArgs do
        let predicate ← safely (lambdaTelescope arg fun xs b => return !xs.isEmpty && (← isProp b))
        unless predicate do usedConstants arg
      return
    usedConstants f; usedConstants a
  | .lam n d b bi | .forallE n d b bi =>
    unless ← safely (isProp d) do usedConstants d
    withLocalDecl n bi d fun x => usedConstants (b.instantiate1 x)
  | .letE n t v b _ =>
    usedConstants t; usedConstants v
    withLetDecl n t v fun x => usedConstants (b.instantiate1 x)
  | .mdata _ x => usedConstants x
  | .proj _ _ x => usedConstants x
  | _ => pure ()

-- The predicates of the project that the definition of `root` reaches.
partial def predicates (root : Name) : MetaM (List Name) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut todo := [root]
  let mut found := []
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some info := env.find? n | continue
    if n != root && projectName n then
      let isPred ← forallTelescope info.type fun _ body => return body.isProp
      if isPred && !info.isTheorem then found := n :: found
    -- A theorem is a proof inside a definition; what it proves is not part
    -- of what the definition computes.
    let exprs := match info with
      | .defnInfo d => [d.type, d.value]
      | .thmInfo _ => []
      | _ => [info.type]
    for e in exprs do
      let (_, used) ← (usedConstants e).run {}
      for c in used do
        if projectName c && !seen.contains c then todo := c :: todo
  return found.reverse

run_cmd liftTermElabM do
  let env ← getEnv
  let mut lines : Array String := #[]
  let mut structs : List Name := []
  let mut publicCount := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some m := env.header.moduleNames[idx.toNat]? | continue
    unless publicModules.contains m && info.isTheorem && isPublicTheorem name do continue
    publicCount := publicCount + 1
    let (ls, ss) ← theoremLines name info.type
    lines := lines ++ ls.toArray
    structs := structs ++ ss
  if publicCount == 0 then throwError "no public theorems"
  for s in structured do
    if structs.contains s then lines := lines ++ (← fieldLines s).toArray
  for f in entryFunctions do
    for p in ← predicates f do
      lines := lines.push s!"definition {f} -> {p}"
  let recorded := lines.toList.eraseDups
  let path := (← IO.getEnv "PUBLIC_HYPOTHESES_ALLOW").getD "public-hypotheses.allow"
  let text ← IO.FS.readFile path
  let mut allowed : List String := []
  let mut unresolved := 0
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let parts := line.splitOn "\t"
    let some reason := parts[1]? | throwError "no reason (tab-separated) for: {line}"
    unless reasons.any (reason.startsWith ·) do
      throwError "the reason is not a row of ADR 0097 or UNRESOLVED: {line}"
    if reason.startsWith "UNRESOLVED" then unresolved := unresolved + 1
    allowed := parts[0]! :: allowed
  let missing := recorded.filter (!allowed.contains ·)
  let stale := allowed.filter (!recorded.contains ·)
  for l in missing do logInfo m!"not allowed: {l}"
  for l in stale do logInfo m!"allowed but not recorded: {l}"
  unless missing.isEmpty && stale.isEmpty do
    throwError "the hypotheses of the public theorems differ from public-hypotheses.allow"
  unless unresolved == unresolvedLimit do
    throwError "{unresolved} UNRESOLVED hypotheses; the limit is {unresolvedLimit}"
  logInfo m!"{publicCount} public theorems, {recorded.length} hypotheses, {unresolved} unresolved"
