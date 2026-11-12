import TemplateSubstitution
import TemplateQueue

namespace PegHs.TemplateExpansion

open TemplateSubstitution

structure Template where
  name : String
  valueParams : Nat
  params : List (String × Bool)
  body : List (List Expr)

structure Job where
  name : String
  template : Template
  args : List Expr
  captured : List (String × String)
  depth : Nat
  location : Nat

structure Context where
  templates : String → Option Template
  callerName : String
  callerParams : String → Option String
  orderedNames : List Expr → List String
  reserved : String → Bool
  bodyUses : String → String → Bool
  ruleTypes : String → Option String
  key : Template → List Expr → List (String × String) → String
  freshName : String → Nat → List String → String
  instanceType : Template → List (Option String) → String

structure State where
  errors : List Diagnostic := []
  pending : List Job := []
  instances : String → Option String := fun _ => none
  count : Nat := 0
  generated : List String := []
  instanceTypes : String → Option String := fun _ => none

def addErrors (ds : List Diagnostic) : StateM State Unit :=
  modify fun st => { st with errors := ds.reverse ++ st.errors }

def captureDetails (ctx : Context) (scope : List String) (location : Nat) (template : Template)
    (args : List Expr) : List (String × String) × List Diagnostic :=
  let names := ctx.orderedNames args
  let bound := names.filter (fun x => decide (x ∈ scope))
  let taken := names.filterMap fun x =>
    if ctx.reserved x || decide (x ∈ scope) then none
    else (ctx.callerParams x).map (fun ty => (x, ty))
  let boundErrors := bound.map fun x =>
    (location, "the argument of the template " ++ template.name ++
      " uses the binding " ++ x ++ ", which a template cannot take; pass it as a value argument")
  let captureErrors := (taken.filter (fun pair => ctx.bodyUses template.name pair.1)).map fun pair =>
    (location, "the template " ++ template.name ++ " uses the name " ++ pair.1 ++
      " in its body, so its argument cannot take the parameter " ++ pair.1 ++
      " of the rule " ++ ctx.callerName ++ "; rename the parameter")
  (taken, boundErrors ++ captureErrors)

theorem boundCaptureDiagnostic (ctx : Context) (scope : List String)
    (location : Nat) (template : Template) (args : List Expr) (name : String)
    (listed : name ∈ ctx.orderedNames args) (bound : name ∈ scope) :
    (location, "the argument of the template " ++ template.name ++
      " uses the binding " ++ name ++
      ", which a template cannot take; pass it as a value argument") ∈
      (captureDetails ctx scope location template args).2 := by
  unfold captureDetails
  simp only [List.mem_append]
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨name, ?_, rfl⟩
  simp [listed, bound]

def argumentType (ctx : Context) (st : State) (location : Nat)
    (param : String × Bool) (arg : Expr) : Option String × List Diagnostic :=
  if !param.2 then (none, [])
  else match arg with
    | .ref _ name _ =>
      (some ((st.instanceTypes name).getD ((ctx.ruleTypes name).getD "()")), [])
    | .capture _ => (some "PegRt.Text", [])
    | _ => (some "()", [(location, "the argument for " ++ param.1 ++
        " must be a rule, a capture or a template call, since its value is used")])

theorem argumentType_untyped (ctx : Context) (st : State) (location : Nat)
    (name : String) (arg : Expr) :
    argumentType ctx st location (name, false) arg = (none, []) := by
  simp [argumentType]

theorem argumentType_invalid (ctx : Context) (st : State) (location : Nat)
    (name value written : String) :
    argumentType ctx st location (name, true) (.lit value written) =
      (some "()", [(location, "the argument for " ++ name ++
        " must be a rule, a capture or a template call, since its value is used")]) := by
  simp [argumentType]

def instanceOf (ctx : Context) (location depth : Nat) (template : Template)
    (args : List Expr) (captured : List (String × String))
    (types : List (Option String)) (st : State) : String × State :=
  let key := ctx.key template args captured
  match st.instances key with
  | some name => (name, st)
  | none =>
    let name := ctx.freshName template.name st.count st.generated
    (name, { st with
      instances := fun queried => if queried == key then some name else st.instances queried
      pending := st.pending ++ [Job.mk name template args captured (depth + 1) location]
      count := st.count + 1
      generated := name :: st.generated
      instanceTypes := fun queried =>
        if queried == name then some (ctx.instanceType template types)
        else st.instanceTypes queried })

theorem instanceOf_existing_pending (ctx : Context) (location depth : Nat)
    (template : Template) (args : List Expr) (captured : List (String × String))
    (types : List (Option String)) (st : State) (name : String)
    (existing : st.instances (ctx.key template args captured) = some name) :
    (instanceOf ctx location depth template args captured types st).2.pending = st.pending := by
  simp [instanceOf, existing]

theorem instanceOf_fresh_pending (ctx : Context) (location depth : Nat)
    (template : Template) (args : List Expr) (captured : List (String × String))
    (types : List (Option String)) (st : State)
    (fresh : st.instances (ctx.key template args captured) = none) :
    (instanceOf ctx location depth template args captured types st).2.pending =
      st.pending ++ [Job.mk (ctx.freshName template.name st.count st.generated) template args captured
        (depth + 1) location] := by
  simp [instanceOf, fresh]

theorem instanceOf_fresh_count (ctx : Context) (location depth : Nat)
    (template : Template) (args : List Expr) (captured : List (String × String))
    (types : List (Option String)) (st : State)
    (fresh : st.instances (ctx.key template args captured) = none) :
    (instanceOf ctx location depth template args captured types st).2.count = st.count + 1 := by
  simp [instanceOf, fresh]

theorem instanceOf_fresh_generated (ctx : Context) (location depth : Nat)
    (template : Template) (args : List Expr) (captured : List (String × String))
    (types : List (Option String)) (st : State)
    (fresh : st.instances (ctx.key template args captured) = none) :
    (instanceOf ctx location depth template args captured types st).2.generated =
      ctx.freshName template.name st.count st.generated :: st.generated := by
  simp [instanceOf, fresh]

-- `expandExpr` itself follows only strict subexpressions. Calling instanceOf
-- can append a job, but that job is processed later by TemplateQueue.drain.
def expandExpr (ctx : Context) (depth : Nat) (scope : List String) :
    Expr → StateM State Expr
  | .ref location name args => do
    if (ctx.templates name).isSome then
      addErrors [(location, "the template " ++ name ++ " needs arguments: " ++ name ++ "<...>")]
    pure (.ref location name args)
  | .template location name args vals => do
    match ctx.templates name with
    | none =>
      addErrors [(location, "rule " ++ name ++ " is not a template")]
      pure (.ref location name [])
    | some template =>
      addErrors (valueErrors location name template.valueParams vals)
      let args' ← args.mapM (expandExpr ctx depth scope)
      if args'.length != template.params.length then
        addErrors [(location, "the template " ++ name ++ " expects " ++
          toString template.params.length ++ " argument(s), but got " ++ toString args'.length)]
        pure (.ref location name [])
      else
        let (captured, captureErrors) := captureDetails ctx scope location template args'
        addErrors captureErrors
        let st ← get
        let typeResults := (List.zip template.params args').map fun (param, arg) =>
          argumentType ctx st location param arg
        addErrors (typeResults.flatMap Prod.snd)
        let st' ← get
        let (instanceName, next) := instanceOf ctx location depth template args' captured
          (typeResults.map Prod.fst) st'
        set next
        pure (.ref location instanceName (vals ++ captured.map Prod.fst))
  | .group alts => do
    let alts' ← alts.mapM (fun items => items.mapM (expandExpr ctx depth scope))
    pure (.group alts')
  | .star x => return .star (← expandExpr ctx depth scope x)
  | .plus x => return .plus (← expandExpr ctx depth scope x)
  | .opt x => return .opt (← expandExpr ctx depth scope x)
  | .and x => return .and (← expandExpr ctx depth scope x)
  | .not x => return .not (← expandExpr ctx depth scope x)
  | .capture x => return .capture (← expandExpr ctx depth scope x)
  | .label location x name => return .label location (← expandExpr ctx depth scope x) name
  | .discard x => return .discard (← expandExpr ctx depth scope x)
  | e => pure e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega

def exprSize : Expr → Nat
  | .group alts => 1 + (alts.map fun items => (items.map exprSize).sum).sum
  | .star x | .plus x | .opt x | .and x | .not x | .capture x | .discard x =>
    1 + exprSize x
  | .label _ x _ => 1 + exprSize x
  | .template _ _ args _ => 1 + (args.map exprSize).sum
  | _ => 1
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega

def substitutionFor (template : Template) (args : List Expr) : Substitution :=
  (List.zip template.params args).foldl
    (fun lookup pair queried =>
      if queried == pair.1.1 then some (pair.1.2, pair.2) else lookup queried)
    (fun _ => none)

-- Only drain reads the existing pending queue. The body starts with a local
-- empty child queue, then its finite new suffix is appended to the old queue.
def expandBody (ctx : Context) (job : Job) (st : State) : State × List Job :=
  let sub := substitutionFor job.template job.args
  let action : StateM State (List (List Expr)) :=
    job.template.body.mapM fun items =>
      (substituteAlt sub items).mapM (expandExpr ctx job.depth [])
  let startState := { st with pending := [] }
  let (_, after) := action.run startState
  let children := after.pending
  ({ after with pending := st.pending ++ children }, children)

theorem expandBody_pending_prefix (ctx : Context) (job : Job) (st : State) :
    (expandBody ctx job st).1.pending = st.pending ++ (expandBody ctx job st).2 := by
  let sub := substitutionFor job.template job.args
  let action : StateM State (List (List Expr)) :=
    job.template.body.mapM fun items =>
      (substituteAlt sub items).mapM (expandExpr ctx job.depth [])
  let startState := { st with pending := [] }
  cases h : action.run startState with
  | mk result after => simp [expandBody, sub, action, startState, h]

def worker (ctx : Context) : TemplateQueue.Worker Job State where
  size := fun job => (job.args.map exprSize).sum
  expand := fun _ job st => expandBody ctx job st
  reject := fun job st =>
    { st with errors :=
      (job.location, "the expansion of the template " ++ job.template.name ++
        " does not end: templates call templates more than 64 levels deep") :: st.errors }

theorem expansionQueueTerminates (ctx : Context) (jobs : List Job) (st : State)
    (depth : Nat) :
    ∃ final, TemplateQueue.Drains (worker ctx) st
      (TemplateQueue.tag depth jobs) final := by
  exact TemplateQueue.invariant2_drain_terminates (worker ctx) jobs st depth

theorem rejectedJobHasDiagnostic (ctx : Context) (job : Job) (st : State)
    (depth : Nat) (past : 64 < depth) :
    ((TemplateQueue.visit (worker ctx) depth job st).1).errors =
      (job.location, "the expansion of the template " ++ job.template.name ++
        " does not end: templates call templates more than 64 levels deep") :: st.errors ∧
    (TemplateQueue.visit (worker ctx) depth job st).2 = [] := by
  simp [TemplateQueue.visit, TemplateQueue.allowed, worker, Nat.not_le_of_lt past]

theorem oversizedJobHasDiagnostic (ctx : Context) (job : Job) (st : State)
    (depth : Nat) (large : 10000 < (job.args.map exprSize).sum) :
    ((TemplateQueue.visit (worker ctx) depth job st).1).errors =
      (job.location, "the expansion of the template " ++ job.template.name ++
        " does not end: templates call templates more than 64 levels deep") :: st.errors ∧
    (TemplateQueue.visit (worker ctx) depth job st).2 = [] := by
  simp [TemplateQueue.visit, TemplateQueue.allowed, worker, Nat.not_le_of_lt large]

-- Invariant 2 boundaries precede the expansion implementation.
example (ctx : Context) (st : State) :
    ((expandExpr ctx 0 [] (.lit "a" "'a'")).run st).1 = .lit "a" "'a'" := by
  simp [expandExpr]
  rfl

example : exprSize (.template 1 "T" [.star (.lit "a" "'a'")] []) = 3 := by
  simp [exprSize]

end PegHs.TemplateExpansion

#print axioms PegHs.TemplateExpansion.boundCaptureDiagnostic
#print axioms PegHs.TemplateExpansion.argumentType_invalid
#print axioms PegHs.TemplateExpansion.instanceOf_fresh_pending
#print axioms PegHs.TemplateExpansion.expansionQueueTerminates
#print axioms PegHs.TemplateExpansion.rejectedJobHasDiagnostic
