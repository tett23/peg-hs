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

-- The traversal of expressions, the instance bodies and the queue are modelled
-- with the caller of each instance and the scope of the bindings in
-- TemplateExpansionWhole.lean.

end PegHs.TemplateExpansion

#print axioms PegHs.TemplateExpansion.boundCaptureDiagnostic
#print axioms PegHs.TemplateExpansion.argumentType_invalid
#print axioms PegHs.TemplateExpansion.instanceOf_fresh_pending
