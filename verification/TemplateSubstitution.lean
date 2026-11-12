import Std
import Lean.Elab.Tactic.Omega

namespace PegHs.TemplateSubstitution

-- Item locations, bindings, Alt actions, and located value arguments are
-- projected away: substituteAlt changes only itemExpr in these records.
inductive Expr where
  | lit (value written : String)
  | charClass (written : String)
  | any
  | ref (location : Nat) (name : String) (args : List String)
  | group (alts : List (List Expr))
  | star (child : Expr)
  | plus (child : Expr)
  | opt (child : Expr)
  | and (child : Expr)
  | not (child : Expr)
  | capture (child : Expr)
  | label (location : Nat) (child : Expr) (name : String)
  | predicate (polarity : Bool) (code : String)
  | template (location : Nat) (name : String) (args : List Expr) (vals : List String)
  | discard (child : Expr)
  deriving Repr

-- The Bool records whether the template parameter has a value type.
abbrev Substitution := String → Option (Bool × Expr)

-- `passed = true` is the special ETemplate-argument context. An injected
-- argument is returned directly, not recursively traversed in this pass.
def substitute (sub : Substitution) (passed : Bool) : Expr → Expr
  | .ref location name [] =>
    match sub name with
    | some (typed, arg) =>
      if passed || typed then arg else .discard arg
    | none => .ref location name []
  | .group alts => .group (alts.map fun items => items.map (substitute sub false))
  | .star x => .star (substitute sub false x)
  | .plus x => .plus (substitute sub false x)
  | .opt x => .opt (substitute sub false x)
  | .and x => .and (substitute sub false x)
  | .not x => .not (substitute sub false x)
  | .capture x => .capture (substitute sub false x)
  | .label location x name => .label location (substitute sub false x) name
  | .discard x => .discard (substitute sub false x)
  | .template location name args vals =>
    .template location name (args.map (substitute sub true)) vals
  | e => e
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega
  · apply Nat.lt_trans (List.sizeOf_lt_of_mem (by assumption))
    omega

def substituteAlt (sub : Substitution) (items : List Expr) : List Expr :=
  items.map (substitute sub false)

theorem expandedArguments_length (expandChild : Expr → Expr) (args : List Expr) :
    (args.map expandChild).length = args.length := by simp

theorem substituteAlt_length (sub : Substitution) (items : List Expr) :
    (substituteAlt sub items).length = items.length := by
  simp [substituteAlt]

theorem typed_reference (sub : Substitution) (location : Nat) (name : String)
    (arg : Expr) (h : sub name = some (true, arg)) :
    substitute sub false (.ref location name []) = arg := by
  simp [substitute, h]

theorem untyped_reference (sub : Substitution) (location : Nat) (name : String)
    (arg : Expr) (h : sub name = some (false, arg)) :
    substitute sub false (.ref location name []) = .discard arg := by
  simp [substitute, h]

theorem passed_reference (sub : Substitution) (location : Nat) (name : String)
    (typed : Bool) (arg : Expr) (h : sub name = some (typed, arg)) :
    substitute sub true (.ref location name []) = arg := by
  simp [substitute, h]

abbrev Diagnostic := Nat × String

-- These are the direct diagnostics of expandExpr's ETemplate branch. Child
-- expansion, captures, argType, and instanceOf may append further errors.
def valueErrors (location : Nat) (name : String) (valueParams : Nat)
    (vals : List String) : List Diagnostic :=
  if valueParams == 0 && !vals.isEmpty then
    [(location, "the template " ++ name ++ " takes no value arguments")]
  else if vals.length != valueParams then
    [(location, "the template " ++ name ++ " expects " ++ toString valueParams ++
      " value argument(s), but got " ++ toString vals.length)]
  else []

def callErrors (hasTemplate : Bool) (location : Nat) (name : String)
    (valueParams templateParams : Nat) (args : List Expr)
    (vals : List String) : List Diagnostic :=
  if !hasTemplate then [(location, "rule " ++ name ++ " is not a template")]
  else valueErrors location name valueParams vals ++
    if args.length != templateParams then
      [(location, "the template " ++ name ++ " expects " ++ toString templateParams ++
        " argument(s), but got " ++ toString args.length)]
    else []

def bareReferenceErrors (templateName : Bool) (location : Nat) (name : String) :
    List Diagnostic :=
  if templateName then
    [(location, "the template " ++ name ++ " needs arguments: " ++ name ++ "<...>")]
  else []

theorem unknownTemplate (location : Nat) (name : String)
    (valueParams templateParams : Nat) (args : List Expr) (vals : List String) :
    callErrors false location name valueParams templateParams args vals =
      [(location, "rule " ++ name ++ " is not a template")] := by
  simp [callErrors]

theorem noValueParameters (location : Nat) (name : String)
    (templateParams : Nat) (args : List Expr) (vals : List String)
    (nonempty : vals ≠ []) :
    (location, "the template " ++ name ++ " takes no value arguments") ∈
      callErrors true location name 0 templateParams args vals := by
  simp [callErrors, valueErrors, nonempty]

theorem wrongValueCount (location : Nat) (name : String)
    (valueParams templateParams : Nat) (args : List Expr) (vals : List String)
    (positive : 0 < valueParams) (wrong : vals.length ≠ valueParams) :
    (location, "the template " ++ name ++ " expects " ++ toString valueParams ++
      " value argument(s), but got " ++ toString vals.length) ∈
      callErrors true location name valueParams templateParams args vals := by
  have nonzero : valueParams ≠ 0 := by omega
  simp [callErrors, valueErrors, nonzero, wrong]

theorem wrongTemplateArity (location : Nat) (name : String)
    (valueParams templateParams : Nat) (args : List Expr) (vals : List String)
    (wrong : args.length ≠ templateParams) :
    (location, "the template " ++ name ++ " expects " ++ toString templateParams ++
      " argument(s), but got " ++ toString args.length) ∈
      callErrors true location name valueParams templateParams args vals := by
  simp [callErrors, wrong]

theorem bareReferenceNeedsArguments (location : Nat) (name : String) :
    bareReferenceErrors true location name =
      [(location, "the template " ++ name ++ " needs arguments: " ++ name ++ "<...>")] := by
  simp [bareReferenceErrors]

theorem callFailureVisible (errors rest : List Diagnostic)
    (nonempty : errors ≠ []) : errors ++ rest ≠ [] := by
  cases errors with
  | nil => contradiction
  | cons _ _ => simp

def finishErrors (errs : List Diagnostic) : List Diagnostic :=
  errs.reverse.eraseDups

theorem finishErrors_nonempty (errs : List Diagnostic) (nonempty : errs ≠ []) :
    finishErrors errs ≠ [] := by
  cases errs with
  | nil => contradiction
  | cons d ds =>
    have member : d ∈ finishErrors (d :: ds) := by
      apply List.mem_eraseDups.mpr
      simp
    intro empty
    simp [empty] at member

theorem directCallDiagnosticVisible (errors prior : List Diagnostic)
    (nonempty : errors ≠ []) :
    finishErrors (errors.reverse ++ prior) ≠ [] := by
  apply finishErrors_nonempty
  cases errors with
  | nil => contradiction
  | cons d ds => simp

theorem callDiagnosticVisible (hasTemplate : Bool) (location : Nat) (name : String)
    (valueParams templateParams : Nat) (args : List Expr) (vals : List String)
    (prior : List Diagnostic) (diagnostic : Diagnostic)
    (member : diagnostic ∈ callErrors hasTemplate location name valueParams
      templateParams args vals) :
    finishErrors ((callErrors hasTemplate location name valueParams templateParams args vals).reverse ++
      prior) ≠ [] := by
  apply directCallDiagnosticVisible
  intro empty
  simp [empty] at member

-- Invariant 2 tests are placed before the translator is implemented.
example : substitute (fun _ => none) false (.star .any) = .star .any := by
  simp [substitute]
example : substitute (fun n => if n == "x" then some (false, .lit "a" "'a'") else none)
    false (.ref 1 "x" []) = .discard (.lit "a" "'a'") := by
  simp [substitute]
example : substitute (fun n => if n == "x" then some (false, .lit "a" "'a'") else none)
    true (.ref 1 "x" []) = .lit "a" "'a'" := by
  simp [substitute]
example : substitute (fun n => if n == "x" then some (false, .lit "a" "'a'") else none)
    false (.template 1 "T" [.ref 1 "x" []] []) =
      .template 1 "T" [.lit "a" "'a'"] [] := by
  simp [substitute]
example : callErrors false 1 "X" 0 0 [] [] =
    [(1, "rule X is not a template")] := by decide
example : callErrors true 1 "X" 0 0 [] ["v"] =
    [(1, "the template X takes no value arguments")] := by decide
example : callErrors true 1 "X" 1 0 [] [] =
    [(1, "the template X expects 1 value argument(s), but got 0")] := by decide
example : callErrors true 1 "X" 0 1 [] [] =
    [(1, "the template X expects 1 argument(s), but got 0")] := by decide
example : callErrors true 1 "X" 0 1 [] ["v"] =
    [(1, "the template X takes no value arguments"),
     (1, "the template X expects 1 argument(s), but got 0")] := by decide

end PegHs.TemplateSubstitution

#print axioms PegHs.TemplateSubstitution.substituteAlt_length
#print axioms PegHs.TemplateSubstitution.typed_reference
#print axioms PegHs.TemplateSubstitution.wrongTemplateArity
#print axioms PegHs.TemplateSubstitution.directCallDiagnosticVisible
