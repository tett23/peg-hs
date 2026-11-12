import EnvironmentEval
import ExpressionDepth

namespace PegHs.EnvironmentDepth
open PegHs.EnvironmentEval
open PegHs.ExpressionDepth

abbrev CallSite := String × String × List String

inductive DepthArg where
  | zero
  | current
  | successor
  | plusValue (name : String)
  deriving DecidableEq, Repr

def depthArgOf : String → Option DepthArg
  | "0" => some .zero
  | "d" => some .current
  | "d + 1" => some .successor
  | "d + snd e" => some (.plusValue "e")
  | "d + snd p" => some (.plusValue "p")
  | _ => none

def supportedCallArgs (site : CallSite) : Bool :=
  match site.2.2 with
  | [] => true
  | [source] => (depthArgOf source).isSome
  | _ => false

def evalDepthArg (env : Env) : DepthArg → Option Nat
  | .zero => some 0
  | .current => some env.depth
  | .successor => some (env.depth + 1)
  | .plusValue name => (env.valueDepth name).map (env.depth + ·)

-- A reference without value arguments keeps the caller depth. The only
-- argument forms present in the two metagrammars are listed above.
def enterCall (sites : Nat → Option CallSite) (site : Nat) (env : Env) : Option Env := do
  let (_, _, args) ← sites site
  match args with
  | [] => some env
  | [source] => do
      let arg ← depthArgOf source
      let depth ← evalDepthArg env arg
      some { depth := depth }
  | _ => none

-- A successful bound rule can publish the structural height of its returned
-- expression. The caller supplies its parsed shape; unknown shapes remain
-- absent, so d + snd e/p fails closed rather than inventing a depth.
def bindShape (shapeAt : Nat → String → List Char → Option Shape)
    (site : Nat) (name : String) (text : List Char) (env : Env) : Option Env :=
  let captured := (env.put name text).putDepth name env.resultDepth
  match shapeAt site name text with
  | some shape => if height shape = env.resultDepth then some captured else none
  | none => some captured

def hooks (sites : Nat → Option CallSite)
    (shapeAt : Nat → String → List Char → Option Shape) : Hooks where
  bindValue := bindShape shapeAt
  enterCall := enterCall sites
  leaveCall := fun _ caller callee => { caller with resultDepth := callee.resultDepth }

theorem invariant1_argument_from_shape (env : Env) (name : String) (shape : Shape) :
    evalDepthArg (env.putDepth name (height shape)) (.plusValue name) =
      some (env.depth + height shape) := by
  simp [evalDepthArg, Env.putDepth, Env.valueDepth]

theorem invariant1_missing_shape_rejected (env : Env) (name : String)
    (absent : env.valueDepth name = none) :
    evalDepthArg env (.plusValue name) = none := by
  simp [evalDepthArg, absent]

theorem invariant1_action_enter (env : Env) (name : String) (shape : Shape)
    (bound : env.valueDepth name = some (height shape)) :
    DepthAction.eval env (.successor name) = some (height (.enter shape)) := by
  simp [DepthAction.eval, bound, height]

theorem invariant1_action_postfix (env : Env) (primary ops : String)
    (shape : Shape) (count : Nat)
    (hp : env.valueDepth primary = some (height shape))
    (ho : env.valueDepth ops = some count) :
    DepthAction.eval env (.add primary ops) =
      some (height (.postOps shape count)) := by
  simp [DepthAction.eval, hp, ho, height]

theorem invariant1_action_children (env : Env) (left right : String)
    (a b : Shape)
    (ha : env.valueDepth left = some (height a))
    (hb : env.valueDepth right = some (height b)) :
    DepthAction.eval env (.maximum left right) =
      some (height (.children a b)) := by
  simp [DepthAction.eval, ha, hb, height]

theorem invariant1_action_optional_label (env : Env) (value presence : String)
    (shape : Shape) (hv : env.valueDepth value = some (height shape)) :
    DepthAction.eval env (.plusIfBound value presence) =
      some (if env.captures.any (fun pair => pair.1 == presence)
        then height (.enter shape) else height shape) := by
  cases h : env.captures.any (fun pair => pair.1 == presence) <;>
    simp [DepthAction.eval, hv, height, h]

example : depthArgOf "d + snd e" = some (.plusValue "e") := by decide
example : enterCall (fun _ => some ("Labeled", "LabelPart", ["d + snd e"]))
    0 ({ depth := 3 } : Env) = none := by rfl
example : enterCall (fun _ => some ("Labeled", "LabelPart", ["d + snd e"]))
    0 ({ depth := 3, valueDepths := [("e", 2)] } : Env) =
      some ({ depth := 5 } : Env) := by rfl

#print axioms invariant1_argument_from_shape
#print axioms invariant1_missing_shape_rejected
#print axioms invariant1_action_enter
#print axioms invariant1_action_postfix
#print axioms invariant1_action_children
#print axioms invariant1_action_optional_label

end PegHs.EnvironmentDepth
