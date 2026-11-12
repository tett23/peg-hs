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
      some { env with depth }
  | _ => none

-- A successful bound rule can publish the structural height of its returned
-- expression. The caller supplies its parsed shape; unknown shapes remain
-- absent, so d + snd e/p fails closed rather than inventing a depth.
def bindShape (shapeAt : Nat → String → List Char → Option Shape)
    (site : Nat) (name : String) (text : List Char) (env : Env) : Option Env :=
  let captured := env.put name text
  some <| match shapeAt site name text with
    | some shape => captured.putDepth name (height shape)
    | none => captured

def hooks (sites : Nat → Option CallSite)
    (shapeAt : Nat → String → List Char → Option Shape) : Hooks where
  bindValue := bindShape shapeAt
  enterCall := enterCall sites
  leaveCall := fun _ caller _ => caller

theorem invariant1_argument_from_shape (env : Env) (name : String) (shape : Shape) :
    evalDepthArg (env.putDepth name (height shape)) (.plusValue name) =
      some (env.depth + height shape) := by
  simp [evalDepthArg, Env.putDepth, Env.valueDepth]

theorem invariant1_missing_shape_rejected (env : Env) (name : String)
    (absent : env.valueDepth name = none) :
    evalDepthArg env (.plusValue name) = none := by
  simp [evalDepthArg, absent]

example : depthArgOf "d + snd e" = some (.plusValue "e") := by decide
example : enterCall (fun _ => some ("Labeled", "LabelPart", ["d + snd e"]))
    0 ({ depth := 3 } : Env) = none := by rfl
example : enterCall (fun _ => some ("Labeled", "LabelPart", ["d + snd e"]))
    0 ({ depth := 3, valueDepths := [("e", 2)] } : Env) =
      some ({ depth := 5, valueDepths := [("e", 2)] } : Env) := by rfl

#print axioms invariant1_argument_from_shape
#print axioms invariant1_missing_shape_rejected

end PegHs.EnvironmentDepth
