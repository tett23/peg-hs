import SemanticPredicates
import ConcreteTerminal
import CallOrder

namespace PegHs.EnvironmentEval

open PegHs.ConcreteTerminal
open PegHs.SemanticPredicates

structure Env where
  captures : List (String × List Char) := []
  depth : Nat := 0
  valueDepths : List (String × Nat) := []
  deriving Repr, DecidableEq, Inhabited

def Env.lookup (env : Env) (name : String) : List Char :=
  ((env.captures.find? fun pair => pair.1 == name).map Prod.snd).getD []

def Env.put (env : Env) (name : String) (captured : List Char) : Env :=
  { env with captures := (name, captured) :: env.captures }

def Env.valueDepth (env : Env) (name : String) : Option Nat :=
  (env.valueDepths.find? fun pair => pair.1 == name).map Prod.snd

def Env.putDepth (env : Env) (name : String) (depth : Nat) : Env :=
  { env with valueDepths := (name, depth) :: env.valueDepths }

inductive Body where
  | eps
  | terminal (site : Nat)
  | predicate (site : Nat)
  | call (site rule : Nat)
  | seq (a b : Body)
  | alt (a b : Body)
  | ahead (a : Body)
  | notAhead (a : Body)
  | star (a : Body)
  | label (name : String) (message : Option String) (a : Body)
  | capture (a : Body)
  | bind (site : Nat) (name : String) (a : Body)
  deriving Repr, DecidableEq

def erase : Body → PegHs.CallOrder.Body
  | .eps | .predicate _ => .eps
  | .terminal _ => .token
  | .call _ rule => .call rule
  | .seq a b => .seq (erase a) (erase b)
  | .alt a b => .alt (erase a) (erase b)
  | .ahead a | .notAhead a => .look (erase a)
  | .star a => .star (erase a)
  | .label _ _ a | .capture a | .bind _ _ a => erase a

def sitesInBounds (termCount predCount callCount bindCount ruleCount : Nat) : Body → Bool
  | .eps => true
  | .terminal site => site < termCount
  | .predicate site => site < predCount
  | .call site rule => site < callCount && rule < ruleCount
  | .seq a b | .alt a b =>
      sitesInBounds termCount predCount callCount bindCount ruleCount a &&
        sitesInBounds termCount predCount callCount bindCount ruleCount b
  | .ahead a | .notAhead a | .star a | .capture a | .label _ _ a =>
      sitesInBounds termCount predCount callCount bindCount ruleCount a
  | .bind site _ a => site < bindCount &&
      sitesInBounds termCount predCount callCount bindCount ruleCount a

inductive Reply where
  | ok (remaining : Nat) (env : Env)
  | fail
  | throwLabel (remaining : Nat) (name : String) (message : Option String)
  deriving Repr, DecidableEq

structure Hooks where
  -- A binding can denote captured text or a rule's semantic value. The
  -- extracted site source is retained so callers can supply exact behavior.
  bindValue : Nat → String → List Char → Env → Option Env
  enterCall : Nat → Env → Option Env
  leaveCall : Nat → Env → Env → Env

def defaultHooks : Hooks where
  bindValue := fun _ name text env => some (env.put name text)
  enterCall := fun _ env => some env
  leaveCall := fun _ caller _ => caller

structure Inputs where
  rules : Nat → Body
  terms : Nat → Option Terminal
  sites : Nat → Option (Kind × Bool)
  classes : Classes
  predicateEnv : Nat → Env → SemanticPredicates.Env
  hooks : Hooks
  input : List Char

private def matchedText (input : List Char) (start rest : Nat) : List Char :=
  (input.drop (input.length - start)).take (start - rest)

-- A failed choice retries with the original env. Lookahead also restores it.
def runFuel (ctx : Inputs) : Nat → Body → Nat → Env → Option Reply
  | 0, _, _, _ => none
  | fuel + 1, body, remaining, env =>
      match body with
      | .eps => some (.ok remaining env)
      | .terminal site =>
          match ctx.terms site with
          | none => some .fail
          | some term =>
              match terminalOracle term ctx.input remaining with
              | none => some .fail
              | some rest => if rest < remaining then some (.ok rest env) else some .fail
      | .predicate site =>
          match ctx.sites site with
          | none => some .fail
          | some (kind, polarity) =>
              if eval ctx.classes kind (ctx.predicateEnv site env) == polarity
              then some (.ok remaining env) else some .fail
      | .call site rule =>
          match ctx.hooks.enterCall site env with
          | none => some .fail
          | some callee =>
              match runFuel ctx fuel (ctx.rules rule) remaining callee with
              | some (.ok rest inner) => some (.ok rest (ctx.hooks.leaveCall site env inner))
              | some .fail => some .fail
              | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
              | none => none
      | .seq a b =>
          match runFuel ctx fuel a remaining env with
          | some (.ok rest next) => runFuel ctx fuel b rest next
          | some .fail => some .fail
          | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
          | none => none
      | .alt a b =>
          match runFuel ctx fuel a remaining env with
          | some .fail => runFuel ctx fuel b remaining env
          | other => other
      | .ahead a =>
          match runFuel ctx fuel a remaining env with
          | some (.ok _ _) => some (.ok remaining env)
          | some _ => some .fail
          | none => none
      | .notAhead a =>
          match runFuel ctx fuel a remaining env with
          | some (.ok _ _) => some .fail
          | some _ => some (.ok remaining env)
          | none => none
      | .star a =>
          match runFuel ctx fuel a remaining env with
          | some .fail => some (.ok remaining env)
          | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
          | some (.ok rest next) =>
              if rest < remaining then runFuel ctx fuel (.star a) rest next
              else some (.ok remaining env)
          | none => none
      | .label name msg a =>
          match runFuel ctx fuel a remaining env with
          | some .fail => some (.throwLabel remaining name msg)
          | other => other
      | .capture a => runFuel ctx fuel a remaining env
      | .bind site name a =>
          match runFuel ctx fuel a remaining env with
          | some (.ok rest inner) =>
              match ctx.hooks.bindValue site name
                  (matchedText ctx.input remaining rest) inner with
              | some bound => some (.ok rest bound)
              | none => some .fail
          | other => other

private def exampleClasses : Classes where
  space := fun c => c == ' '
  alpha := fun _ => false
  alnum := fun _ => false

private def exampleHooks : Hooks where
  bindValue := fun _ name _ env => some (env.put name ['x'])
  enterCall := fun _ env => some { env with depth := env.depth + 1 }
  leaveCall := fun _ caller _ => caller

private def exampleInputs : Inputs where
  rules := fun _ => .predicate 1
  terms := fun _ => none
  sites := fun site => if site == 0 then some (.space, true) else some (.depth, true)
  classes := exampleClasses
  predicateEnv := fun site env =>
    { captured := if site == 0 then env.lookup "c" else [], depth := env.depth }
  hooks := exampleHooks
  input := []

-- The right branch sees the original capture after the left branch fails.
private def before : Env := { captures := [("c", [' '])] }
example : runFuel exampleInputs 5
    (.alt (.seq (.bind 0 "c" .eps) (.terminal 0)) (.predicate 0))
    0 before = some (.ok 0 before) := by rfl

-- The same input position can yield different predicate results by env.
example : runFuel exampleInputs 2 (.predicate 0) 0 before =
    some (.ok 0 before) := by rfl
example : runFuel exampleInputs 2 (.predicate 0) 0 (before.put "c" ['x']) =
    some .fail := by rfl

-- A rule argument changes depth only inside the callee.
example : runFuel exampleInputs 3 (.call 0 0) 0 { depth := 254 } =
    some (.ok 0 { depth := 254 }) := by rfl
example : runFuel exampleInputs 3 (.call 0 0) 0 { depth := 255 } =
    some .fail := by rfl

theorem invariant1_choice_rewinds (ctx : Inputs) (fuel n : Nat) (env : Env)
    (a b : Body) (failed : runFuel ctx fuel a n env = some .fail) :
    runFuel ctx (fuel + 1) (.alt a b) n env = runFuel ctx fuel b n env := by
  simp [runFuel, failed]

theorem invariant1_ahead_restores (ctx : Inputs) (fuel n rest : Nat)
    (env next : Env) (a : Body)
    (accepted : runFuel ctx fuel a n env = some (.ok rest next)) :
    runFuel ctx (fuel + 1) (.ahead a) n env = some (.ok n env) := by
  simp [runFuel, accepted]

theorem invariant1_notAhead_restores (ctx : Inputs) (fuel n pos : Nat)
    (env : Env) (a : Body) (name : String) (msg : Option String)
    (thrown : runFuel ctx fuel a n env = some (.throwLabel pos name msg)) :
    runFuel ctx (fuel + 1) (.notAhead a) n env = some (.ok n env) := by
  simp [runFuel, thrown]

theorem invariant1_call_passes_and_returns (ctx : Inputs) (fuel n rest site rule : Nat)
    (caller calleeStart calleeEnd : Env)
    (entered : ctx.hooks.enterCall site caller = some calleeStart)
    (accepted : runFuel ctx fuel (ctx.rules rule) n
      calleeStart = some (.ok rest calleeEnd)) :
    runFuel ctx (fuel + 1) (.call site rule) n caller =
      some (.ok rest (ctx.hooks.leaveCall site caller calleeEnd)) := by
  simp [runFuel, entered, accepted]

#print axioms invariant1_choice_rewinds
#print axioms invariant1_ahead_restores
#print axioms invariant1_notAhead_restores
#print axioms invariant1_call_passes_and_returns

end PegHs.EnvironmentEval
