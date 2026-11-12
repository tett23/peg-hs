import MetagrammarPredicates
import EnvironmentEval

namespace PegHs.PredicateBindings
open MetagrammarPredicates SemanticPredicates EnvironmentEval

def captureName : Kind → Option String
  | .depth => none
  | .typeText => some "ty"
  | .unicodeEscape => some "h"
  | .classItem => some "s"
  | _ => some "c"

def predicateEnv (k : Kind) (env : EnvironmentEval.Env) : SemanticPredicates.Env :=
  { depth := env.depth, captured := (captureName k).map env.lookup |>.getD [] }

-- A rule starts with no local text bindings. Only explicit text captures
-- qualify; a later binding with the same name shadows the previous one.
def scope (sites : Array Site) (bound : List String) : Body → Option (List String)
  | .eps | .terminal _ | .call .. => some bound
  | .predicate i => do
      let site ← sites[i]?
      let kind ← classifySite site
      guard ((captureName kind).all bound.contains)
      return bound
  | .seq a b => do scope sites (← scope sites bound a) b
  | .alt a b => do
      let left ← scope sites bound a
      let right ← scope sites bound b
      return left.filter right.contains
  | .ahead a | .notAhead a => do
      let _ ← scope sites bound a
      return bound
  | .star a => do
      let after ← scope sites bound a
      guard (bound.all after.contains)
      return bound
  | .capture a | .label _ _ a => scope sites bound a
  | .bind _ name a => do
      let after ← scope sites bound a
      match a with
      | .capture _ => return name :: after
      | _ => return after.filter (· != name)

def allScoped (sites : Array Site) (rules : Array Body) :=
  rules.all fun body => (scope sites [] body).isSome

theorem invariant1_local_captures :
    allScoped MetaTerminal1.predicateSites MetaTerminal1.environmentBodyTable = true ∧
    allScoped MetaTerminal2.predicateSites MetaTerminal2.environmentBodyTable = true := by
  decide +kernel

end PegHs.PredicateBindings
