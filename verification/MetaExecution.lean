import PredicateBindings
import EnvironmentDepth
import EnvironmentActual

open PegHs PegHs.EnvironmentEval PegHs.MetagrammarPredicates

namespace PegHs.MetaExecution

private def inputs (rules : Nat → Body) (terms : Nat → Option ConcreteTerminal.Terminal)
    (preds : Array Site) (actions : Array (String × String × DepthAction))
    (calls : Array EnvironmentDepth.CallSite) (source : List Char) : Inputs :=
  let sites := preds.map fun site => (classifySite site).map fun kind => (kind, site.2.1)
  { rules, terms, input := source
    classes := GhcPredicates.classes
    sites := fun id => sites[id]?.join
    actions := fun id => actions[id]?.map (·.2.2)
    predicateEnv := fun id env => match sites[id]?.join with
      | some (kind, _) => PredicateBindings.predicateEnv kind env
      | none => { captured := [], depth := env.depth }
    hooks := EnvironmentDepth.hooks (fun id => calls[id]?) (fun _ _ _ => none) }

def peg := inputs MetaTerminal1.environmentBody MetaTerminal1.termById
  MetaTerminal1.predicateSites MetaTerminal1.depthActions MetaTerminal1.callSites
def syntaxPeg := inputs MetaTerminal2.environmentBody MetaTerminal2.termById
  MetaTerminal2.predicateSites MetaTerminal2.depthActions MetaTerminal2.callSites

def context (syntaxMode : Bool) (input : List Char) :=
  if syntaxMode then syntaxPeg input else peg input

def startRule (syntaxMode : Bool) :=
  if syntaxMode then MetaTerminal2.startRule else MetaTerminal1.startRule

def FileResult (syntaxMode : Bool) (input : List Char) (reply : Reply) : Prop :=
  let ctx := context syntaxMode input
  Derives ctx (ctx.rules (startRule syntaxMode)) input.length {} reply

theorem invariant1_file_result (syntaxMode : Bool) (input : List Char) :
    ∃ r, FileResult syntaxMode input r ∧ ∀ other, FileResult syntaxMode input other → other = r := by
  let ctx := context syntaxMode input
  let start := startRule syntaxMode
  have rules : ctx.rules = (if syntaxMode then MetaTerminal2.environmentBody
      else MetaTerminal1.environmentBody) := by cases syntaxMode <;> rfl
  obtain ⟨fuel, r, h⟩ := invariant1_actual_environment_total syntaxMode ctx rules
    (input.length, start) {}
  refine ⟨r, invariant1_runFuel_sound h, ?_⟩
  intro other derivation
  obtain ⟨k, observed⟩ := invariant1_derivation_has_fuel derivation
  exact invariant1_result_unique ctx observed h

#print axioms invariant1_file_result

end PegHs.MetaExecution
