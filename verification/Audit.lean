import Lean
import CallOrder
import CallTables
import RecursiveEval
import ConcreteTerminal
import TerminalCursor
import Utf8Terminals
import ConcreteTerminalBody
import LabeledConcreteBody
import ConcreteTables
import MetagrammarPredicates
import PredicateBindings
import Guard
import SemanticPredicates
import EnvironmentEval
import CaptureWindow
import EnvironmentFuel
import EnvironmentDerivation
import EnvironmentActual
import MetaExecution
import FileEntry
import PublicParsing
import FileExamples
import EnvironmentDepth
import CapturedPredicates
import GhcPredicates
import ParameterPredicates
import EscapePredicates
import ExpressionDepth
import Parsing
import Header
import Whitespace
import TemplateQueue
import Lexical
import Nullable
import Reachable
import Literal
import Signatures
import File
import Consumption
import FileTrees
import Pipeline
import Pragmas
import RuleRejection
import RuleRejectionRefs
import RuleRejectionRepeat
import RuleRejectionNullable

namespace PegHs.RecursiveEval

-- The two tables are extracted from Peg.hpeg and PegSyntax.hpeg by
-- ExtractCallOrder.hs during verification/check.sh.
def actualMetaRules (syntaxMode : Bool) : Nat → CallOrder.Body :=
  if syntaxMode then Meta2.rules else Meta1.rules

theorem invariant1_actual_meta_total (syntaxMode : Bool) (token : Nat → Option Nat)
    (rule remaining : Nat) :
    ∃ fuel result,
      runFuel (actualMetaRules syntaxMode) token fuel
        (actualMetaRules syntaxMode rule) remaining = some result := by
  cases syntaxMode with
  | false =>
      simpa [actualMetaRules] using
        (invariant1_rule_executable (token := token) Meta1.invariant1_checked (remaining, rule))
  | true =>
      simpa [actualMetaRules] using
        (invariant1_rule_executable (token := token) Meta2.invariant1_checked (remaining, rule))

#print axioms invariant1_actual_meta_total

end PegHs.RecursiveEval

namespace PegHs.ConcreteTerminalBody

-- Both extracted metagrammars terminate on every concrete character input.
theorem invariant1_actual_concrete_total (syntaxMode : Bool)
    (input : List Char) (rule : Nat) :
    ∃ fuel result,
      (if syntaxMode then MetaTerminal2.runConcrete input fuel rule
       else MetaTerminal1.runConcrete input fuel rule) = some result := by
  cases syntaxMode with
  | false => simpa using MetaTerminal1.invariant1_runConcrete_total input rule
  | true => simpa using MetaTerminal2.invariant1_runConcrete_total input rule

#print axioms invariant1_actual_concrete_total

theorem invariant1_actual_labeled_total (syntaxMode : Bool)
    (oracle : Nat → Nat → Bool) (input : List Char) (rule : Nat) :
    ∃ fuel result,
      (if syntaxMode then MetaTerminal2.runLabeled oracle input fuel rule
       else MetaTerminal1.runLabeled oracle input fuel rule) = some result := by
  cases syntaxMode with
  | false => simpa using MetaTerminal1.invariant1_runLabeled_total oracle input rule
  | true => simpa using MetaTerminal2.invariant1_runLabeled_total oracle input rule

#print axioms invariant1_actual_labeled_total

end PegHs.ConcreteTerminalBody

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in [`CallOrder, `CallTables, `RecursiveEval, `Utf8Terminals, `ConcreteTerminal, `TerminalCursor, `ConcreteTerminalBody,
      `LabeledConcreteBody, `ConcreteTables, `MetagrammarPredicates, `PredicateBindings, `Guard, `Parsing, `Header, `Lexical,
      `Whitespace, `TemplateQueue, `Nullable, `Reachable, `Literal, `Signatures,
      `File, `Consumption, `FileTrees, `Pipeline, `Pragmas, `RuleRejection,
      `RuleRejectionRefs, `RuleRejectionRepeat, `RuleRejectionNullable, `EnvironmentEval, `CaptureWindow, `EnvironmentFuel, `EnvironmentDerivation, `EnvironmentActual, `MetaExecution, `FileEntry, `PublicParsing, `FileExamples, `EnvironmentDepth, `CapturedPredicates, `SemanticPredicates, `GhcPredicates,
      `ParameterPredicates, `EscapePredicates, `ExpressionDepth] do
    let some idx := env.getModuleIdx? moduleName | throwError "missing module {moduleName}"
    let mut checked := 0
    for (name, info) in env.constants.toList do
      if env.getModuleIdxFor? name != some idx then continue
      if info.isAxiom then throwError "unexpected axiom declaration {name}"
      if !info.isTheorem then continue
      checked := checked + 1
      let axioms ← collectAxioms name
      logInfo m!"{name}: {axioms}"
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "{name} depends on unexpected axiom {ax}"
    if checked == 0 then throwError "no theorems in {moduleName}"
