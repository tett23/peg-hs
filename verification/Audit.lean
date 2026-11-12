import Lean
import Guard
import Parsing
import Header
import Whitespace
import TemplateExpansion
import TemplateExpansionFresh
import TemplateSubstitution
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

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in [`Guard, `Parsing, `Header, `Lexical, `Whitespace, `TemplateQueue,
      `TemplateSubstitution, `TemplateExpansion, `TemplateExpansionFresh, `Nullable, `Reachable, `Literal, `Signatures, `File,
      `Consumption, `FileTrees, `Pipeline, `Pragmas, `RuleRejection, `RuleRejectionRefs,
      `RuleRejectionRepeat, `RuleRejectionNullable] do
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
