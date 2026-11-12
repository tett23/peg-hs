import Lean
import Guard
import Parsing
import Header
import Lexical
import Nullable
import Reachable
import Literal
import Signatures

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for moduleName in [`Guard, `Parsing, `Header, `Lexical, `Nullable,
      `Reachable, `Literal, `Signatures] do
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
