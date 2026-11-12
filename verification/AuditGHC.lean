import Lean
import DerivationPeg
import DerivationPegSyntax

open Lean Elab Command in
run_cmd do
  for result in [``Peg.invariant3_module_trace, ``PegSyntax.invariant3_module_trace,
      ``Peg.invariant3_source_tokens, ``PegSyntax.invariant3_source_tokens] do
    let axioms ← collectAxioms result
    logInfo m!"{result}: {axioms}"
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{result} uses unexpected axiom {ax}"
