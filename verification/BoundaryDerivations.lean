import DerivationOneAction
import CommittedModuleDerivations

/-!
ADR 0097 I3, the boundary row "a grammar with one valid semantic action": the
module that peg-hs generates from

    %module OneAction
    S :: Int
    S <- 'a' { 1 }

derives from GHC's module start symbol. check-ghc-parser-trace.sh generates
the module, traces it with GHC 9.10.3's lexer and parser, and checks that GHC
parses it without a diagnostic (the public entry's result); check-ghc-
derivations.sh writes the trace as the certificate DerivationOneAction (the
Lean result). The premise is that of CommittedModuleDerivations: GHC's lexer
gives the certificate's token word.
-/

namespace PegHs.BoundaryDerivations

open CFG GHCGrammar CommittedModuleDerivations

theorem adr0097_i3_one_action_module_derives :
    Derives (layoutGrammar productions) [.nonterminal moduleStart]
      (certifiedWord OneAction.source0) := by
  unfold certifiedWord
  exact OneAction.invariant3_source_tokens

theorem adr0097_i3_one_action_module_nonempty : OneAction.source0 ≠ [] := by
  simp [OneAction.source0, OneAction.lexer0]

end PegHs.BoundaryDerivations
