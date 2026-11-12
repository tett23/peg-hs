import RenderExpressionGHC
import RenderExpressionLexer

namespace PegHs.RenderPrimitiveChoice

open PegHs.CFG PegHs.GHCGrammar

structure Alternative where
  source : String
  tokens : List Symbol
  valid : Derives productions [.nonterminal 229] tokens

-- The inner `PegRt.choice` fragment in Codegen.ruleDecl. A parsed hpeg rule
-- has at least one alternative (Peg.hpeg: Alts <- a:Alt as:MoreAlt*).
def printedChoice (first : Alternative) (rest : List Alternative) : String :=
  "PegRt.choice\n      [ " ++
    String.intercalate "\n      , "
      (first.source :: rest.map Alternative.source) ++ "\n      ]"

def choiceTokens (first : Alternative) (rest : List Alternative) : List Symbol :=
  [.terminal 121, .terminal 105] ++
    (rest.map Alternative.tokens).foldl RenderExpressionGHC.commaAppend
      first.tokens ++ [.terminal 106]

theorem printed_choice_fold (first : Alternative) (rest : List Alternative) :
    printedChoice first rest =
      "PegRt.choice\n      [ " ++
        rest.foldl (fun acc alt => acc ++ "\n      , " ++ alt.source)
          first.source ++ "\n      ]" := by
  simp [printedChoice, RenderExpressionLexer.intercalate_cons,
    List.foldl_map, String.append_assoc]

theorem choice_tokens_derive (first : Alternative) (rest : List Alternative) :
    Derives productions [.nonterminal 217] (choiceTokens first rest) := by
  cases rest with
  | nil =>
    simpa [choiceTokens] using
      RenderExpressionGHC.choice_singleton first.valid
  | cons second more =>
    have more_ok : ∀ tokens ∈ more.map Alternative.tokens,
        Derives productions [.nonterminal 229] tokens := by
      intro tokens member
      obtain ⟨alt, _, equal⟩ := List.mem_map.mp member
      exact equal ▸ alt.valid
    simpa [choiceTokens, List.foldl_map, List.foldl_cons] using
      RenderExpressionGHC.choice_many first.tokens second.tokens
        (more.map Alternative.tokens) first.valid second.valid more_ok

#print axioms printed_choice_fold
#print axioms choice_tokens_derive

end PegHs.RenderPrimitiveChoice
