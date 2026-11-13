import RenderExpressionGHC
import RenderExpressionLexer
import RenderPrimitiveDoGHC

namespace PegHs.RenderPrimitiveChoice

open PegHs.CFG PegHs.GHCGrammar

structure Alternative where
  source : String
  tokens : List Symbol
  valid : Derives productions [.nonterminal 229] tokens

-- A generated alternative always ends with the action's return statement.
def doAlternative (first : RenderPrimitiveDoGHC.Statement) (rest : List RenderPrimitiveDoGHC.Statement) :
    Alternative where
  source := RenderPrimitiveDo.printedDo (first.source :: rest.map RenderPrimitiveDoGHC.Statement.source)
  tokens := [.terminal 125, .terminal 101] ++ RenderPrimitiveDoGHC.statementTokens first rest ++ [.terminal 102]
  valid := RenderExpressionGHC.aexp_to_texp (RenderPrimitiveDoGHC.do_tokens_derive first rest)

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

-- Each step accounts for the lexer at one comma boundary.
theorem printed_choice_ghc (lex : String → List Symbol) (first : Alternative) (rest : List Alternative)
    (initial : lex ("PegRt.choice\n      [ " ++ first.source) = [.terminal 121, .terminal 105] ++ first.tokens)
    (trace : RenderComposition.Trace lex "\n      , " ("PegRt.choice\n      [ " ++ first.source)
      ([.terminal 121, .terminal 105] ++ first.tokens)
      (rest.map fun alt => ⟨alt.source, [.terminal 114] ++ alt.tokens⟩) openSource openTokens)
    (closing : lex (openSource ++ "\n      ]") = openTokens ++ [.terminal 106]) :
    Derives productions [.nonterminal 217] (lex (printedChoice first rest)) := by
  obtain ⟨hs, ht, _⟩ := RenderComposition.trace_sound initial trace
  have fold (alts : List Alternative) (src : String) (tokens : List Symbol) :
      let chunks := alts.map fun alt => (⟨alt.source, [.terminal 114] ++ alt.tokens⟩ : RenderComposition.Chunk)
      RenderComposition.renderTail "\n      , " ("PegRt.choice\n      [ " ++ src) chunks =
        "PegRt.choice\n      [ " ++ alts.foldl (fun acc alt => acc ++ "\n      , " ++ alt.source) src ∧
      RenderComposition.tokenTail ([.terminal 121, .terminal 105] ++ tokens) chunks =
        [.terminal 121, .terminal 105] ++ (alts.map Alternative.tokens).foldl RenderExpressionGHC.commaAppend tokens := by
    induction alts generalizing src tokens with
    | nil => exact ⟨rfl, rfl⟩
    | cons a more ih =>
      simpa [RenderComposition.renderTail, RenderComposition.tokenTail, RenderExpressionGHC.commaAppend,
        List.append_assoc, String.append_assoc] using ih (src ++ "\n      , " ++ a.source)
          (RenderExpressionGHC.commaAppend tokens a.tokens)
  obtain ⟨sourceEq, tokensEq⟩ := fold rest first.source first.tokens
  rw [printed_choice_fold, ← sourceEq, ← hs, closing, ht, tokensEq]
  exact choice_tokens_derive first rest

#print axioms doAlternative
#print axioms printed_choice_ghc
#print axioms printed_choice_fold
#print axioms choice_tokens_derive

end PegHs.RenderPrimitiveChoice
