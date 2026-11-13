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

-- ruleDecl emits a closing parenthesis for each present wrapper.
def wrapChoice (wrapper : Option (List Symbol)) (inner : List Symbol) : List Symbol :=
  match wrapper with
  | none => inner
  | some fn => fn ++ [.terminal 107] ++ inner ++ [.terminal 108]

theorem wrap_choice_valid (wrapper : Option (List Symbol))
    (wrapper_ok : ∀ fn ∈ wrapper, Derives productions [.nonterminal 217] fn)
    (inner_ok : Derives productions [.nonterminal 217] inner) :
    Derives productions [.nonterminal 217] (wrapChoice wrapper inner) := by
  cases wrapper with
  | none => exact inner_ok
  | some fn =>
    exact RenderExpressionGHC.application_parenthesized
      (wrapper_ok fn (by simp)) (RenderExpressionGHC.fexp_to_texp inner_ok)

def expectWrapper (hasLabel : Bool) : Option (List Symbol) :=
  if hasLabel then some [.terminal 121, .terminal 130] else none

-- PegRt.token and PegRt.node are both QVARIDs, and kindVar emits a VARID.
def treeWrapper (syntaxMode inlineRule : Bool) : Option (List Symbol) :=
  if syntaxMode && !inlineRule then some [.terminal 121, .terminal 117] else none

-- memo and memoLR have the same token classes. memoArg also applies a key.
inductive MemoCall where
  | nomemo
  | table
  | withKey (wildcards : List Bool)

def MemoCall.tokens : MemoCall → List Symbol
  | .nomemo => [.terminal 121, .terminal 130]
  | .table => [.terminal 121, .terminal 117, .terminal 130]
  | .withKey ps => [.terminal 121, .terminal 117, .terminal 130] ++ RenderDeclarationsGHC.memoKeyWord ps

theorem memo_call_valid (memo : MemoCall) :
    Derives productions [.nonterminal 217] memo.tokens := by
  have table := RenderExpressionGHC.application
    (RenderExpressionGHC.application RenderExpressionGHC.qualified_function
      RenderDeclarationsGHC.varid_argument) RenderExpressionGHC.string_argument
  cases memo with
  | nomemo => exact RenderExpressionGHC.application RenderExpressionGHC.qualified_function
                        RenderExpressionGHC.string_argument
  | table => exact table
  | withKey ps => exact RenderExpressionGHC.application table (RenderDeclarationsGHC.memo_key_argument ps)

theorem rule_body_valid (first : Alternative) (rest : List Alternative)
    (memo : MemoCall) (hasLabel syntaxMode inlineRule : Bool) :
    Derives productions [.nonterminal 211]
      (memo.tokens ++ [.terminal 107] ++ wrapChoice (expectWrapper hasLabel)
        (wrapChoice (treeWrapper syntaxMode inlineRule) (choiceTokens first rest)) ++ [.terminal 108]) := by
  have expect_ok : ∀ fn ∈ expectWrapper hasLabel, Derives productions [.nonterminal 217] fn := by
    intro fn member
    unfold expectWrapper at member
    split at member <;> cases member
    exact RenderExpressionGHC.application RenderExpressionGHC.qualified_function
      RenderExpressionGHC.string_argument
  have tree_ok : ∀ fn ∈ treeWrapper syntaxMode inlineRule, Derives productions [.nonterminal 217] fn := by
    intro fn member
    unfold treeWrapper at member
    split at member <;> cases member
    exact RenderExpressionGHC.application RenderExpressionGHC.qualified_function
      RenderDeclarationsGHC.varid_argument
  exact RenderExpressionGHC.fexp_to_exp (RenderExpressionGHC.application_parenthesized (memo_call_valid memo)
    (RenderExpressionGHC.fexp_to_texp (wrap_choice_valid _ expect_ok
      (wrap_choice_valid _ tree_ok (choice_tokens_derive first rest)))))

#print axioms rule_body_valid

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
