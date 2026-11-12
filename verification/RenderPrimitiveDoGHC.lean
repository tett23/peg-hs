import RenderPrimitiveDo
import RenderComposition
import RenderExpressionGHC

namespace PegHs.RenderPrimitiveDoGHC

open PegHs.CFG PegHs.GHCGrammar

structure Statement where
  source : String
  tokens : List Symbol
  valid : Derives productions [.nonterminal 257] tokens

def chunks (rest : List Statement) : List RenderComposition.Chunk :=
  rest.map fun statement =>
    ⟨statement.source, [.terminal 113] ++ statement.tokens⟩

def statementTokens (first : Statement) (rest : List Statement) : List Symbol :=
  rest.foldl (fun acc statement =>
    RenderExpressionGHC.semicolonAppend acc statement.tokens) first.tokens

private theorem render_tail_prefix (lead separator first : String)
    (rest : List RenderComposition.Chunk) :
    RenderComposition.renderTail separator (lead ++ first) rest =
      lead ++ RenderComposition.renderTail separator first rest := by
  induction rest generalizing first with
  | nil => rfl
  | cons chunk more ih =>
    simpa [RenderComposition.renderTail, String.append_assoc] using
      ih (first ++ separator ++ chunk.source)

theorem printed_do_text (first : Statement) (rest : List Statement) :
    RenderComposition.renderTail "\n          ; "
      ("do { " ++ first.source) (chunks rest) ++ "\n          }" =
    RenderPrimitiveDo.printedDo (first.source :: rest.map Statement.source) := by
  rw [render_tail_prefix]
  rw [RenderComposition.renderTail_intercalate]
  simp [chunks, List.map_map, Function.comp_def, RenderPrimitiveDo.printedDo,
    RenderPrimitiveDo.join_intersperse, String.append_assoc]

theorem token_tail_eq (first : Statement) (rest : List Statement) :
    RenderComposition.tokenTail
      ([.terminal 125, .terminal 101] ++ first.tokens) (chunks rest) =
    [.terminal 125, .terminal 101] ++ statementTokens first rest := by
  have general (initial : List Symbol) (tail : List Statement) :
      RenderComposition.tokenTail
        ([.terminal 125, .terminal 101] ++ initial) (chunks tail) =
      [.terminal 125, .terminal 101] ++
        tail.foldl (fun acc statement =>
          RenderExpressionGHC.semicolonAppend acc statement.tokens) initial := by
    induction tail generalizing initial with
    | nil => rfl
    | cons statement more ih =>
      simpa [chunks, RenderComposition.tokenTail, List.foldl,
        RenderExpressionGHC.semicolonAppend, List.append_assoc] using
        ih (initial ++ [.terminal 113] ++ statement.tokens)
  exact general first.tokens rest

theorem do_tokens_derive (first : Statement) (rest : List Statement) :
    Derives productions [.nonterminal 218]
      ([.terminal 125, .terminal 101] ++ statementTokens first rest ++
        [.terminal 102]) := by
  have rest_ok : ∀ tokens ∈ rest.map Statement.tokens,
      Derives productions [.nonterminal 257] tokens := by
    intro tokens member
    obtain ⟨statement, _, equal⟩ := List.mem_map.mp member
    exact equal ▸ statement.valid
  have h := RenderExpressionGHC.do_many first.tokens (rest.map Statement.tokens)
    first.valid rest_ok
  simpa [statementTokens, List.foldl_map] using h

-- Each lexical premise is for a prefix after exactly one statement is
-- appended. This leaves the GHC lexer bridge visible without assuming the
-- desired derivation of the entire do block.
theorem printed_do_ghc
    (lex : String → List Symbol) (first : Statement) (rest : List Statement)
    (openSource : String) (openTokens : List Symbol)
    (initial : lex ("do { " ++ first.source) =
      [.terminal 125, .terminal 101] ++ first.tokens)
    (trace : RenderComposition.Trace lex "\n          ; "
      ("do { " ++ first.source)
      ([.terminal 125, .terminal 101] ++ first.tokens)
      (chunks rest) openSource openTokens)
    (closing : lex (openSource ++ "\n          }") =
      openTokens ++ [.terminal 102]) :
    Derives productions [.nonterminal 218]
      (lex (RenderPrimitiveDo.printedDo
        (first.source :: rest.map Statement.source))) := by
  obtain ⟨source_eq, tokens_eq, _⟩ :=
    RenderComposition.trace_sound initial trace
  rw [← printed_do_text, ← source_eq, closing, tokens_eq, token_tail_eq]
  exact do_tokens_derive first rest

#print axioms token_tail_eq
#print axioms do_tokens_derive
#print axioms printed_do_text
#print axioms printed_do_ghc

end PegHs.RenderPrimitiveDoGHC
