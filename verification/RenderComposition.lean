import RenderModuleGHC
import RenderExpressionLexer
import RenderDeclarationsGHC

namespace PegHs.RenderComposition

open CFG GHCGrammar RenderModuleGHC

-- A chunk is a single element of Codegen.render's intercalated list.
-- Its token annotation excludes tokens introduced by previous chunks.
structure Chunk where
  source : String
  tokens : List Symbol

def renderTail (separator first : String) (chunks : List Chunk) : String :=
  chunks.foldl (fun acc chunk => acc ++ separator ++ chunk.source) first

def tokenTail (first : List Symbol) (chunks : List Chunk) : List Symbol :=
  chunks.foldl (fun acc chunk => acc ++ chunk.tokens) first

theorem renderTail_append (separator first : String) (left right : List Chunk) :
    renderTail separator first (left ++ right) =
      renderTail separator (renderTail separator first left) right := by
  simp [renderTail, List.foldl_append]

theorem tokenTail_append (first : List Symbol) (left right : List Chunk) :
    tokenTail first (left ++ right) =
      tokenTail (tokenTail first left) right := by
  simp [tokenTail, List.foldl_append]

theorem renderTail_intercalate (separator first : String) (chunks : List Chunk) :
    renderTail separator first chunks =
      String.intercalate separator (first :: chunks.map Chunk.source) := by
  simpa [renderTail, List.foldl_map] using
    (RenderExpressionLexer.intercalate_cons separator first
      (chunks.map Chunk.source)).symm

-- GHC inserts virtual layout tokens according to the entire preceding input.
-- A step therefore checks the lexer on the full prefix after adding a chunk.
-- This is a local, independently checkable obligation, not an assumption that
-- the final module's token sequence is already correct.
inductive Trace (lex : String → List Symbol) (separator : String) :
    String → List Symbol → List Chunk → String → List Symbol → Prop where
  | done (source : String) (tokens : List Symbol) :
      Trace lex separator source tokens [] source tokens
  | next {source finalSource : String} {tokens finalTokens : List Symbol}
      {chunk : Chunk} {rest : List Chunk}
      (step : lex (source ++ separator ++ chunk.source) = tokens ++ chunk.tokens)
      (tail : Trace lex separator (source ++ separator ++ chunk.source)
        (tokens ++ chunk.tokens) rest finalSource finalTokens) :
      Trace lex separator source tokens (chunk :: rest) finalSource finalTokens

theorem trace_sound {lex : String → List Symbol} {separator first finalSource : String}
    {firstTokens finalTokens : List Symbol} {chunks : List Chunk}
    (initial : lex first = firstTokens)
    (trace : Trace lex separator first firstTokens chunks finalSource finalTokens) :
    finalSource = renderTail separator first chunks ∧
    finalTokens = tokenTail firstTokens chunks ∧
    lex finalSource = finalTokens := by
  induction trace with
  | done source tokens => exact ⟨rfl, rfl, initial⟩
  | @next source finalSource tokens finalTokens chunk rest step tail ih =>
    obtain ⟨hSource, hTokens, hLex⟩ := ih step
    exact ⟨by simpa [renderTail] using hSource,
      by simpa [tokenTail] using hTokens, hLex⟩

theorem trace_append {lex : String → List Symbol} {separator first middle last : String}
    {firstTokens middleTokens lastTokens : List Symbol}
    {beforeChunks afterChunks : List Chunk}
    (left : Trace lex separator first firstTokens beforeChunks middle middleTokens)
    (right : Trace lex separator middle middleTokens afterChunks last lastTokens) :
    Trace lex separator first firstTokens (beforeChunks ++ afterChunks) last lastTokens := by
  induction left with
  | done _ _ => simpa using right
  | next step tail ih =>
    simpa using Trace.next step (ih right)

-- The CFG theorem is valid for arbitrary export, import and declaration lists.
-- The two remaining premises are observable lexer trace obligations: the
-- prefix trace and its token annotations must match those CFG fragments.
theorem generated_module
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (name : List Symbol) (usesPegPrelude importsPrelude : Bool)
    (exports verbatimImports decls : List (List Symbol))
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : ∀ item ∈ exports, Derives productions [.nonterminal 47] item)
    (verbatim_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (decls_ok : ∀ item ∈ decls, Derives productions [.nonterminal 78] item)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ name ++ exportWord exports ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude ++ verbatimImports).foldl
          semiAppend [] ++ decls.foldl semiAppend [])) :
    lex finalSource = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 32] finalTokens := by
  have hLex := (trace_sound initial trace).2.2
  constructor
  · exact hLex
  · rw [tokens_match]
    exact generated_with_imports name usesPegPrelude importsPrelude exports
      verbatimImports decls name_ok exports_ok verbatim_ok decls_ok

-- Codegen.ruleDecl contributes a signature and a binding for each emitted
-- rule. Other generated declarations may precede these pairs. The exact
-- ruleDecl rendering is pinned by check-render-declarations-ghc.sh.
structure RuleFragment where
  ty : List Symbol
  args : List (List Symbol)
  body : List Symbol
  type_ok : Derives productions [.nonterminal 163] ty
  args_ok : ∀ arg ∈ args, Derives productions [.nonterminal 218] arg
  body_ok : Derives productions [.nonterminal 211] body

def ruleItems (rules : List RuleFragment) : List (List Symbol) :=
  rules.flatMap fun rule =>
    RenderDeclarationsGHC.generatedPair rule.ty rule.args rule.body

theorem rule_items_valid (rules : List RuleFragment) :
    ∀ item ∈ ruleItems rules,
      Derives productions [.nonterminal 78] item := by
  intro item member
  obtain ⟨rule, _, inside⟩ := List.mem_flatMap.mp member
  simp only [RenderDeclarationsGHC.generatedPair, List.mem_cons,
    List.mem_nil_iff, or_false] at inside
  rcases inside with signature | binding
  · rw [signature]
    exact RenderDeclarationsGHC.signature_named_ctype rule.type_ok
  · rw [binding]
    exact RenderDeclarationsGHC.binding_named_arguments rule.args rule.args_ok
      rule.body_ok

theorem generated_module_with_rules
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (name : List Symbol) (usesPegPrelude importsPrelude : Bool)
    (exports verbatimImports otherDecls : List (List Symbol))
    (rules : List RuleFragment)
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : ∀ item ∈ exports, Derives productions [.nonterminal 47] item)
    (verbatim_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (other_ok : ∀ item ∈ otherDecls,
      Derives productions [.nonterminal 78] item)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ name ++ exportWord exports ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude ++ verbatimImports).foldl
          semiAppend [] ++ (otherDecls ++ ruleItems rules).foldl semiAppend [])) :
    lex finalSource = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 32] finalTokens := by
  apply generated_module lex first firstTokens chunks finalSource finalTokens name
    usesPegPrelude importsPrelude exports verbatimImports
    (otherDecls ++ ruleItems rules) name_ok exports_ok verbatim_ok
  · intro item member
    rcases List.mem_append.mp member with inOther | inRule
    · exact other_ok item inOther
    · exact rule_items_valid rules item inRule
  · exact initial
  · exact trace
  · exact tokens_match

#print axioms renderTail_intercalate
#print axioms renderTail_append
#print axioms tokenTail_append
#print axioms trace_sound
#print axioms trace_append
#print axioms generated_module
#print axioms rule_items_valid
#print axioms generated_module_with_rules

end PegHs.RenderComposition
