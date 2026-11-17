import RenderComposition
import RenderFinalize

/-
The public entry's text, not only render's: generated_module_verbatim and
generated_module_with_rules_verbatim carried to the output of
Codegen.finalize (ADR 0097 invariant 3).

`Codegen.generate` returns `finalize opts marker (render opts g analysis
marker)`. The theorems of RenderComposition are about `finalSource`, render's
text with the restore markers still in it (`trace_sound` gives
`finalSource = renderTail "\n" first chunks`). The theorems below are about
`finalize shown marker finalSource`, the text that generate returns and the
CLI writes, with every marker line replaced by its LINE pragma and a '\n' at
the end. The `_header` theorem also takes render's list as the header lines
(the two comments, the LANGUAGE pragmas and the OPTIONS_GHC pragma) followed
by the rest, and shows those lines open the finalized file unchanged.

Premises left explicit in the theorems:
- `initial`, `trace`, `tokens_match`: the lexer obligations of
  generated_module (RenderComposition), on render's text.
- `verbatim_split`, `verbatim_imports_ok`, `verbatim_decls_ok`, `name_ok`,
  `exports_ok`, `user_ok`, `decls_ok`: as in generated_module_verbatim and
  generated_module_with_rules_verbatim.
- `eof`, `steps`: the lexer obligations of RenderFinalize.finalize_lex. A '\n'
  at the end adds no token, and each marker line lexes as its LINE pragma
  does.
- `source_ok`, `languages_ok` (`_header` only): the source file name and the
  `%language` arguments hold no '\n'.
-/

namespace PegHs.RenderFinalizeModule

open CFG GHCGrammar RenderModuleGHC RenderComposition RenderFinalize

theorem generated_module_finalized
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (shown marker : String)
    (name : List Symbol) (usesPegPrelude importsPrelude : Bool)
    (exports blocks verbatimImports verbatimDecls decls : List (List Symbol))
    (name_ok : Derives productions [.nonterminal 321] name)
    (exports_ok : ∀ item ∈ exports, Derives productions [.nonterminal 47] item)
    (verbatim_split : blocks.flatten =
      verbatimImports.foldl semiAppend [] ++ verbatimDecls.foldl semiAppend [])
    (verbatim_imports_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (verbatim_decls_ok : ∀ item ∈ verbatimDecls,
      Derives productions [.nonterminal 78] item)
    (decls_ok : ∀ item ∈ decls, Derives productions [.nonterminal 78] item)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ name ++ exportWord exports ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude).foldl semiAppend [] ++
        blocks.flatten ++ decls.foldl semiAppend []))
    (eof : lex (finalSource ++ "\n") = lex finalSource)
    (steps : Transparent lex shown marker [] 1 (textLines finalSource)) :
    lex (finalize shown marker finalSource) = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 0] finalTokens := by
  obtain ⟨hLex, hDerives⟩ := generated_module_verbatim lex first firstTokens chunks
    finalSource finalTokens name usesPegPrelude importsPrelude exports blocks
    verbatimImports verbatimDecls decls name_ok exports_ok verbatim_split
    verbatim_imports_ok verbatim_decls_ok decls_ok initial trace tokens_match
  exact ⟨(finalize_lex lex shown marker finalSource eof steps).trans hLex, hDerives⟩

theorem generated_module_with_rules_finalized
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (shown marker : String)
    (qualifiedName : Bool) (usesPegPrelude importsPrelude : Bool)
    (selected : List RenderModuleGHC.GeneratedExport) (dataTypes : Nat)
    (userExports blocks verbatimImports verbatimDecls : List (List Symbol))
    (parts : GeneratedParts)
    (user_ok : ∀ item ∈ userExports, Derives productions [.nonterminal 47] item)
    (verbatim_split : blocks.flatten =
      verbatimImports.foldl semiAppend [] ++ verbatimDecls.foldl semiAppend [])
    (verbatim_imports_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (verbatim_decls_ok : ∀ item ∈ verbatimDecls,
      Derives productions [.nonterminal 78] item)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ [.terminal (if qualifiedName then 122 else 118)] ++
        exportWord (parts.exports selected dataTypes userExports) ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude).foldl semiAppend [] ++
        blocks.flatten ++ parts.decls.foldl semiAppend []))
    (eof : lex (finalSource ++ "\n") = lex finalSource)
    (steps : Transparent lex shown marker [] 1 (textLines finalSource)) :
    lex (finalize shown marker finalSource) = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 0] finalTokens := by
  obtain ⟨hLex, hDerives⟩ := generated_module_with_rules_verbatim lex first
    firstTokens chunks finalSource finalTokens qualifiedName usesPegPrelude
    importsPrelude selected dataTypes userExports blocks verbatimImports
    verbatimDecls parts user_ok verbatim_split verbatim_imports_ok
    verbatim_decls_ok initial trace tokens_match
  exact ⟨(finalize_lex lex shown marker finalSource eof steps).trans hLex, hDerives⟩

-- The same, with render's list (`first` and the chunks) opened by the header
-- lines and the marker that freshRestoreMarker chooses: the finalized file
-- starts with the header lines, unchanged, and lexes to tokens that derive
-- from GHC's module start symbol.
theorem generated_module_with_rules_finalized_header
    (lex : String → List Symbol) (first : String) (firstTokens : List Symbol)
    (chunks : List Chunk) (finalSource : String) (finalTokens : List Symbol)
    (shown source : String) (languages : List String) (pruned : Bool) (k : Nat)
    (body : List String)
    (qualifiedName : Bool) (usesPegPrelude importsPrelude : Bool)
    (selected : List RenderModuleGHC.GeneratedExport) (dataTypes : Nat)
    (userExports blocks verbatimImports verbatimDecls : List (List Symbol))
    (parts : GeneratedParts)
    (layout : first :: chunks.map Chunk.source = headerLines source languages pruned ++ body)
    (body_ne : body ≠ [])
    (source_ok : '\n' ∉ source.toList)
    (languages_ok : ∀ x ∈ languages, '\n' ∉ x.toList)
    (user_ok : ∀ item ∈ userExports, Derives productions [.nonterminal 47] item)
    (verbatim_split : blocks.flatten =
      verbatimImports.foldl semiAppend [] ++ verbatimDecls.foldl semiAppend [])
    (verbatim_imports_ok : ∀ item ∈ verbatimImports,
      Derives productions [.nonterminal 59] item)
    (verbatim_decls_ok : ∀ item ∈ verbatimDecls,
      Derives productions [.nonterminal 78] item)
    (initial : lex first = firstTokens)
    (trace : Trace lex "\n" first firstTokens chunks finalSource finalTokens)
    (tokens_match : finalTokens = sourceSymbols
      ([.terminal 19] ++ [.terminal (if qualifiedName then 122 else 118)] ++
        exportWord (parts.exports selected dataTypes userExports) ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude).foldl semiAppend [] ++
        blocks.flatten ++ parts.decls.foldl semiAppend []))
    (eof : lex (finalSource ++ "\n") = lex finalSource)
    (steps : Transparent lex shown (restoreMarker k) [] 1 (textLines finalSource)) :
    finalize shown (restoreMarker k) finalSource =
      textUnlines (headerLines source languages pruned) ++
        finalizeAt shown (restoreMarker k) (1 + (headerLines source languages pruned).length)
          (String.intercalate "\n" body) ∧
    lex (finalize shown (restoreMarker k) finalSource) = finalTokens ∧
    Derives (layoutGrammar productions) [.nonterminal 0] finalTokens := by
  have hSource : finalSource =
      String.intercalate "\n" (headerLines source languages pruned ++ body) := by
    rw [(trace_sound initial trace).1, renderTail_intercalate, layout]
  refine ⟨?_, generated_module_with_rules_finalized lex first firstTokens chunks
    finalSource finalTokens shown (restoreMarker k) qualifiedName usesPegPrelude
    importsPrelude selected dataTypes userExports blocks verbatimImports
    verbatimDecls parts user_ok verbatim_split verbatim_imports_ok
    verbatim_decls_ok initial trace tokens_match eof steps⟩
  rw [hSource]
  exact finalize_render_header shown source languages pruned k body source_ok
    languages_ok body_ne

#print axioms generated_module_finalized
#print axioms generated_module_with_rules_finalized
#print axioms generated_module_with_rules_finalized_header

end PegHs.RenderFinalizeModule
