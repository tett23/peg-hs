import PublicGeneration
import RenderFinalizeModule

/-!
ADR 0097 invariant 3 at the public entry `generateWithWarnings`, with
GHC's module grammar: the text that the entry returns lexes, under GHC's
lexer, to tokens that derive from GHC's module start symbol.

PublicGeneration.invariant3_generateWithWarnings_text shows that a module
text is `RenderFinalize.finalize shown marker (render g a marker)` for a
grammar `g` that template expansion and `check` accept, with the marker that
selectMarker picks. RenderFinalizeModule.generated_module_with_rules_finalized
gives the derivation of `finalize shown marker finalSource` when render's text
`finalSource` is a composition that RenderComposition describes. This module
joins the two.

Premise (`renderShape`, not proved here): for every grammar that `check`
accepts and whose exports the generator defines, render's text with the
selected marker is such a composition (`ModuleShape`): the hypotheses of
generated_module_with_rules_finalized, that is the lexer obligations
(`initial`, `trace`, `tokens_match`) on GHC's lexer after finalize and the
derivations of the user's exports and verbatim blocks. Which of these hold
for every grammar is the subject of the render modules (RenderComposition,
RenderExpressionGHC, RenderPrinting); it is not composed here.
-/

namespace PegHs.PublicGenerationGHC

open CFG GHCGrammar RenderModuleGHC RenderComposition RenderFinalize RenderFinalizeModule

-- render's text `text`, finalized with `marker`, is a module that
-- generated_module_with_rules_finalized describes.
def ModuleShape (ghcLex : String → List Symbol) (shown marker text : String) : Prop :=
  ∃ (first : String) (firstTokens : List Symbol) (chunks : List Chunk) (finalTokens : List Symbol)
    (qualifiedName usesPegPrelude importsPrelude : Bool)
    (selected : List RenderModuleGHC.GeneratedExport) (dataTypes : Nat)
    (userExports blocks verbatimImports verbatimDecls : List (List Symbol))
    (parts : GeneratedParts),
    (∀ item ∈ userExports, Derives productions [.nonterminal 47] item) ∧
    blocks.flatten = verbatimImports.foldl semiAppend [] ++ verbatimDecls.foldl semiAppend [] ∧
    (∀ item ∈ verbatimImports, Derives productions [.nonterminal 59] item) ∧
    (∀ item ∈ verbatimDecls, Derives productions [.nonterminal 78] item) ∧
    finalizedLex ghcLex shown marker first = firstTokens ∧
    Trace (finalizedLex ghcLex shown marker) "\n" first firstTokens chunks text finalTokens ∧
    finalTokens = sourceSymbols
      ([.terminal 19] ++ [.terminal (if qualifiedName then 122 else 118)] ++
        exportWord (parts.exports selected dataTypes userExports) ++
        [.terminal 25, .terminal 103] ++
        (generatedImports usesPegPrelude importsPrelude).foldl semiAppend [] ++
        blocks.flatten ++ parts.decls.foldl semiAppend [])

theorem finalized_module_derives (ghcLex : String → List Symbol) (shown marker text : String)
    (shape : ModuleShape ghcLex shown marker text) :
    Derives (layoutGrammar productions) [.nonterminal 0] (ghcLex (finalize shown marker text)) := by
  obtain ⟨first, firstTokens, chunks, finalTokens, qualifiedName, usesPegPrelude, importsPrelude,
    selected, dataTypes, userExports, blocks, verbatimImports, verbatimDecls, parts,
    user_ok, verbatim_split, verbatim_imports_ok, verbatim_decls_ok, initial, trace,
    tokens_match⟩ := shape
  obtain ⟨hLex, hDerives⟩ := generated_module_with_rules_finalized ghcLex first firstTokens chunks
    text finalTokens shown marker qualifiedName usesPegPrelude importsPrelude selected dataTypes
    userExports blocks verbatimImports verbatimDecls parts user_ok verbatim_split
    verbatim_imports_ok verbatim_decls_ok initial trace tokens_match
  rw [hLex]
  exact hDerives

open PegHs.PublicGeneration in
theorem invariant3_generateWithWarnings_ghc {T : Type} (s : Inputs T) (p : Premises s)
    (input : List Char) (code : String) (ghcLex : String → List Symbol)
    (renderShape : ∀ g a, CheckGroups.check (toCheck g) (s.oracle g) = .ok a → s.missing g a = [] →
      ModuleShape ghcLex s.shown (Peg.Verification.selectMarker (s.render g a ""))
        (s.render g a (Peg.Verification.selectMarker (s.render g a ""))))
    (success : publicModule s input = .ok code) :
    Derives (layoutGrammar productions) [.nonterminal 0] (ghcLex code) := by
  obtain ⟨_, _, _, final, a, _, _, _, _, _, _, _, _, checked, defined, rfl⟩ :=
    invariant3_generateWithWarnings_text s p input code success
  exact finalized_module_derives ghcLex s.shown _ _ (renderShape final a checked defined)

end PegHs.PublicGenerationGHC

#print axioms PegHs.PublicGenerationGHC.finalized_module_derives
#print axioms PegHs.PublicGenerationGHC.invariant3_generateWithWarnings_ghc
