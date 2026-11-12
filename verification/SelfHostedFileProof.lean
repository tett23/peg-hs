import TranslatedStrictFile
import FileEntry
import VerbatimRule

namespace PegHs.MetaExecution
open EnvironmentEval

theorem invariant1_translated_strict_file (input : List Char) (reply : Reply) :
    Derives (context false input) translatedStrictFile input.length {} reply ↔
      FileResult false input reply := by rfl

theorem invariant1_translated_strict_run (input : List Char) (reply : Reply) :
    (∃ fuel, runFuel (context false input) fuel translatedStrictFile input.length {} = some reply) ↔
      FileResult false input reply := by
  rw [← invariant1_translated_strict_file]
  exact ⟨fun ⟨_, observed⟩ => invariant1_runFuel_sound observed, invariant1_derivation_has_fuel⟩

theorem invariant1_strict_child_bodies (input : List Char) :
    translatedStrictTopItem = (context false input).rules 1 ∧
    translatedStrictTopOne = (context false input).rules 2 ∧
    translatedStrictWs = (context false input).rules 4 ∧
    translatedStrictSpaceChar = (context false input).rules 5 ∧
    translatedStrictComment = (context false input).rules 6 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem invariant1_strict_identifier_bodies (input : List Char) :
    translatedStrictIdent = (context false input).rules 8 ∧
    translatedStrictIdentStart = (context false input).rules 9 ∧
    translatedStrictIdentChar = (context false input).rules 10 := ⟨rfl, rfl, rfl⟩

theorem invariant1_strict_verbatim_bodies (input : List Char) :
    translatedStrictHere = (context false input).rules 3 ∧
    translatedStrictVerbatim = (context false input).rules 11 := ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
theorem invariant1_strict_declaration (input : List Char) :
    translatedStrictDeclaration = (context false input).rules 13 := rfl

theorem invariant1_strict_template_parameters (input : List Char) :
    translatedStrictTemplateParams = (context false input).rules 14 ∧
    translatedStrictTemplateParam = (context false input).rules 15 := ⟨rfl, rfl⟩

theorem invariant1_strict_type_text (input : List Char) :
    translatedStrictTypeText = (context false input).rules 16 := rfl

theorem invariant1_strict_param_list (input : List Char) :
    translatedStrictParamList = (context false input).rules 17 := rfl

theorem invariant1_strict_param_chunks (input : List Char) :
    translatedStrictParamChunks = (context false input).rules 18 := rfl

set_option maxRecDepth 4096 in
theorem invariant1_strict_param_chunk (input : List Char) :
    translatedStrictParamChunk = (context false input).rules 19 := rfl

theorem invariant1_strict_alternatives (input : List Char) :
    translatedStrictAlts = (context false input).rules 20 ∧
    translatedStrictMoreAlt = (context false input).rules 21 := ⟨rfl, rfl⟩

theorem invariant1_strict_alt_constructor (input : List Char) :
    translatedStrictAlt = (context false input).rules 22 ∧
    translatedStrictConstructor = (context false input).rules 23 := ⟨rfl, rfl⟩

theorem invariant1_strict_item (input : List Char) :
    translatedStrictItem = (context false input).rules 24 := rfl

theorem invariant1_strict_item_boundaries (input : List Char) :
    translatedStrictDeclStart = (context false input).rules 25 ∧
    translatedStrictBinding = (context false input).rules 26 := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
theorem invariant1_strict_prefix (input : List Char) :
    translatedStrictPrefixE = (context false input).rules 27 := rfl

theorem invariant2_translated_unterminated_block (pre xs : List Char) (env : Env)
    (missing : verbatimRest xs = []) :
    Derives (context false (pre ++ '%' :: '{' :: xs)) translatedStrictVerbatim
      (xs.length + 2) env (.throwLabel 0 "verbatim" (some "unterminated %{ block")) :=
  invariant2_unterminated_verbatim false pre xs env missing

end PegHs.MetaExecution
