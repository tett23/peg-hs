import TranslatedStrictFile
import TotalFile
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

theorem invariant1_strict_label_suffix (input : List Char) :
    translatedStrictLabeled = (context false input).rules 28 ∧
    translatedStrictLabelPart = (context false input).rules 29 := ⟨rfl, rfl⟩

theorem invariant1_strict_postfix (input : List Char) :
    translatedStrictSuffixE = (context false input).rules 30 ∧
    translatedStrictPostOps = (context false input).rules 31 ∧
    translatedStrictPostOp = (context false input).rules 32 := ⟨rfl, rfl, rfl⟩

theorem invariant1_strict_quoted_literals (input : List Char) :
    translatedStrictLit1 = (context false input).rules 39 ∧
    translatedStrictLit2 = (context false input).rules 40 ∧
    translatedStrictEscape = (context false input).rules 41 := ⟨rfl, rfl, rfl⟩

theorem invariant1_strict_escape_body (input : List Char) :
    translatedStrictEscapeBody = (context false input).rules 42 := rfl

theorem invariant1_strict_character_classes (input : List Char) :
    translatedStrictClassLit = (context false input).rules 43 ∧
    translatedStrictClassItem = (context false input).rules 44 ∧
    translatedStrictClassChar = (context false input).rules 45 := ⟨rfl, rfl, rfl⟩

theorem invariant1_strict_embedded_code (input : List Char) :
    translatedStrictAction = (context false input).rules 46 ∧
    translatedStrictPredCode = (context false input).rules 47 ∧
    translatedStrictActionCode = (context false input).rules 50 ∧
    translatedStrictArgCode = (context false input).rules 51 := ⟨rfl, rfl, rfl, rfl⟩

theorem invariant1_strict_haskell_brackets (input : List Char) :
    translatedStrictHsPart = (context false input).rules 52 ∧
    translatedStrictHsParen = (context false input).rules 53 ∧
    translatedStrictHsNested = (context false input).rules 54 ∧
    translatedStrictHsInner = (context false input).rules 55 := ⟨rfl, rfl, rfl, rfl⟩

theorem invariant1_strict_haskell_quotes (input : List Char) :
    translatedStrictHsString = (context false input).rules 56 ∧
    translatedStrictHsChar = (context false input).rules 57 ∧
    translatedStrictHsIdent = (context false input).rules 58 := ⟨rfl, rfl, rfl⟩

theorem invariant1_strict_call_arguments (input : List Char) :
    translatedStrictCallArgs = (context false input).rules 36 ∧
    translatedStrictArgChunks = (context false input).rules 48 ∧
    translatedStrictArgChunk = (context false input).rules 49 := ⟨rfl, rfl, rfl⟩

theorem invariant1_strict_group_alternatives (input : List Char) :
    translatedStrictGroupAlts = (context false input).rules 37 ∧
    translatedStrictMoreGroup = (context false input).rules 38 := ⟨rfl, rfl⟩

theorem invariant1_strict_template_arguments (input : List Char) :
    translatedStrictTemplateArgs = (context false input).rules 34 ∧
    translatedStrictTemplateArg = (context false input).rules 35 := ⟨rfl, rfl⟩

set_option maxRecDepth 8192 in
theorem invariant1_strict_primary (input : List Char) :
    translatedStrictPrimary = (context false input).rules 33 := rfl

set_option maxRecDepth 16384 in
theorem invariant1_strict_rule_table :
    translatedStrictTable = MetaTerminal1.environmentBodyTable := rfl

def strictContext (input : List Char) : Inputs :=
  { context false input with rules := fun i => translatedStrictTable[i]?.getD (.terminal 0) }

set_option maxRecDepth 16384 in
theorem invariant1_strict_context (input : List Char) :
    strictContext input = context false input := by
  unfold strictContext
  rw [invariant1_strict_rule_table]
  rfl

set_option maxRecDepth 16384 in
theorem invariant1_strict_recursive_file (input : List Char) (reply : Reply) :
    (∃ fuel, runFuel (strictContext input) fuel translatedStrictFile input.length {} = some reply) ↔
      FileResult false input reply := by
  rw [invariant1_strict_context, invariant1_translated_strict_run]

theorem invariant1_strict_public_acceptance (source : String)
    (format : PublicParsing.Failure → String) :
    parseFile false source format = .ok () ↔ ∃ env fuel,
      runFuel (strictContext source.toList) fuel translatedStrictFile source.toList.length {} =
        some (.ok 0 env) := by
  rw [invariant1_parseFile_entry, FileEntry.invariant1_public_entry
    (recognizeFile false source.toList).property]
  exact exists_congr fun env => (invariant1_strict_recursive_file _ (.ok 0 env)).symm

theorem invariant2_strict_public_rejection (source : String)
    (format : PublicParsing.Failure → String) :
    (∃ msg, parseFile false source format = .error [msg]) ↔ ¬ ∃ env fuel,
      runFuel (strictContext source.toList) fuel translatedStrictFile source.toList.length {} =
        some (.ok 0 env) := by
  rw [invariant2_parseFile_rejects_iff]
  exact not_congr (exists_congr fun env => (invariant1_strict_recursive_file _ (.ok 0 env)).symm)

-- A terminating translated evaluation determines the public outcome,
-- including the precise trailing-input byte offset or labelled failure.
theorem invariant1_strict_public_reply (source : String) (fuel : Nat) (reply : Reply)
    (observed : runFuel (strictContext source.toList) fuel translatedStrictFile
      source.toList.length {} = some reply)
    (format : PublicParsing.Failure → String) :
    parseFile false source format = PublicParsing.entry source.toList.utf8Encode.size
      (FileEntry.start source.toList reply) format := by
  have parsed := (invariant1_strict_recursive_file source.toList reply).mp ⟨fuel, observed⟩
  obtain ⟨_, _, unique⟩ := invariant1_file_result false source.toList
  have same := (unique _ (recognizeFile false source.toList).property).trans (unique _ parsed).symm
  rw [invariant1_parseFile_entry, same]

theorem invariant2_strict_public_terminates (source : String) :
    ∃ bound reply, (∀ limit ≥ bound,
      runFuel (strictContext source.toList) limit translatedStrictFile
        source.toList.length {} = some reply) ∧
      ∀ format, parseFile false source format = PublicParsing.entry source.toList.utf8Encode.size
        (FileEntry.start source.toList reply) format := by
  obtain ⟨reply, parsed, _⟩ := invariant1_file_result false source.toList
  obtain ⟨bound, observed⟩ := (invariant1_strict_recursive_file source.toList reply).mpr parsed
  exact ⟨bound, reply, fun _ enough => invariant1_fuel_stable _ enough observed,
    invariant1_strict_public_reply source bound reply observed⟩

theorem invariant2_strict_rejection_no_module (source : String)
    (invalid : ¬ ∃ env fuel, runFuel (strictContext source.toList) fuel translatedStrictFile
      source.toList.length {} = some (.ok 0 env))
    (format : PublicParsing.Failure → String)
    (assemble : Unit → Except Pipeline.Diagnostics G) (resolve expand : G → Except Pipeline.Diagnostics G)
    (check : G → Except Pipeline.Diagnostics Unit) (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics)
    (strip : Option (G → G)) (warnings : G → G → Pipeline.Diagnostics)
    (generate : G → Except Pipeline.Diagnostics String) :
    ∃ bound reply, (∀ limit ≥ bound, runFuel (strictContext source.toList) limit translatedStrictFile
      source.toList.length {} = some reply) ∧
      Pipeline.visible (Pipeline.pipeline ((parseFile false source format).bind assemble)
        resolve expand check notes strip warnings generate) =
        .error [format (FileEntry.incompleteCause source.toList reply)] := by
  let result := recognizeFile false source.toList
  obtain ⟨bound, observed⟩ := (invariant1_strict_recursive_file _ _).mpr result.property
  refine ⟨bound, result.val, fun _ enough => invariant1_fuel_stable _ enough observed, ?_⟩
  apply (invariant2_parseFile_pipeline_diagnostic false source _ format assemble resolve expand
    check notes strip warnings generate).2
  rintro ⟨env, accepted⟩
  exact invalid ⟨env, (invariant1_strict_recursive_file _ _).mpr accepted⟩

#print axioms invariant2_strict_rejection_no_module
#print axioms invariant2_strict_public_terminates
#print axioms invariant1_strict_public_reply

#print axioms invariant1_strict_public_acceptance
#print axioms invariant2_strict_public_rejection

theorem invariant2_translated_unterminated_block (pre xs : List Char) (env : Env)
    (missing : verbatimRest xs = []) :
    Derives (context false (pre ++ '%' :: '{' :: xs)) translatedStrictVerbatim
      (xs.length + 2) env (.throwLabel 0 "verbatim" (some "unterminated %{ block")) :=
  invariant2_unterminated_verbatim false pre xs env missing

end PegHs.MetaExecution
