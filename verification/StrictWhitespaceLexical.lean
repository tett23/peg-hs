import StrictWhitespaceScan
import Whitespace
import FileEnd
import FileEntry
import RuntimeChoiceProof
import AssembleValidation

namespace PegHs.MetaExecution

private theorem sameSpace (c : Char) : GhcPredicates.space c = PegVerification.ghcIsSpace c := by
  apply Bool.eq_iff_iff.mpr
  change (_ = true) ↔ PegVerification.ghcSpaceChars.contains c = true
  rw [List.contains_iff_mem]
  have mem : c ∈ PegVerification.ghcSpaceChars ↔ c.toNat ∈ PegVerification.ghcSpaceChars.map Char.toNat := by
    simp [List.mem_map, Char.toNat_inj]
  rw [mem]
  change (GhcPredicates.spaceRanges.any _ = true) ↔ c.toNat ∈
    [9,10,11,12,13,32,160,5760,8192,8193,8194,8195,8196,8197,8198,8199,8200,8201,8202,8239,8287,12288]
  simp [GhcPredicates.spaceRanges]
  omega

private theorem sameRemainder (fuel : Nat) (xs : List Char) (enough : xs.length < fuel) :
    PegVerification.wsDrop PegVerification.ghcIsSpace fuel xs = afterWhitespace xs := by
  induction fuel generalizing xs with
  | zero => omega
  | succ fuel ih =>
    cases xs with
    | nil => simp [PegVerification.wsDrop, afterWhitespace]
    | cons c cs =>
      simp only [List.length_cons] at enough
      rw [afterWhitespace, PegVerification.wsDrop, sameSpace]
      by_cases space : PegVerification.ghcIsSpace c = true
      · simpa [space] using ih cs (by omega)
      · by_cases hash : c = '#'
        · subst c
          have shorter := (List.dropWhile_suffix PegVerification.beforeNewline (l := cs)).length_le
          simp only [space, beq_self_eq_true, ite_true]
          rw [show (fun x : Char => x != '\n') = PegVerification.beforeNewline by funext x; rfl]
          exact
            ih (cs.dropWhile PegVerification.beforeNewline) (by omega)
        · simp [space, hash]

theorem afterWhitespace_suffix (xs : List Char) : (afterWhitespace xs).IsSuffix xs := by
  rw [← sameRemainder (xs.length + 1) xs (by omega)]
  exact PegVerification.invariant1_ws_suffix _ _ _

theorem invariant1_strict_ws_lexical_reply (pre xs : List Char) (env : EnvironmentEval.Env) :
    ∃ suffix, PegVerification.run PegVerification.whitespaceExpr xs = .ok suffix ∧
      EnvironmentEval.Derives (context false (pre ++ xs)) translatedStrictWs xs.length env
        (.ok suffix.length {env with resultDepth := 0}) := by
  refine ⟨afterWhitespace xs, ?_, invariant1_strict_whitespace_scan pre xs env⟩
  rw [PegVerification.invariant1_ws_expr, sameRemainder _ _ (by omega)]

-- File calls Ws before trying any top-level item. This establishes its
-- first runtime cursor for any source, including empty and comment-only files.
set_option maxRecDepth 8192 in
theorem invariant1_file_initial_ws_lexical (input : List Char) :
    ∃ suffix, PegVerification.run PegVerification.whitespaceExpr input = .ok suffix ∧
      EnvironmentEval.Derives (context false input) (.call 0 4) input.length {}
        (.ok suffix.length {}) := by
  obtain ⟨suffix, lexical, parsed⟩ := invariant1_strict_ws_lexical_reply [] input {}
  simp only [List.nil_append] at parsed
  let ctx := context false input
  have entered : ctx.hooks.enterCall 0 {} = some {} := rfl
  exact ⟨suffix, lexical, EnvironmentEval.Derives.call (ctx := ctx) (rule := 4) entered parsed⟩

theorem invariant1_whitespace_only_file (input : List Char)
    (consumed : PegVerification.run PegVerification.whitespaceExpr input = .ok []) :
    FileResult false input (.ok 0 {}) := by
  obtain ⟨suffix, lexical, ws⟩ := invariant1_file_initial_ws_lexical input
  rw [consumed] at lexical
  cases lexical
  exact invariant1_file_from_top_items false input ws
    (invariant1_top_items_end false input {}) (invariant1_eof_terminal _ _)

theorem invariant1_whitespace_only_public (input : List Char)
    (consumed : PegVerification.run PegVerification.whitespaceExpr input = .ok [])
    (diagnostic : PublicParsing.Failure → String) :
    PublicParsing.translatedPublic diagnostic (PublicParsing.translatedRuntime input.utf8Encode.size
      (FileEntry.start input (.ok 0 {}))) = .ok () := by
  have parsed := invariant1_whitespace_only_file input consumed
  exact (FileEntry.invariant1_translated_public_entry parsed diagnostic).2 ⟨{}, parsed⟩

theorem invariant1_file_return_values (items : List α) :
    translatedFileReturn (EnvironmentEval.translatedManyStop
      (items.foldl EnvironmentEval.translatedManyPush EnvironmentEval.translatedManyInitial)) = items :=
  EnvironmentEval.invariant1_runtime_many_values items

theorem invariant2_file_missing_module {L G} (input : List Char)
    (items : List (PublicParsing.AssemblyItem L)) (diagnostic : PublicParsing.Failure → String)
    (build : (L × String) → G) (sortErrors : List String → List String)
    (absent : ∀ l n al a, PublicParsing.AssemblyItem.directive l n al a ∈ items →
      n ≠ "library" ∧ n ≠ "module") :
    let values := translatedFileReturn (EnvironmentEval.translatedManyStop
      (items.foldl EnvironmentEval.translatedManyPush EnvironmentEval.translatedManyInitial))
    PublicParsing.translatedGrammar input.utf8Encode.size (.ok input.utf8Encode.size values)
      diagnostic (fun ts =>
        let ds := PublicParsing.translatedDirectives ts
        PublicParsing.translatedAssemble [] (PublicParsing.translatedModuleName
          (PublicParsing.translatedLibraryLoc ds) (PublicParsing.translatedSingle ds))
          build "missing %module directive" sortErrors) = .error ["missing %module directive"] := by
  dsimp only
  rw [invariant1_file_return_values]
  have missing := (PublicParsing.invariant2_missing_module_items items).2 absent
  simp [PublicParsing.translatedGrammar, PublicParsing.translatedRuntime,
    PublicParsing.translatedPublic, Except.bind, missing, PublicParsing.translatedAssemble]

#print axioms invariant2_file_missing_module

theorem invariant2_whitespace_only_assembly (input : List Char)
    (consumed : PegVerification.run PegVerification.whitespaceExpr input = .ok [])
    (p : AssembleValidation.Predicates) :
    FileResult false input (.ok 0 {}) ∧
    EnvironmentEval.Derives (context false input) (.call 1 1) 0 {} .fail ∧
    AssembleValidation.parseGrammar (.ok (translatedFileReturn (EnvironmentEval.translatedManyStop
      EnvironmentEval.translatedManyInitial))) p = .error ["missing %module directive"] := by
  exact ⟨invariant1_whitespace_only_file input consumed,
    invariant1_top_item_at_end false input {}, rfl⟩

-- After the item actions have supplied their values, both public wrappers
-- preserve the list, and an assembly diagnostic survives all later stages.
theorem invariant2_file_values_rejected (input : List Char) (items : List AssembleValidation.Top)
    (p : AssembleValidation.Predicates) (diagnostic : PublicParsing.Failure → String)
    (ds : Pipeline.Diagnostics) (rejected : AssembleValidation.assemble items p = .error ds)
    (resolve expand check : Unit → Except Pipeline.Diagnostics Unit)
    (notes : Unit → Pipeline.Diagnostics → Pipeline.Diagnostics) (strip : Option (Unit → Unit))
    (warnings : Unit → Unit → Pipeline.Diagnostics) (generate : Unit → Except Pipeline.Diagnostics String) :
    let values := translatedFileReturn (EnvironmentEval.translatedManyStop
      (items.foldl EnvironmentEval.translatedManyPush EnvironmentEval.translatedManyInitial))
    let tops := PublicParsing.translatedPublic diagnostic (PublicParsing.translatedRuntime input.utf8Encode.size
      (.ok input.utf8Encode.size values))
    Pipeline.visible (Pipeline.pipeline (AssembleValidation.parseGrammar tops p)
      resolve expand check notes strip warnings generate) = .error ds ∧ ds ≠ [] := by
  dsimp only
  rw [invariant1_file_return_values, PublicParsing.invariant1_translated_entry]
  simpa [PublicParsing.entry] using AssembleValidation.public_assemble_failure items p ds rejected
    resolve expand check notes strip warnings generate

#print axioms invariant2_file_values_rejected
#print axioms invariant2_whitespace_only_assembly
#print axioms invariant1_whitespace_only_public
#print axioms invariant1_file_initial_ws_lexical
#print axioms invariant1_strict_ws_lexical_reply
end PegHs.MetaExecution
