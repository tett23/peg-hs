import StrictWhitespaceScan
import Whitespace
import FileEnd
import FileEntry
import TranslatedRuntimeChoice
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

theorem invariant2_whitespace_only_assembly (input : List Char)
    (consumed : PegVerification.run PegVerification.whitespaceExpr input = .ok [])
    (p : AssembleValidation.Predicates) :
    FileResult false input (.ok 0 {}) ∧
    EnvironmentEval.Derives (context false input) (.call 1 1) 0 {} .fail ∧
    AssembleValidation.parseGrammar (.ok (EnvironmentEval.translatedManyStop
      EnvironmentEval.translatedManyInitial)) p = .error ["missing %module directive"] := by
  exact ⟨invariant1_whitespace_only_file input consumed,
    invariant1_top_item_at_end false input {}, rfl⟩

#print axioms invariant2_whitespace_only_assembly
#print axioms invariant1_whitespace_only_public
#print axioms invariant1_file_initial_ws_lexical
#print axioms invariant1_strict_ws_lexical_reply
end PegHs.MetaExecution
