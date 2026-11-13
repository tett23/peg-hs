import FileEntry

namespace PegHs.MetaExecution
open EnvironmentEval

-- Search for a successful fuel bound. The existential is used only in the
-- termination proof; each executable call tests the current approximation.
private def searchFuel {α : Type} (trial : Nat → Option α) (reachable : ∃ bound, ∀ k, bound ≤ k → (trial k).isSome = true)
    (n : Nat) :
    {r : α // ∃ k, trial k = some r} :=
  match h : trial n with
  | some r => ⟨r, n, h⟩
  | none =>
    have lt : n < Classical.choose reachable := by
      apply Nat.lt_of_not_ge
      intro ge
      have ok := Classical.choose_spec reachable n ge
      simp [h] at ok
    searchFuel trial reachable (2 * n + 1)
termination_by Classical.choose reachable - n
decreasing_by omega

def recognizeFile (mode : Bool) (input : List Char) : {r // FileResult mode input r} := by
  let ctx := context mode input
  let trial := fun k => runFuel ctx k (ctx.rules (startRule mode)) input.length {}
  have future : ∃ bound, ∀ k, bound ≤ k → (trial k).isSome = true := by
    obtain ⟨r, hr, _⟩ := invariant1_file_result mode input
    obtain ⟨k, ok⟩ := invariant1_derivation_has_fuel hr
    refine ⟨k, fun limit budget => ?_⟩
    simpa [trial] using congrArg Option.isSome (invariant1_fuel_stable ctx budget ok)
  let result := searchFuel trial future 0
  exact ⟨result.val, by obtain ⟨k, ok⟩ := result.property; exact invariant1_runFuel_sound ok⟩

private def executableStart (input : List Char) : Reply → PublicParsing.StartResult Unit
  | .ok rest _ => .ok (String.ofList (input.take (input.length - rest))).utf8ByteSize ()
  | .fail => .fail
  | .throwLabel rest label msg =>
    .throwLabel (String.ofList (input.take (input.length - rest))).utf8ByteSize label msg

def parseFile (mode : Bool) (source : String) (diagnostic : PublicParsing.Failure → String) :=
  PublicParsing.translatedPublic diagnostic (PublicParsing.translatedRuntime source.utf8ByteSize
    (executableStart source.toList (recognizeFile mode source.toList).val))

theorem invariant1_parseFile_entry (mode : Bool) (source : String)
    (diagnostic : PublicParsing.Failure → String) :
    parseFile mode source diagnostic =
      PublicParsing.entry source.toList.utf8Encode.size
        (FileEntry.start source.toList (recognizeFile mode source.toList).val) diagnostic := by
  unfold parseFile
  rw [PublicParsing.invariant1_translated_entry]
  have bytes : source.utf8ByteSize = source.toList.utf8Encode.size := by simp
  rw [bytes]
  congr 1

theorem invariant2_parseFile_rejects_iff (mode : Bool) (source : String)
    (diagnostic : PublicParsing.Failure → String) :
    (∃ msg, parseFile mode source diagnostic = .error [msg]) ↔
      ¬ ∃ env, FileResult mode source.toList (.ok 0 env) := by
  rw [invariant1_parseFile_entry]
  have accepted := FileEntry.invariant1_public_entry
    (recognizeFile mode source.toList).property diagnostic
  rw [← accepted]
  cases h : PublicParsing.entry source.toList.utf8Encode.size
      (FileEntry.start source.toList (recognizeFile mode source.toList).val) diagnostic with
  | ok u => simp
  | error ds =>
    obtain ⟨msg, rfl⟩ := PublicParsing.invariant2_parseTops_singleton _ _ _ _ h
    simp

theorem invariant1_total_public_entry (mode : Bool) (input : List Char)
    (diagnostic : PublicParsing.Failure → String) :
    PublicParsing.translatedPublic diagnostic (PublicParsing.translatedRuntime input.utf8Encode.size
      (FileEntry.start input (recognizeFile mode input).val)) = .ok () ↔
      ∃ env, FileResult mode input (.ok 0 env) :=
  FileEntry.invariant1_translated_public_entry (recognizeFile mode input).property diagnostic

theorem invariant2_total_invalid_file (mode : Bool) (input : List Char)
    (invalid : ¬ ∃ env, FileResult mode input (.ok 0 env))
    (diagnostic : PublicParsing.Failure → String) {G : Type}
    (assemble : Unit → Except Pipeline.Diagnostics G)
    (resolve expand : G → Except Pipeline.Diagnostics G) (check : G → Except Pipeline.Diagnostics Unit)
    (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics) (strip : Option (G → G))
    (warnings : G → G → Pipeline.Diagnostics) (generate : G → Except Pipeline.Diagnostics String) :
    let start := FileEntry.start input (recognizeFile mode input).val
    ∃ msg, Pipeline.visible (Pipeline.pipeline
      ((PublicParsing.translatedPublic diagnostic (PublicParsing.translatedRuntime input.utf8Encode.size start)).bind assemble)
      resolve expand check notes strip warnings generate) = .error [msg] := by
  dsimp only
  rw [PublicParsing.invariant1_translated_entry]
  exact FileEntry.invariant2_invalid_file_no_module (recognizeFile mode input).property invalid
    diagnostic assemble resolve expand check notes strip warnings generate

theorem invariant2_parseFile_pipeline_diagnostic (mode : Bool) (source : String)
    (invalid : ¬ ∃ env, FileResult mode source.toList (.ok 0 env))
    (format : PublicParsing.Failure → String)
    (assemble : Unit → Except Pipeline.Diagnostics G) (resolve expand : G → Except Pipeline.Diagnostics G)
    (check : G → Except Pipeline.Diagnostics Unit) (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics)
    (strip : Option (G → G)) (warnings : G → G → Pipeline.Diagnostics)
    (generate : G → Except Pipeline.Diagnostics String) :
    let cause := FileEntry.incompleteCause source.toList (recognizeFile mode source.toList).val
    let tops := parseFile mode source format
    tops = .error [format cause] ∧
      Pipeline.visible (Pipeline.pipeline (tops.bind assemble) resolve expand check notes strip warnings generate) =
        .error [format cause] := by
  have result := FileEntry.invariant2_incomplete_file_diagnostic (recognizeFile mode source.toList).property
    invalid format assemble resolve expand check notes strip warnings generate
  dsimp only at result ⊢
  rw [invariant1_parseFile_entry]
  rw [PublicParsing.invariant1_translated_entry] at result
  exact result

theorem invariant1_generated_module_requires_complete_parse (mode : Bool) (source moduleText : String)
    (format : PublicParsing.Failure → String)
    (assemble : Unit → Except Pipeline.Diagnostics G) (resolve expand : G → Except Pipeline.Diagnostics G)
    (check : G → Except Pipeline.Diagnostics Unit) (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics)
    (strip : Option (G → G)) (warnings : G → G → Pipeline.Diagnostics)
    (generate : G → Except Pipeline.Diagnostics String)
    (generated : Pipeline.visible (Pipeline.pipeline ((parseFile mode source format).bind assemble)
      resolve expand check notes strip warnings generate) = .ok moduleText) :
    ∃ env, FileResult mode source.toList (.ok 0 env) := by
  apply Classical.byContradiction
  intro invalid
  have rejected := (invariant2_parseFile_pipeline_diagnostic mode source invalid format assemble
    resolve expand check notes strip warnings generate).2
  rw [generated] at rejected
  contradiction

#print axioms invariant1_generated_module_requires_complete_parse
#print axioms invariant2_parseFile_pipeline_diagnostic
#print axioms invariant2_total_invalid_file
#print axioms invariant1_total_public_entry
end PegHs.MetaExecution
