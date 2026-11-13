import MetaExecution
import PublicEntryProof

namespace PegHs.FileEntry
open EnvironmentEval MetaExecution PublicParsing

-- Recognition erases the list of Top values produced by Haskell actions.
noncomputable def start (input : List Char) : Reply → StartResult Unit
  | .ok rest _ => .ok (Utf8Terminals.byteOffset input (input.length - rest)) ()
  | .fail => .fail
  | .throwLabel remaining label message =>
    .throwLabel (Utf8Terminals.byteOffset input (input.length - remaining)) label message

theorem invariant1_public_entry {mode input reply} (result : FileResult mode input reply)
    (diagnostic : Failure → String) :
    entry input.utf8Encode.size (start input reply) diagnostic = .ok () ↔
      ∃ env, FileResult mode input (.ok 0 env) := by
  obtain ⟨_, _, unique⟩ := invariant1_file_result mode input
  rw [invariant1_parseTops_iff]
  constructor
  · intro h
    cases reply with
    | ok rest env =>
      obtain rfl := (invariant1_file_end_bytes result).mp (by simpa [start] using h)
      exact ⟨env, result⟩
    | fail => contradiction
    | throwLabel => contradiction
  · rintro ⟨env, accepted⟩
    have same := (unique _ result).trans (unique _ accepted).symm
    subst reply
    simp [start, Utf8Terminals.byteOffset]

theorem invariant1_translated_public_entry {mode input reply} (result : FileResult mode input reply)
    (diagnostic : Failure → String) :
    translatedPublic diagnostic (translatedRuntime input.utf8Encode.size (start input reply)) = .ok () ↔
      ∃ env, FileResult mode input (.ok 0 env) := by
  rw [invariant1_translated_entry]
  exact invariant1_public_entry result diagnostic

theorem invariant2_invalid_file_no_module {mode input reply} (result : FileResult mode input reply)
    (invalid : ¬ ∃ env, FileResult mode input (.ok 0 env))
    (diagnostic : Failure → String) {G : Type} (assemble : Unit → Except Pipeline.Diagnostics G)
    (resolve expand : G → Except Pipeline.Diagnostics G) (check : G → Except Pipeline.Diagnostics Unit)
    (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics) (strip : Option (G → G))
    (warnings : G → G → Pipeline.Diagnostics) (generate : G → Except Pipeline.Diagnostics String) :
    ∃ msg, Pipeline.visible (Pipeline.pipeline
      ((entry input.utf8Encode.size (start input reply) diagnostic).bind assemble)
      resolve expand check notes strip warnings generate) = .error [msg] := by
  cases h : entry input.utf8Encode.size (start input reply) diagnostic with
  | ok x => exact False.elim (invalid ((invariant1_public_entry result diagnostic).mp h))
  | error ds =>
    simpa only [h] using invariant2_parseFailure_no_module _ _ _ _ h assemble resolve expand
      check notes strip warnings generate

theorem invariant2_labelled_file_diagnostic {mode input reply pos label message}
    (parsed : FileResult mode input reply)
    (rejected : FileResult mode input (.throwLabel pos label message))
    (format : PublicParsing.Failure → String)
    (assemble : Unit → Except Pipeline.Diagnostics G) (resolve expand : G → Except Pipeline.Diagnostics G)
    (check : G → Except Pipeline.Diagnostics Unit) (notes : G → Pipeline.Diagnostics → Pipeline.Diagnostics)
    (strip : Option (G → G)) (warnings : G → G → Pipeline.Diagnostics)
    (generate : G → Except Pipeline.Diagnostics String) :
    let tops := PublicParsing.translatedPublic format (PublicParsing.translatedRuntime input.utf8Encode.size
      (start input reply))
    let diagnostic := [format (.labelled label message)]
    tops = .error diagnostic ∧
      Pipeline.visible (Pipeline.pipeline (tops.bind assemble) resolve expand check notes strip warnings generate) =
        .error diagnostic := by
  obtain ⟨_, _, unique⟩ := invariant1_file_result mode input
  have eq := (unique _ parsed).trans (unique _ rejected).symm
  subst reply
  exact ⟨rfl, rfl⟩

#print axioms invariant2_labelled_file_diagnostic
end PegHs.FileEntry
