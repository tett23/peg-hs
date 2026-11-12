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

#print axioms invariant2_total_invalid_file
#print axioms invariant1_total_public_entry
end PegHs.MetaExecution
