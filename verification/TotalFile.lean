import FileEntry

namespace PegHs.MetaExecution
open EnvironmentEval

-- Search for a successful fuel bound. The existential is used only in the
-- termination proof; each executable call tests the current approximation.
private def searchFuel {α : Type} (trial : Nat → Option α) (reachable : ∃ k, (trial k).isSome = true)
    (n : Nat) (within : n ≤ Classical.choose reachable) :
    {r : α // ∃ k, trial k = some r} :=
  match h : trial n with
  | some r => ⟨r, n, h⟩
  | none =>
    have lt : n < Classical.choose reachable := by
      have ne : n ≠ Classical.choose reachable := by
        intro eq
        have ok := Classical.choose_spec reachable
        rw [← eq, h] at ok
        contradiction
      omega
    searchFuel trial reachable (n + 1) lt
termination_by Classical.choose reachable - n
decreasing_by omega

def recognizeFile (mode : Bool) (input : List Char) : {r // FileResult mode input r} := by
  let ctx := context mode input
  let trial := fun k => runFuel ctx k (ctx.rules (startRule mode)) input.length {}
  have future : ∃ k, (trial k).isSome = true := by
    obtain ⟨r, hr, _⟩ := invariant1_file_result mode input
    obtain ⟨k, ok⟩ := invariant1_derivation_has_fuel hr
    exact ⟨k, by simpa [trial] using congrArg Option.isSome ok⟩
  let result := searchFuel trial future 0 (Nat.zero_le _)
  exact ⟨result.val, by obtain ⟨k, ok⟩ := result.property; exact invariant1_runFuel_sound ok⟩

theorem invariant1_total_public_entry (mode : Bool) (input : List Char)
    (diagnostic : PublicParsing.Failure → String) :
    PublicParsing.translatedPublic diagnostic (PublicParsing.translatedRuntime input.utf8Encode.size
      (FileEntry.start input (recognizeFile mode input).val)) = .ok () ↔
      ∃ env, FileResult mode input (.ok 0 env) :=
  FileEntry.invariant1_translated_public_entry (recognizeFile mode input).property diagnostic

#print axioms invariant1_total_public_entry
end PegHs.MetaExecution
