import VerbatimRule
import TranslatedVerbatimBody
import AssembleValidationHelpers

namespace PegHs.MetaExecution

theorem invariant1_verbatim_value (file : α) (line column : Nat) (body : List Char) :
    translatedVerbatimBody file line column body =
      if body.head? = some '\n' then
        ((file, line + 1, 1), ParameterPredicates.stripEnd PegVerification.ghcIsSpace body.tail)
      else ((file, line, column), AssembleValidationHelpers.stripSpace body) := by
  cases body with
  | nil => rfl
  | cons c cs =>
    by_cases newline : c = '\n'
    · subst c; rfl
    · simp [translatedVerbatimBody, newline, AssembleValidationHelpers.stripSpace,
        ParameterPredicates.stripEnd]

theorem invariant1_parameter_location {space alpha alnum src name ty}
    (accepted : ParameterPredicates.classify space alpha alnum src = .ok name ty)
    (loc : α × Nat × Nat) :
    ∃ a b, ParameterPredicates.FirstSeparator src a b ∧
      let beforeType := a ++ [':', ':'] ++ b.takeWhile space
      let remaining := b.dropWhile space
      remaining.head?.any (fun c => !space c) = true ∧
      ParameterPredicates.stripEnd space remaining = ty ∧
      translatedAdvanceLoc (translatedAdvanceLoc loc beforeType) remaining = translatedAdvanceLoc loc src := by
  obtain ⟨a, b, split, source, first, text⟩ := ParameterPredicates.invariant1_parameter_type_start accepted
  refine ⟨a, b, split, first, text, ?_⟩
  rw [source]
  exact (List.foldl_append ..).symm

#print axioms invariant1_parameter_location
#print axioms invariant1_verbatim_value
end PegHs.MetaExecution
