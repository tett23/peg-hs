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

#print axioms invariant1_verbatim_value
end PegHs.MetaExecution
