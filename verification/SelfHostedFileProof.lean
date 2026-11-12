import TranslatedStrictFile
import FileEntry

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

end PegHs.MetaExecution
