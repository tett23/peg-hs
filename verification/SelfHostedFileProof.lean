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

end PegHs.MetaExecution
