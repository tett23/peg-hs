import Std

namespace PegHs.Guard

-- Haskell Char admits all values from U+0000 to U+10FFFF, including
-- surrogates. A list of Nat code points covers that domain.
private def translatedIsControlChar (n : Nat) : Bool :=
  n < 0x20 || n == 0x7f

private def forbiddenCodepoint (n : Nat) : Prop :=
  n < 0x20 ∨ n = 0x7f

private def translatedHasControl (name : List Nat) : Bool :=
  name.any translatedIsControlChar

private def rejectFileNames (source output : List Nat) : Bool :=
  [source, output].any translatedHasControl

private def fileNameDiagnostic (source output : List Nat) : Option String :=
  if rejectFileNames source output then
    some "the file name contains a control character"
  else
    none

private theorem translatedIsControlChar_iff (n : Nat) :
    translatedIsControlChar n = true ↔ forbiddenCodepoint n := by
  simp [translatedIsControlChar, forbiddenCodepoint]

private theorem translatedHasControl_iff (name : List Nat) :
    translatedHasControl name = true ↔
      ∃ n ∈ name, forbiddenCodepoint n := by
  simp [translatedHasControl, List.any_eq_true, translatedIsControlChar_iff]

theorem invariant2_fileNameDiagnostic_iff (source output : List Nat) :
    fileNameDiagnostic source output =
      some "the file name contains a control character" ↔
    (∃ n ∈ source, forbiddenCodepoint n) ∨
    (∃ n ∈ output, forbiddenCodepoint n) := by
  by_cases hs : translatedHasControl source = true
  · simp [fileNameDiagnostic, rejectFileNames, hs,
      (translatedHasControl_iff source).mp hs]
  · by_cases ho : translatedHasControl output = true
    · simp [fileNameDiagnostic, rejectFileNames, hs, ho,
        (translatedHasControl_iff output).mp ho]
    · have ns : ¬ ∃ n ∈ source, forbiddenCodepoint n :=
        fun h => hs ((translatedHasControl_iff source).mpr h)
      have no : ¬ ∃ n ∈ output, forbiddenCodepoint n :=
        fun h => ho ((translatedHasControl_iff output).mpr h)
      simp [fileNameDiagnostic, rejectFileNames, hs, ho, ns, no]

-- Invariant 2: both source and output names reject the two boundary
-- control code points. Surrogates remain representable and permitted.
example : fileNameDiagnostic [0x00] [] = some "the file name contains a control character" := by decide
example : fileNameDiagnostic [] [0x1f] = some "the file name contains a control character" := by decide
example : fileNameDiagnostic [0x7f] [] = some "the file name contains a control character" := by decide
example : fileNameDiagnostic [0x20] [0xd800, 0xdfff] = none := by decide
example : fileNameDiagnostic [0x10ffff] [] = none := by decide

end PegHs.Guard

#print axioms PegHs.Guard.invariant2_fileNameDiagnostic_iff
