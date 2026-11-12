import TranslatedEntry

namespace PegHs.PublicParsing

-- The start-rule result and the diagnostic formatter are the two inputs here.
-- The runtime position is measured in UTF-8 bytes, as is ctxLen.
theorem invariant1_translated_entry {T} (bytes : Nat) (r : StartResult T)
    (d : Failure → String) :
    translatedPublic d (translatedRuntime bytes r) = entry bytes r d := by
  cases r with
  | ok j x => by_cases endPos : j = bytes <;> simp [translatedRuntime, translatedPublic, entry, endPos]
  | fail => rfl
  | throwLabel => rfl

#print axioms invariant1_translated_entry
end PegHs.PublicParsing
