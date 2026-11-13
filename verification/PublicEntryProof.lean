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

theorem invariant1_translated_grammar {T G} (bytes : Nat) (start : StartResult T)
    (d : Failure → String) (assemble : T → Except PegHs.Pipeline.Diagnostics G) (g : G) :
    translatedGrammar bytes start d assemble = .ok g ↔
      ∃ tops, start = .ok bytes tops ∧ assemble tops = .ok g := by
  unfold translatedGrammar
  rw [invariant1_translated_entry]
  cases start with
  | ok pos tops =>
    by_cases full : pos = bytes <;> simp [entry, full, Except.bind]
  | fail => simp [entry, Except.bind]
  | throwLabel => simp [entry, Except.bind]

#print axioms invariant1_translated_grammar
#print axioms invariant1_translated_entry
end PegHs.PublicParsing
