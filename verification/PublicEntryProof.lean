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

theorem invariant1_translated_grammar_assembled {T M G} (bytes : Nat) (start : StartResult T)
    (d : Failure → String) (errors : T → List String) (name : T → Option M)
    (build : T → M → G) (missing : String) (sortErrors : List String → List String) (g : G) :
    translatedGrammar bytes start d (fun t =>
      translatedAssemble (errors t) (name t) (build t) missing sortErrors) = .ok g ↔
      ∃ t m, start = .ok bytes t ∧ errors t = [] ∧ name t = some m ∧ build t m = g := by
  rw [invariant1_translated_grammar]
  constructor
  · rintro ⟨t, hs, ha⟩
    cases he : errors t with
    | cons e es => simp [translatedAssemble, he] at ha
    | nil =>
      cases hn : name t with
      | none => simp [translatedAssemble, he, hn] at ha
      | some m => exact ⟨t, m, hs, he, hn, by simpa [translatedAssemble, he, hn] using ha⟩
  · rintro ⟨t, m, hs, he, hn, rfl⟩
    exact ⟨t, hs, by simp [translatedAssemble, he, hn]⟩

theorem invariant2_assembly_diagnostics {T M G} (bytes : Nat) (tops : T) (d : Failure → String)
    (errors : List String) (name : Option M) (build : M → G) (missing : String)
    (sortErrors : List String → List String) (ds : List String) :
    translatedGrammar bytes (.ok bytes tops) d (fun _ =>
      translatedAssemble errors name build missing sortErrors) = .error ds ↔
      (errors = [] ∧ name = none ∧ ds = [missing]) ∨
      (errors ≠ [] ∧ ds = sortErrors errors) := by
  cases errors <;> cases name <;>
    simp [translatedGrammar, translatedRuntime, translatedPublic, translatedAssemble, Except.bind,
      eq_comm]

#print axioms invariant2_assembly_diagnostics
#print axioms invariant1_translated_grammar_assembled
#print axioms invariant1_translated_grammar
#print axioms invariant1_translated_entry
end PegHs.PublicParsing
