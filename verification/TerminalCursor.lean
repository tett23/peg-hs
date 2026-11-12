import ConcreteTerminal

namespace PegHs.ConcreteTerminal

-- Replaying a proof at a known input split only inspects the suffix.
theorem invariant1_oracle_suffix (term : Terminal) (before suffix : List Char) :
    terminalOracle term (before ++ suffix) suffix.length =
      (matchTerm term suffix).map List.length := by
  simp [terminalOracle, matchAt]
  cases h : matchTerm term suffix with
  | none => simp
  | some tail =>
    have matched := (invariant1_matchTerm_iff term suffix tail).mp h
    have bound : tail.length ≤ suffix.length := by cases matched <;> simp
    simp
    omega

theorem invariant1_oracle_at_cursor {term : Terminal} {source before suffix : List Char}
    (atCursor : source = before ++ suffix) {remaining : Nat}
    (atEnd : remaining = suffix.length) :
    terminalOracle term source remaining = (matchTerm term suffix).map List.length := by
  subst source remaining
  exact invariant1_oracle_suffix _ _ _

-- A short literal can fail by reaching the end of its window. Such a
-- failure is transferable only when the window already covers the literal.
def readWidth : Terminal → Nat
  | .lit pattern => pattern.length
  | .cls _ | .any => 1

private theorem literal_window (pattern window extra : List Char)
    (enough : pattern.length ≤ window.length) :
    matchLiteral pattern (window ++ extra) =
      (matchLiteral pattern window).map (· ++ extra) := by
  induction pattern generalizing window with
  | nil => simp [matchLiteral]
  | cons c cs ih =>
    cases window with
    | nil => simp at enough
    | cons x xs =>
      by_cases same : c = x
      · simp [matchLiteral, same, ih xs (by simpa using enough)]
      · simp [matchLiteral, same]

theorem invariant1_terminal_window (term : Terminal) (window extra : List Char)
    (enough : readWidth term ≤ window.length) :
    matchTerm term (window ++ extra) = (matchTerm term window).map (· ++ extra) := by
  cases term with
  | lit pattern => exact literal_window pattern window extra enough
  | any => cases window <;> simp_all [matchTerm, readWidth]
  | cls ranges =>
    cases window with
    | nil => simp [readWidth] at enough
    | cons c cs => by_cases h : classHas ranges c <;> simp [matchTerm, h]

theorem invariant1_oracle_window (term : Terminal) (before window extra : List Char)
    (enough : readWidth term ≤ window.length) :
    terminalOracle term (before ++ (window ++ extra)) (window ++ extra).length =
      (terminalOracle term window window.length).map (· + extra.length) := by
  rw [invariant1_oracle_suffix, invariant1_terminal_window term window extra enough]
  have localStep := invariant1_oracle_suffix term [] window
  simp only [List.nil_append] at localStep
  rw [localStep]
  cases matchTerm term window <;> simp

end PegHs.ConcreteTerminal
