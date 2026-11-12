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

end PegHs.ConcreteTerminal
