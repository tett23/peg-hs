namespace PegHs.LineIndex

-- The line index stores offsets in bytes. Both bounds are inclusive.
def lineOf (start : Nat → Nat) (off a b : Nat) : Nat :=
  if a < b then
    let m := (a + b + 1) / 2
    if start m ≤ off then lineOf start off m b else lineOf start off a (m - 1)
  else a
termination_by b - a
decreasing_by all_goals omega

theorem lineOf_last_start (start : Nat → Nat) (off a b : Nat)
    (ordered : ∀ i j, i ≤ j → start i ≤ start j)
    (bounds : a ≤ b) (initial : start a ≤ off) :
    let l := lineOf start off a b
    a ≤ l ∧ l ≤ b ∧ start l ≤ off ∧ ∀ j, l < j → j ≤ b → off < start j := by
  rw [lineOf]
  split
  · rename_i narrow
    dsimp only
    split
    · rename_i before
      obtain ⟨lo, hi, ok, last⟩ :=
        lineOf_last_start start off ((a + b + 1) / 2) b ordered (by omega) before
      exact ⟨by omega, hi, ok, last⟩
    · rename_i after
      obtain ⟨lo, hi, ok, last⟩ :=
        lineOf_last_start start off a ((a + b + 1) / 2 - 1) ordered (by omega) initial
      refine ⟨lo, by omega, ok, ?_⟩
      intro j hj _
      by_cases h : j < (a + b + 1) / 2
      · exact last j hj (by omega)
      · have step := ordered ((a + b + 1) / 2) j (by omega)
        omega
  · exact ⟨Nat.le_refl _, bounds, initial, by omega⟩
termination_by b - a
decreasing_by all_goals omega

#print axioms lineOf_last_start
end PegHs.LineIndex
