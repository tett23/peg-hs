namespace PegHs.LineIndex

def followingStarts : Nat → List Char → List Nat
  | _, [] => []
  | offset, c :: cs =>
    let next := offset + c.utf8Size
    if c = '\n' then next :: followingStarts next cs else followingStarts next cs

def lineIndex (input : List Char) := 0 :: followingStarts 0 input

theorem followingStarts_ordered (offset : Nat) (input : List Char) :
    (offset :: followingStarts offset input).Pairwise (· < ·) := by
  induction input generalizing offset with
  | nil => simp [followingStarts]
  | cons c cs ih =>
    let next := offset + c.utf8Size
    have pos : 0 < c.utf8Size := by
      simp only [Char.utf8Size]; grind
    have lt : offset < next := by dsimp [next]; omega
    have rest := ih next
    have above := (List.pairwise_cons.mp rest).1
    change (offset :: (if c = '\n' then next :: followingStarts next cs else followingStarts next cs)).Pairwise _
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_, rest⟩
      intro x member
      rcases List.mem_cons.mp member with rfl | later
      · exact lt
      · exact Nat.lt_trans lt (above x later)
    · exact List.pairwise_cons.mpr ⟨fun x hx => Nat.lt_trans lt (above x hx),
        (List.pairwise_cons.mp rest).2⟩

theorem lineIndex_ordered (input : List Char) : (lineIndex input).Pairwise (· < ·) :=
  followingStarts_ordered 0 input

#print axioms lineIndex_ordered

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
