namespace PegHs.LineIndex

def followingStarts : Nat → List Char → List Nat
  | _, [] => []
  | offset, c :: cs =>
    let next := offset + c.utf8Size
    if c = '\n' then next :: followingStarts next cs else followingStarts next cs

def lineIndex (input : List Char) := 0 :: followingStarts 0 input

theorem mem_followingStarts (base pos : Nat) (input : List Char) :
    pos ∈ followingStarts base input ↔ ∃ pre post : List Char,
      input = pre ++ '\n' :: post ∧ pos = base + pre.utf8Encode.size + '\n'.utf8Size := by
  induction input generalizing base with
  | nil => simp [followingStarts]
  | cons c cs ih =>
    constructor
    · intro member
      have later (h : pos ∈ followingStarts (base + c.utf8Size) cs) :
          ∃ pre post : List Char, c :: cs = pre ++ '\n' :: post ∧
            pos = base + pre.utf8Encode.size + '\n'.utf8Size := by
        obtain ⟨pre, post, split, offset⟩ := (ih _).mp h
        exact ⟨c :: pre, post, by simp [split], by
          rw [List.utf8Encode_cons]; simpa [List.utf8Encode_singleton, Nat.add_assoc] using offset⟩
      by_cases lf : c = '\n'
      · subst c
        rcases List.mem_cons.mp (by simpa [followingStarts] using member) with here | tail
        · exact ⟨[], cs, rfl, by simpa using here⟩
        · exact later tail
      · exact later (by simpa [followingStarts, lf] using member)
    · rintro ⟨pre, post, split, offset⟩
      cases pre with
      | nil =>
        cases split
        simp_all [followingStarts]
      | cons x xs =>
        cases split
        have h := (ih (base + c.utf8Size)).mpr
          ⟨xs, post, rfl, by rw [List.utf8Encode_cons] at offset; simpa [List.utf8Encode_singleton, Nat.add_assoc] using offset⟩
        by_cases lf : c = '\n' <;> simp [followingStarts, lf] at h ⊢ <;> simp [h]

theorem mem_lineIndex (input : List Char) (pos : Nat) :
    pos ∈ lineIndex input ↔ pos = 0 ∨ ∃ pre post : List Char,
      input = pre ++ '\n' :: post ∧ pos = pre.utf8Encode.size + '\n'.utf8Size := by
  simp [lineIndex, mem_followingStarts]

#print axioms mem_lineIndex

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
    (ordered : ∀ i j, i ≤ j → j ≤ b → start i ≤ start j)
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
        lineOf_last_start start off a ((a + b + 1) / 2 - 1) (fun i j hij hj => ordered i j hij (by omega)) (by omega) initial
      refine ⟨lo, by omega, ok, ?_⟩
      intro j hj _
      by_cases h : j < (a + b + 1) / 2
      · exact last j hj (by omega)
      · have step := ordered ((a + b + 1) / 2) j (by omega) (by assumption)
        omega
  · exact ⟨Nat.le_refl _, bounds, initial, by omega⟩
termination_by b - a
decreasing_by all_goals omega

theorem lookup_lineIndex (input : List Char) (off : Nat) :
    let starts := lineIndex input
    let read := fun i => starts[i]?.getD 0
    let last := starts.length - 1
    let l := lineOf read off 0 last
    l ≤ last ∧ read l ≤ off ∧ ∀ j, l < j → j ≤ last → off < read j := by
  let starts := lineIndex input
  have positive : 0 < starts.length := by simp [starts, lineIndex]
  have ordered (i j : Nat) (le : i ≤ j) (hj : j ≤ starts.length - 1) :
      starts[i]?.getD 0 ≤ starts[j]?.getD 0 := by
    by_cases same : i = j
    · simp [same]
    · have hi : i < starts.length := by omega
      have hlast : j < starts.length := by omega
      have earlier := List.pairwise_iff_getElem.mp (lineIndex_ordered input)
        i j hi hlast (by omega)
      simpa [List.getElem?_eq_getElem, hi, hlast] using Nat.le_of_lt earlier
  exact (lineOf_last_start (fun i => starts[i]?.getD 0) off 0 (starts.length - 1)
    ordered (Nat.zero_le _) (by simp [starts, lineIndex])).2

#print axioms lookup_lineIndex
#print axioms lineOf_last_start
end PegHs.LineIndex
