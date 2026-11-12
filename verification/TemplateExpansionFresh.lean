import TemplateExpansion

namespace PegHs.TemplateExpansion

-- The nonnegative part of Haskell's base <> "'" <> show (k :: Integer).
def decimalName (base : String) (k : Nat) : String :=
  base ++ "'" ++ Nat.repr k

theorem decimalName_injective (base : String) : Function.Injective (decimalName base) := by
  intro a b eq
  apply Nat.repr_injective
  have h : Nat.repr a = Nat.repr b := by
    exact (String.append_right_inj (base ++ "'")).mp (by
      simpa only [decimalName, String.append_assoc] using eq)
  exact h

theorem decimal_range_nodup (base : String) (start count : Nat) :
    ((List.range' start count).map (decimalName base)).Nodup := by
  induction count generalizing start with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.map_cons, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨j, hj, eq⟩ := List.mem_map.mp member
      have lower : start + 1 ≤ j := by
        rw [List.mem_range'] at hj
        obtain ⟨i, _, heq⟩ := hj
        omega
      have same := decimalName_injective base eq.symm
      omega
    · exact ih (start + 1)

-- At most one of the first `used.length + 1` distinct decimal candidates
-- can be occupied by each used name.
theorem decimal_fresh_within (base : String) (used : List String) (start : Nat) :
    ∃ k, start ≤ k ∧ k ≤ start + used.length ∧ decimalName base k ∉ used := by
  let candidates := (List.range' start (used.length + 1)).map (decimalName base)
  classical
  by_cases present : ∃ k, start ≤ k ∧ k ≤ start + used.length ∧ decimalName base k ∉ used
  · exact present
  have absent := present
  have allUsed : candidates ⊆ used := by
    intro name member
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp member
    by_cases occupied : decimalName base k ∈ used
    · exact occupied
    · exfalso
      apply absent
      refine ⟨k, ?_, ?_, occupied⟩
      · rw [List.mem_range'] at hk
        obtain ⟨i, hi, heq⟩ := hk
        omega
      · rw [List.mem_range'] at hk
        obtain ⟨i, hi, heq⟩ := hk
        omega
  have bound := (decimal_range_nodup base start (used.length + 1)).length_le_of_subset allUsed
  simp only [List.length_map, List.length_range'] at bound
  exfalso
  omega

theorem fresh_avoids_original_and_generated (base : String)
    (original generated : List String) (start : Nat) :
    ∃ k, start ≤ k ∧ k ≤ start + original.length + generated.length ∧
      decimalName base k ∉ original ∧ decimalName base k ∉ generated := by
  obtain ⟨k, lower, upper, free⟩ := decimal_fresh_within base (original ++ generated) start
  simp only [List.mem_append, not_or] at free
  exact ⟨k, lower, by simpa [List.length_append, Nat.add_assoc] using upper,
    free.1, free.2⟩

-- The finite prefix has `original.length + generated.length + 1` trials.
def boundedSearch (base : String) (original generated : List String)
    (start : Nat) : Option Nat :=
  (List.range' start (original.length + generated.length + 1)).find? fun k =>
    !(original.contains (decimalName base k) || generated.contains (decimalName base k))

theorem boundedSearch_succeeds (base : String) (original generated : List String)
    (start : Nat) : ∃ k, boundedSearch base original generated start = some k := by
  obtain ⟨k, lower, upper, freeOriginal, freeGenerated⟩ :=
    fresh_avoids_original_and_generated base original generated start
  have member : k ∈ List.range' start (original.length + generated.length + 1) := by
    rw [List.mem_range']
    exact ⟨k - start, by omega, by omega⟩
  have success : (boundedSearch base original generated start).isSome = true := by
    apply List.find?_isSome.mpr
    refine ⟨k, member, ?_⟩
    simp [freeOriginal, freeGenerated]
  cases h : boundedSearch base original generated start with
  | none => simp [h] at success
  | some found => exact ⟨found, rfl⟩

theorem boundedSearch_first (base : String) (original generated : List String)
    (start k : Nat) (found : boundedSearch base original generated start = some k) :
    start ≤ k ∧ k ≤ start + original.length + generated.length ∧
    decimalName base k ∉ original ∧ decimalName base k ∉ generated ∧
    (∀ j, start ≤ j → j < k →
      decimalName base j ∈ original ∨ decimalName base j ∈ generated) := by
  have details := (List.find?_range'_eq_some.mp found)
  obtain ⟨free, member, earlier⟩ := details
  have lower : start ≤ k := by
    rw [List.mem_range'] at member
    obtain ⟨i, _, eq⟩ := member
    omega
  have upper : k ≤ start + original.length + generated.length := by
    rw [List.mem_range'] at member
    obtain ⟨i, hi, eq⟩ := member
    omega
  have freeBoth : decimalName base k ∉ original ∧ decimalName base k ∉ generated := by
    simp at free
    exact free
  refine ⟨lower, upper, freeBoth.1, freeBoth.2, ?_⟩
  intro j hj hjk
  have occupied := earlier j hj hjk
  simp at occupied
  exact occupied

-- The Int depth is incremented only after it was at most 64; the first
-- rejected depth is 65, far below the minimum bound of an Int64.
theorem bounded_depth_increment (depth : Nat) (h : depth ≤ 64) : depth + 1 ≤ 65 := by
  omega

#print axioms PegHs.TemplateExpansion.decimalName_injective
#print axioms PegHs.TemplateExpansion.fresh_avoids_original_and_generated
#print axioms PegHs.TemplateExpansion.boundedSearch_succeeds
#print axioms PegHs.TemplateExpansion.boundedSearch_first

end PegHs.TemplateExpansion
