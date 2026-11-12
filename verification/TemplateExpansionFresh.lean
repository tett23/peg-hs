import TemplateExpansion

namespace PegHs.TemplateExpansion

-- A finite set of names cannot cover an injective sequence of suffixes.
-- The Haskell caller uses base ++ "'" ++ show k, with Integer k.
theorem fresh_suffix_exists (used : List String) (candidate : Nat → String)
    (injective : Function.Injective candidate) (start : Nat) :
    ∃ k, start ≤ k ∧ candidate k ∉ used := by
  induction used generalizing start with
  | nil => exact ⟨start, Nat.le_refl _, by simp⟩
  | cons name rest ih =>
    obtain ⟨k, hk, hrest⟩ := ih start
    by_cases hit : candidate k = name
    · obtain ⟨j, hj, hrestj⟩ := ih (k + 1)
      have different : candidate j ≠ name := by
        intro eq
        have same := injective (hit.trans eq.symm)
        omega
      exact ⟨j, by omega, by simp [different, hrestj]⟩
    · exact ⟨k, hk, by simp [hit, hrest]⟩

theorem fresh_avoids_original_and_generated (original generated : List String)
    (candidate : Nat → String) (injective : Function.Injective candidate)
    (start : Nat) :
    ∃ k, start ≤ k ∧ candidate k ∉ original ∧ candidate k ∉ generated := by
  obtain ⟨k, hk, hnot⟩ := fresh_suffix_exists (original ++ generated) candidate injective start
  simp only [List.mem_append, not_or] at hnot
  exact ⟨k, hk, hnot.1, hnot.2⟩

-- The Int depth is incremented only after it was at most 64; the first
-- rejected depth is 65, far below the minimum bound of an Int64.
theorem bounded_depth_increment (depth : Nat) (h : depth ≤ 64) : depth + 1 ≤ 65 := by
  omega

#print axioms PegHs.TemplateExpansion.fresh_avoids_original_and_generated
#print axioms PegHs.TemplateExpansion.bounded_depth_increment

end PegHs.TemplateExpansion
