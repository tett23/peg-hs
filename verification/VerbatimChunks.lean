import VerbatimRule

namespace PegHs.MetaExecution

-- The final character must differ from '}' so a closing delimiter cannot
-- straddle the next chunk boundary.
def safeChunk : List Char → Bool
  | [] => true
  | [c] => c != '}'
  | c :: d :: rest => !(c == '}' && d == '%') && safeChunk (d :: rest)

theorem invariant1_safe_chunk (chunk tail : List Char)
    (safe : safeChunk chunk = true) :
    verbatimRest (chunk ++ tail) = verbatimRest tail := by
  induction chunk generalizing tail with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil =>
      simp only [safeChunk, bne_iff_ne] at safe
      cases tail with
      | nil => simp [verbatimRest, verbatimEnd]
      | cons d rest =>
        simp [verbatimRest, verbatimEnd, safe]
    | cons d rest =>
      have both := Bool.and_eq_true_iff.mp safe
      have first : verbatimEnd (c :: d :: rest) = false := by
        cases hc : c == '}' <;> cases hd : d == '%' <;>
          simp_all [verbatimEnd, safeChunk]
      have next : safeChunk (d :: rest) = true := both.2
      have same : verbatimEnd (c :: d :: (rest ++ tail)) = false := by
        simpa [verbatimEnd] using first
      change verbatimRest (c :: d :: (rest ++ tail)) = _
      rw [verbatimRest]
      simp only [same, Bool.false_eq_true, ite_false]
      exact ih tail next

#print axioms invariant1_safe_chunk

end PegHs.MetaExecution
