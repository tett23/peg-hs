import EnvironmentEval

namespace PegHs.EnvironmentEval

theorem invariant1_capture_window (before window extra : List Char) (start rest : Nat)
    (within : start ≤ window.length) :
    matchedText (before ++ (window ++ extra)) (start + extra.length) (rest + extra.length) =
      matchedText window start rest := by
  unfold matchedText
  simp only [List.length_append, Nat.add_sub_add_right]
  have pos : before.length + (window.length + extra.length) - (start + extra.length) =
      before.length + (window.length - start) := by omega
  rw [pos, List.drop_append]
  simp only [Nat.le_add_right, List.drop_eq_nil_of_le, Nat.add_sub_cancel_left, List.nil_append]
  rw [List.drop_append]
  simp only [List.take_append, List.length_drop]
  have exactStart : window.length - (window.length - start) = start := by omega
  simp [exactStart, Nat.sub_eq_zero_of_le (show start - rest ≤ start by omega)]

end PegHs.EnvironmentEval
