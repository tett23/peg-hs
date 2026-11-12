import AssembleValidationHelpers

namespace PegHs.AssembleValidationHelpers

-- The Haskell unicode branch consumes span isHexDigit and folds the decoded digits.
theorem invariant2_hex_prefix (cs value : List Char) (digits number : Nat) :
    let run := cs.takeWhile (fun c => (hexValue c).isSome)
    let tail := cs.dropWhile (fun c => (hexValue c).isSome)
    cs.foldl decodeStep (.hex value digits number) =
      tail.foldl decodeStep (.hex value (digits + run.length)
        (run.foldl (fun n c => n * 16 + (hexValue c).getD 0) number)) := by
  induction cs generalizing digits number with
  | nil => simp
  | cons c cs ih =>
    cases h : hexValue c with
    | none => simp [h]
    | some d =>
      simp [h, decodeStep, List.foldl_cons, ih, Nat.add_assoc, Nat.add_comm]

theorem invariant2_hex_digit_range (c : Char) (d : Nat) (h : hexValue c = some d) :
    d < 16 := by
  simp only [hexValue, Bool.and_eq_true, decide_eq_true_eq] at h
  split at h <;> simp_all <;> first | omega | split at h
  all_goals simp_all <;> first | omega | split at h
  all_goals simp_all <;> omega

#print axioms invariant2_hex_prefix
end PegHs.AssembleValidationHelpers
