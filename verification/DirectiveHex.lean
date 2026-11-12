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

private theorem fold_hex_digits (ds value : List Char) (count acc : Nat)
    (allHex : ∀ c ∈ ds, (hexValue c).isSome = true) :
    ds.foldl decodeStep (.hex value count acc) =
      .hex value (count + ds.length) (ds.foldl (fun n c => n * 16 + (hexValue c).getD 0) acc) := by
  have h := invariant2_hex_prefix ds value count acc
  have parts : ds.takeWhile (fun c => (hexValue c).isSome) = ds ∧
      ds.dropWhile (fun c => (hexValue c).isSome) = [] := by
    clear h
    induction ds with
    | nil => exact ⟨rfl, rfl⟩
    | cons c cs ih =>
      have tail := ih (fun d hd => allHex d (.tail _ hd))
      simp [allHex c (.head _), tail]
  simpa [parts.1, parts.2] using h

theorem invariant2_closed_unicode_escape (ds value rest : List Char)
    (allHex : ∀ c ∈ ds, (hexValue c).isSome = true) :
    let number := ds.foldl (fun n c => n * 16 + (hexValue c).getD 0) 0
    (ds ++ '}' :: rest).foldl decodeStep (.hex value 0 0) =
      rest.foldl decodeStep (if ds.isEmpty || number > 0x10FFFF then
        .failed "invalid \\u escape" else
        .plain (value ++ [Char.ofNat (if 0xD800 ≤ number && number ≤ 0xDFFF then 0xFFFD else number)])) := by
  rw [List.foldl_append, fold_hex_digits ds value 0 0 allHex]
  have brace : hexValue '}' = none := by decide
  cases ds <;> simp [List.foldl_cons, decodeStep, brace]

private theorem failed_stays (rest : List Char) (msg : String) :
    rest.foldl decodeStep (.failed msg) = .failed msg := by
  induction rest with
  | nil => rfl
  | cons c cs ih => exact ih

theorem invariant2_unicode_missing_close (ds : List Char)
    (allHex : ∀ c ∈ ds, (hexValue c).isSome = true) :
    decodeString (['\\', 'u', '{'] ++ ds) = .error "expected '}'" := by
  unfold decodeString
  rw [List.foldl_append]
  have initial : ['\\', 'u', '{'].foldl decodeStep (.plain []) = .hex [] 0 0 := rfl
  rw [initial]
  rw [fold_hex_digits ds [] 0 0 allHex]

theorem invariant2_unicode_wrong_close (ds : List Char) (bad : Char) (rest : List Char)
    (allHex : ∀ c ∈ ds, (hexValue c).isSome = true)
    (notHex : hexValue bad = none) (notClose : bad ≠ '}') :
    decodeString (['\\', 'u', '{'] ++ ds ++ bad :: rest) = .error "expected '}'" := by
  unfold decodeString
  rw [List.foldl_append, List.foldl_append]
  have initial : ['\\', 'u', '{'].foldl decodeStep (.plain []) = .hex [] 0 0 := rfl
  rw [initial]
  rw [fold_hex_digits ds [] 0 0 allHex]
  simp [List.foldl_cons, decodeStep, notHex, notClose, failed_stays]

#print axioms invariant2_hex_prefix
end PegHs.AssembleValidationHelpers
