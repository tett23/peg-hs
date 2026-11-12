import TranslatedEscapes
import EscapePredicates

namespace PegHs.TranslatedEscapes
open AssembleValidationHelpers

theorem invariant2_hex_lookup (c : Char) : hexDigit c = hexValue c := rfl

theorem hexDigit_parser (c : Char) : hexDigit c = EscapePredicates.digit c := by
  simp [hexDigit, EscapePredicates.digit]

theorem invariant2_hex_positional {cs : List Char} {n : Nat}
    (digits : EscapePredicates.HexValue cs n) (acc : Nat) :
    cs.foldl (fun a c => a * 16 + (hexDigit c).getD 0) acc = acc * 16 ^ cs.length + n := by
  induction digits generalizing acc with
  | empty => simp
  | cons digit _ ih =>
    simp only [List.foldl_cons, hexDigit_parser, digit, Option.getD_some]
    simpa [hexDigit_parser, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.add_assoc] using ih (acc * 16 + _)

theorem invariant2_simple_lookup (c : Char) : table.lookup c = simpleEscape c := by
  unfold simpleEscape
  split <;> first | decide | skip
  rw [List.lookup_eq_none_iff]
  simp [table]
  grind

theorem invariant2_escape_branch (acc input : List Char) :
    escape
      (fun rev rest => finishDecode (rest.foldl decodeStep (.plain rev.reverse)))
      (fun rev rest => finishDecode (rest.foldl decodeStep (.brace rev.reverse)))
      acc input = finishDecode (input.foldl decodeStep (.escaped acc.reverse)) := by
  cases input with
  | nil => rfl
  | cons c rest =>
    by_cases u : c = 'u'
    · subst c; rfl
    · simp only [escape, invariant2_simple_lookup, List.foldl_cons, decodeStep,
        beq_eq_false_iff_ne.mpr u, Bool.false_eq_true, ite_false]
      cases h : simpleEscape c with
      | some d => simp [List.reverse_cons]
      | none =>
        have stuck (msg : String) : rest.foldl decodeStep (.failed msg) = .failed msg := by
          induction rest with
          | nil => rfl
          | cons _ _ ih => exact ih
        simp [stuck, finishDecode]

theorem invariant2_plain_branch (acc input : List Char) :
    plain
      (fun rev rest => finishDecode (rest.foldl decodeStep (.plain rev.reverse)))
      (fun rev rest => finishDecode (rest.foldl decodeStep (.escaped rev.reverse)))
      acc input = finishDecode (input.foldl decodeStep (.plain acc.reverse)) := by
  cases input with
  | nil => rfl
  | cons c rest =>
    by_cases quote : c = '"'
    · subst c
      have done (tail : List Char) :
          rest.foldl decodeStep (.done acc.reverse tail) = .done acc.reverse (tail ++ rest) := by
        induction rest generalizing tail with
        | nil => simp
        | cons x xs ih => simpa [List.foldl_cons, decodeStep, List.append_assoc] using ih (tail ++ [x])
      simp [plain, decodeStep, List.foldl_cons, done, finishDecode]
    · by_cases slash : c = '\\'
      · subst c; rfl
      · simp [plain, quote, slash, List.foldl_cons, decodeStep]

#print axioms invariant2_plain_branch
#print axioms invariant2_escape_branch
#print axioms invariant2_simple_lookup
end PegHs.TranslatedEscapes
