import TranslatedEscapes
import EscapePredicates
import DirectiveHex

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

theorem invariant2_unicode_packed_value {ds : List Char} {n : Nat}
    (digits : EscapePredicates.HexValue ds n) (nonempty : ds ≠ []) (within : n ≤ maximumCode)
    (value rest : List Char) :
    (ds ++ '}' :: rest).foldl decodeStep (.hex value 0 0) =
      rest.foldl decodeStep (.plain (value ++ [packedChr n])) := by
  have allHex : ∀ c ∈ ds, (hexValue c).isSome = true := by
    clear nonempty within
    induction digits with
    | empty => simp
    | cons hd _ ih =>
      intro c h
      rcases List.mem_cons.mp h with rfl | h
      · rw [← invariant2_hex_lookup, hexDigit_parser, hd]; rfl
      · exact ih c h
  have num := invariant2_hex_positional digits 0
  simp only [Nat.zero_mul, Nat.zero_add] at num
  simp only [invariant2_hex_lookup] at num
  have close := invariant2_closed_unicode_escape ds value rest allHex
  change n ≤ 0x10FFFF at within
  simpa [num, nonempty, Nat.not_lt_of_ge within, packedChr] using close

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

private theorem finishFailed (msg : String) (rest : List Char) :
    finishDecode (rest.foldl decodeStep (.failed msg)) = .error msg := by
  induction rest with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem invariant2_unicode_branch (acc input : List Char) :
    unicode (fun rev rest => finishDecode (rest.foldl decodeStep (.plain rev.reverse))) acc input =
      finishDecode (input.foldl decodeStep (.brace acc.reverse)) := by
  cases input with
  | nil => rfl
  | cons c rest =>
    by_cases openBrace : c = '{'
    · subst c
      simp only [unicode, invariant2_hex_lookup, List.foldl_cons, decodeStep, beq_self_eq_true, ite_true]
      rw [invariant2_hex_prefix]
      have stop := List.head?_dropWhile_not (fun c => (hexValue c).isSome) rest
      cases h : rest.dropWhile (fun c => (hexValue c).isSome) with
      | nil => rfl
      | cons last more =>
        rw [h] at stop
        have noDigit : hexValue last = none := by simpa using stop
        by_cases close : last = '}'
        · subst last
          by_cases empty : rest.takeWhile (fun c => (hexValue c).isSome) = []
          all_goals by_cases ok : (rest.takeWhile (fun c => (hexValue c).isSome)).foldl (fun m d => m * 16 + (hexValue d).getD 0) 0 ≤ 0x10FFFF
          all_goals simp_all [List.foldl_cons, decodeStep, packedChr, finishFailed,
            Nat.not_lt_of_ge] <;> intro impossible <;> exact False.elim ((Nat.not_le_of_gt ok) (of_decide_eq_true impossible))
        · simp [close, List.foldl_cons, decodeStep, noDigit, finishFailed]
    · simp [unicode, openBrace, List.foldl_cons, decodeStep, finishFailed]

#print axioms invariant2_unicode_branch
#print axioms invariant2_plain_branch
#print axioms invariant2_escape_branch
#print axioms invariant2_simple_lookup
end PegHs.TranslatedEscapes
