import TranslatedEscapes

namespace PegHs.TranslatedEscapes
open AssembleValidationHelpers

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

#print axioms invariant2_escape_branch
#print axioms invariant2_simple_lookup
end PegHs.TranslatedEscapes
