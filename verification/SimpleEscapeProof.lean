import TranslatedEscapes

namespace PegHs.TranslatedEscapes
open AssembleValidationHelpers

theorem invariant2_simple_lookup (c : Char) : table.lookup c = simpleEscape c := by
  unfold simpleEscape
  split <;> first | decide | skip
  rw [List.lookup_eq_none_iff]
  simp [table]
  grind

#print axioms invariant2_simple_lookup
end PegHs.TranslatedEscapes
