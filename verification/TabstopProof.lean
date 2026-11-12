import TranslatedTabstop

namespace PegHs.TranslatedTabstop

theorem invariant2_tabstop_source (text : String) :
    positive text = BoundedDecimal.positive limit text := by
  have eqStep : step = BoundedDecimal.checkedChar limit := by
    funext acc c
    exact (BoundedDecimal.checkedChar_eq limit acc c (by decide)).symm
  unfold positive
  rw [eqStep]
  exact BoundedDecimal.invariant2_streaming_positive limit text

#print axioms invariant2_tabstop_source
end PegHs.TranslatedTabstop
