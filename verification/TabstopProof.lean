import TranslatedTabstop
import AssembleValidation

namespace PegHs.TranslatedTabstop

theorem invariant2_tabstop_source (text : String) :
    positive text = BoundedDecimal.positive limit text := by
  have eqStep : step = BoundedDecimal.checkedChar limit := by
    funext acc c
    exact (BoundedDecimal.checkedChar_eq limit acc c (by decide)).symm
  unfold positive
  rw [eqStep]
  exact BoundedDecimal.invariant2_streaming_positive limit text

open AssembleValidation

-- The model's maxBound :: Int is the one the extracted source was built with.
theorem invariant2_limit_is_intMax : limit = intMax := rfl

theorem invariant2_invalid_tabstop_diagnostic (tops : List Top) (text : String)
    (first : (args (directives tops) "tabstop").head? = some text)
    (invalid : positive text = none) :
    diagnostic ⟨.invalidTabstop, text⟩ ∈ errors tops := by
  rw [invariant2_tabstop_source, invariant2_limit_is_intMax] at invalid
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  rw [first]
  have emitted : Violation.mk .invalidTabstop text ∈ emit .invalidTabstop
      (if (BoundedDecimal.positive intMax text).isNone then [text] else []) := by
    simp [invalid, emit]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

theorem invariant2_first_tabstop_error (before after : List Top) (text : String)
    (noEarlier : args (directives before) "tabstop" = []) (invalid : positive text = none) :
    let tops := before ++ Top.directive "tabstop" text :: after
    diagnostic ⟨.invalidTabstop, text⟩ ∈ errors tops := by
  apply invariant2_invalid_tabstop_diagnostic _ _ _ invalid
  unfold args directives at noEarlier ⊢
  simp [List.filterMap_append, List.filter_append, noEarlier]

#print axioms invariant2_invalid_tabstop_diagnostic
#print axioms invariant2_tabstop_source
end PegHs.TranslatedTabstop
