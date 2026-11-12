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

theorem invariant2_invalid_tabstop_diagnostic (tops : List Top) (p : Predicates) (text : String)
    (first : (args (directives tops) "tabstop").head? = some text)
    (invalid : positive text = none) :
    let target := { p with intMax := limit }
    diagnostic ⟨.invalidTabstop, text⟩ ∈ errors tops target := by
  rw [invariant2_tabstop_source] at invalid
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  rw [first]
  have emitted : Violation.mk .invalidTabstop text ∈ emit .invalidTabstop
      (if (BoundedDecimal.positive limit text).isNone then [text] else []) := by
    simp [invalid, emit]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

theorem invariant2_first_tabstop_error (before after : List Top) (p : Predicates) (text : String)
    (noEarlier : args (directives before) "tabstop" = []) (invalid : positive text = none) :
    let tops := before ++ Top.directive "tabstop" text :: after
    diagnostic ⟨.invalidTabstop, text⟩ ∈ errors tops {p with intMax := limit} := by
  apply invariant2_invalid_tabstop_diagnostic _ _ _ _ invalid
  unfold args directives at noEarlier ⊢
  simp [List.filterMap_append, List.filter_append, noEarlier]

#print axioms invariant2_invalid_tabstop_diagnostic
#print axioms invariant2_tabstop_source
end PegHs.TranslatedTabstop
