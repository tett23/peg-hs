import AssembleValidation
import DirectiveHex

namespace PegHs.AssembleValidation

theorem invariant2_directive_string_failure (tops : List Top) (p : Predicates)
    (name arg msg : String) (member : Top.directive name arg ∈ tops)
    (supported : name = "expect" ∨ name = "message") (nonempty : arg.isEmpty = false)
    (failed : AssembleValidationHelpers.stringArg p.validIdent name arg = .error msg) :
    diagnostic ⟨.invalidString, msg⟩ ∈ errors tops p := by
  have pair : (name, arg) ∈ directives tops :=
    List.mem_filterMap.mpr ⟨_, member, rfl⟩
  have argument : arg ∈ args (directives tops) name :=
    List.mem_map.mpr ⟨(name, arg), List.mem_filter.mpr ⟨pair, by simp⟩, rfl⟩
  have rejected : Except.error msg ∈ stringResults p (directives tops) name :=
    List.mem_filterMap.mpr ⟨arg, argument, by simp [nonempty, failed]⟩
  have both : Except.error msg ∈ stringResults p (directives tops) "expect" ++
      stringResults p (directives tops) "message" := by
    rcases supported with rfl | rfl
    · exact List.mem_append_left _ rejected
    · exact List.mem_append_right _ rejected
  have messages : msg ∈ parseFailures _ := List.mem_filterMap.mpr ⟨_, both, rfl⟩
  have emitted : Violation.mk .invalidString msg ∈ emit .invalidString _ :=
    List.mem_map.mpr ⟨_, messages, rfl⟩
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

theorem invariant2_directive_decoder_diagnostic (tops : List Top) (p : Predicates)
    (directive : String) (name gap body : List Char) (msg : String)
    (supported : directive = "expect" ∨ directive = "message")
    (member : Top.directive directive (String.ofList (name ++ gap ++ '"' :: body)) ∈ tops)
    (valid : p.validIdent (String.ofList name) = true)
    (noSpace : ∀ c ∈ name, PegVerification.ghcIsSpace c = false)
    (separator : gap ≠ []) (spaces : ∀ c ∈ gap, PegVerification.ghcIsSpace c = true)
    (failed : AssembleValidationHelpers.decodeString body = .error msg) :
    diagnostic ⟨.invalidString, msg⟩ ∈ errors tops p := by
  apply invariant2_directive_string_failure _ _ _ _ _ member supported
  · simp
  · exact AssembleValidationHelpers.invariant2_string_argument_decode_error _ _ _ _ _ _
      valid noSpace separator spaces failed

#print axioms invariant2_directive_string_failure
end PegHs.AssembleValidation
