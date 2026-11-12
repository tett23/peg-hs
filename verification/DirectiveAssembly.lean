import DirectiveSuccess
import DirectiveArgument
import AssembleValidation

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal AssembleValidation

-- Both binders use remaining-input lengths, as in the generated Directive rule.
def capturedDirective (input : List Char) (nameStart nameEnd rawStart rawEnd : Nat) : Top :=
  let name := String.ofList (matchedText input nameStart nameEnd)
  let raw := matchedText input rawStart rawEnd
  .directive name (String.ofList (DirectiveArgument.argument name raw))

theorem directiveRawCapture (pre arg : List Char) :
    matchedText (pre ++ arg) arg.length (arg.dropWhile (· != '\n')).length =
      arg.takeWhile (· != '\n') := by
  let body := arg.takeWhile (· != '\n')
  let rest := arg.dropWhile (· != '\n')
  have parts : body ++ rest = arg := List.takeWhile_append_dropWhile
  have lengths := congrArg List.length parts
  simp only [List.length_append] at lengths
  have width : arg.length - rest.length = body.length := by omega
  change ((pre ++ arg).drop ((pre ++ arg).length - arg.length)).take
    (arg.length - rest.length) = body
  rw [width]
  simp only [List.length_append, Nat.add_sub_cancel, List.drop_left]
  conv => lhs; rw [← parts]
  simp

theorem invariant2_directive_captures (c : Char) (cs : List Char) :
    let tail := cs.dropWhile CharRule.identChar.accepts
    let raw := tail.dropWhile PegVerification.isInlineSpace
    let name := String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)
    capturedDirective ('%' :: c :: cs) (c :: cs).length tail.length raw.length
      (raw.dropWhile (· != '\n')).length =
      .directive name (String.ofList (DirectiveArgument.argument name (raw.takeWhile (· != '\n')))) := by
  dsimp only
  unfold capturedDirective
  have name := invariant1_identifier_capture ['%'] c cs
  simp only [List.cons_append, List.nil_append] at name
  dsimp only
  rw [name]
  let pre := ['%', c] ++ cs.takeWhile CharRule.identChar.accepts ++
    (cs.dropWhile CharRule.identChar.accepts).takeWhile PegVerification.isInlineSpace
  have split : pre ++ ((cs.dropWhile CharRule.identChar.accepts).dropWhile
      PegVerification.isInlineSpace) = '%' :: c :: cs := by simp [pre, List.append_assoc]
  rw [← split, directiveRawCapture]

theorem unknownDirectiveDiagnostic (name arg : String) (p : Predicates)
    (unknown : known.contains name = false) :
    diagnostic ⟨.unknownDirective, name⟩ ∈ errors [.directive name arg] p := by
  apply List.mem_map.mpr
  refine ⟨⟨.unknownDirective, name⟩, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat apply List.mem_append_left
  simpa [directives, emit] using (show name ∉ known by simpa using unknown)

-- The successful File derivation and the assembly error refer to the same input slices.
theorem invariant2_single_unknown_directive (c : Char) (cs : List Char) (p : Predicates)
    (start : CharRule.identStart.accepts c = true)
    (unknown : known.contains (String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)) = false)
    (endOfArg : ((cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      |>.dropWhile (· != '\n')) = []) :
    let tail := cs.dropWhile CharRule.identChar.accepts
    let raw := tail.dropWhile PegVerification.isInlineSpace
    let top := capturedDirective ('%' :: c :: cs) (c :: cs).length tail.length raw.length
      (raw.dropWhile (· != '\n')).length
    FileResult false ('%' :: c :: cs) (.ok 0 {}) ∧
      ∃ ds, assemble [top] p = .error ds ∧
        diagnostic ⟨.unknownDirective, String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)⟩ ∈ ds := by
  refine ⟨invariant1_single_directive_file c cs start endOfArg, ?_⟩
  rw [invariant2_directive_captures]
  have member := unknownDirectiveDiagnostic _ (String.ofList (DirectiveArgument.argument (String.ofList (c :: cs.takeWhile CharRule.identChar.accepts))
    (((cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace).takeWhile
      (· != '\n')))) p unknown
  generalize he : errors _ p = ds at member
  cases ds with
  | nil => simp at member
  | cons d ds => exact ⟨_, by simp only [assemble, he], member⟩

#print axioms invariant2_single_unknown_directive
end PegHs.MetaExecution
