import DirectiveSuccess
import DirectiveArgument
import AssembleValidation

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal AssembleValidation

-- Both binders use remaining-input lengths, as in the generated Directive rule.
def capturedDirective (input : List Char) (nameStart nameEnd rawStart rawEnd : Nat) : Top :=
  let name := String.ofList (matchedText input nameStart nameEnd)
  let raw := matchedText input rawStart rawEnd
  translatedDirectiveValue Top.directive DirectiveArgument.argument name raw

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

theorem invariant2_directive_captures_at (before : List Char) (c : Char) (cs : List Char) :
    let tail := cs.dropWhile CharRule.identChar.accepts
    let raw := tail.dropWhile PegVerification.isInlineSpace
    let name := String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)
    capturedDirective (before ++ '%' :: c :: cs) (c :: cs).length tail.length raw.length
      (raw.dropWhile (· != '\n')).length =
      .directive name (String.ofList (DirectiveArgument.argument name (raw.takeWhile (· != '\n')))) := by
  dsimp only
  unfold capturedDirective translatedDirectiveValue
  have name := invariant1_identifier_capture (before ++ ['%']) c cs
  simp only [List.append_assoc, List.cons_append, List.nil_append] at name
  dsimp only
  rw [name]
  let pre := before ++ ['%', c] ++ cs.takeWhile CharRule.identChar.accepts ++
    (cs.dropWhile CharRule.identChar.accepts).takeWhile PegVerification.isInlineSpace
  have split : pre ++ ((cs.dropWhile CharRule.identChar.accepts).dropWhile
      PegVerification.isInlineSpace) = before ++ '%' :: c :: cs := by simp [pre, List.append_assoc]
  rw [← split, directiveRawCapture]

theorem invariant2_directive_captures (c : Char) (cs : List Char) :
    let tail := cs.dropWhile CharRule.identChar.accepts
    let raw := tail.dropWhile PegVerification.isInlineSpace
    let name := String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)
    capturedDirective ('%' :: c :: cs) (c :: cs).length tail.length raw.length
      (raw.dropWhile (· != '\n')).length =
      .directive name (String.ofList (DirectiveArgument.argument name (raw.takeWhile (· != '\n')))) :=
  invariant2_directive_captures_at [] c cs

private theorem filteredDirectiveDiagnostic (tops : List Top) (name arg : String)
    (kind : Kind) (test : String × String → Bool)
    (member : Top.directive name arg ∈ tops) (accepted : test (name, arg) = true) :
    ⟨kind, name⟩ ∈ emit kind (((directives tops).filter test).map (·.1)) := by
  apply List.mem_map.mpr
  refine ⟨name, List.mem_map.mpr ⟨(name, arg), List.mem_filter.mpr ⟨?_, accepted⟩, rfl⟩, rfl⟩
  exact List.mem_filterMap.mpr ⟨.directive name arg, member, rfl⟩

theorem unknownDirectiveDiagnostic (tops : List Top) (name arg : String) (p : Predicates)
    (member : Top.directive name arg ∈ tops)
    (unknown : known.contains name = false) :
    diagnostic ⟨.unknownDirective, name⟩ ∈ errors tops p := by
  apply List.mem_map.mpr
  refine ⟨⟨.unknownDirective, name⟩, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat apply List.mem_append_left
  exact filteredDirectiveDiagnostic tops name arg .unknownDirective _ member
    (by change (!known.contains name) = true; rw [unknown]; rfl)

theorem invariant2_missing_argument (tops : List Top) (name : String) (p : Predicates)
    (member : Top.directive name "" ∈ tops) (recognized : known.contains name = true)
    (required : ["syntax", "deriving", "library"].contains name = false) :
    diagnostic ⟨.missingArgument, name⟩ ∈ errors tops p := by
  have emitted := filteredDirectiveDiagnostic tops name "" .missingArgument
    (fun d => known.contains d.1 && !["syntax", "deriving", "library"].contains d.1 && d.2.isEmpty)
    member (by simp only [recognized, required]; rfl)
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

theorem invariant2_unexpected_argument (tops : List Top) (name arg : String) (p : Predicates)
    (member : Top.directive name arg ∈ tops) (flag : ["syntax", "library"].contains name = true)
    (nonempty : arg.isEmpty = false) :
    diagnostic ⟨.unexpectedArgument, name⟩ ∈ errors tops p := by
  have emitted := filteredDirectiveDiagnostic tops name arg .unexpectedArgument
    (fun d => ["syntax", "library"].contains d.1 && !d.2.isEmpty)
    member (by simp only [flag, nonempty]; rfl)
  apply List.mem_map.mpr
  refine ⟨_, List.mem_append_left _ ?_, rfl⟩
  unfold otherViolations
  dsimp only [Id.run, Bind.bind, pure, Pure.pure, Id.instMonad]
  repeat first | exact List.mem_append_right _ emitted | apply List.mem_append_left

private theorem reportedRejection (tops : List Top) (p : Predicates) (v : Violation)
    (reported : diagnostic v ∈ errors tops p) :
    ∃ ds, assemble tops p = .error ds ∧ diagnostic v ∈ ds := by
  cases he : errors tops p with
  | nil => simp [he] at reported
  | cons d ds => exact ⟨_, by simp only [assemble, he], he ▸ reported⟩

theorem unknownDirectiveRejected (tops : List Top) (name arg : String) (p : Predicates)
    (member : Top.directive name arg ∈ tops) (unknown : known.contains name = false) :
    ∃ ds, assemble tops p = .error ds ∧ diagnostic ⟨.unknownDirective, name⟩ ∈ ds := by
  exact reportedRejection _ _ _ (unknownDirectiveDiagnostic tops name arg p member unknown)

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
  exact unknownDirectiveRejected _ _ _ p (.head _) unknown

-- The downstream stages are arbitrary. A diagnostic from the captured declaration
-- survives to the public result, including when the declaration also lacks a module.
theorem invariant2_single_directive_public_error (c : Char) (cs : List Char)
    (p : Predicates) (v : Violation) (start : CharRule.identStart.accepts c = true)
    (endOfArg : ((cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      |>.dropWhile (· != '\n')) = [])
    (reported :
      let name := String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)
      let raw := (cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      diagnostic v ∈ errors [.directive name
        (String.ofList (DirectiveArgument.argument name (raw.takeWhile (· != '\n'))))] p)
    (resolve expand check : Unit → Except (List String) Unit)
    (notes : Unit → List String → List String)
    (strip : Option (Unit → Unit)) (warningFor : Unit → Unit → List String)
    (generate : Unit → Except (List String) String) :
    let tail := cs.dropWhile CharRule.identChar.accepts
    let raw := tail.dropWhile PegVerification.isInlineSpace
    let top := capturedDirective ('%' :: c :: cs) (c :: cs).length tail.length raw.length
      (raw.dropWhile (· != '\n')).length
    FileResult false ('%' :: c :: cs) (.ok 0 {}) ∧
      ∃ ds, Pipeline.visible (Pipeline.pipeline (parseGrammar (.ok [top]) p)
        resolve expand check notes strip warningFor generate) = .error ds ∧ diagnostic v ∈ ds := by
  refine ⟨invariant1_single_directive_file c cs start endOfArg, ?_⟩
  rw [invariant2_directive_captures]
  dsimp only at reported
  obtain ⟨ds, failed, member⟩ := reportedRejection _ p v reported
  exact ⟨ds, (public_assemble_failure _ p ds failed resolve expand check notes strip warningFor
    generate).1, member⟩

-- A trailing comment can remove the entire argument or leave a nonempty value.
example (p : Predicates) :
    diagnostic ⟨.missingArgument, "module"⟩ ∈
      errors [capturedDirective "%module  # ignored".toList 17 11 9 0] p := by
  apply invariant2_missing_argument _ _ _ _ (by decide +kernel) (by decide +kernel)
  exact .head _

example (p : Predicates) :
    diagnostic ⟨.unexpectedArgument, "syntax"⟩ ∈
      errors [capturedDirective "%syntax  yes # ignored".toList 21 15 13 0] p := by
  apply invariant2_unexpected_argument _ _ "yes" _ _ (by decide +kernel) (by decide +kernel)
  exact .head _

#print axioms invariant2_single_directive_public_error
#print axioms invariant2_single_unknown_directive
end PegHs.MetaExecution
