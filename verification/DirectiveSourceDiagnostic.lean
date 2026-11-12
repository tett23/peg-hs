import DirectiveDecode
import DirectiveAssembly

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal AssembleValidation

theorem invariant2_single_string_decoder_error (c : Char) (cs : List Char)
    (p : Predicates) (name gap body : List Char) (msg : String) (start : CharRule.identStart.accepts c = true)
    (endOfArg : ((cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      |>.dropWhile (· != '\n')) = [])
    (supported : String.ofList (c :: cs.takeWhile CharRule.identChar.accepts) = "expect" ∨
      String.ofList (c :: cs.takeWhile CharRule.identChar.accepts) = "message")
    (argument :
      let directive := String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)
      let raw := (cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      DirectiveArgument.argument directive (raw.takeWhile (· != '\n')) = name ++ gap ++ '"' :: body)
    (valid : p.validIdent (String.ofList name) = true)
    (noSpace : ∀ k ∈ name, PegVerification.ghcIsSpace k = false)
    (separator : gap ≠ []) (spaces : ∀ k ∈ gap, PegVerification.ghcIsSpace k = true)
    (failed : TranslatedEscapes.run (body.length + 1) .plain [] body = .error msg)
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
        resolve expand check notes strip warningFor generate) = .error ds ∧ diagnostic ⟨.invalidString, msg⟩ ∈ ds := by
  apply invariant2_single_directive_public_error _ _ _ _ start endOfArg _
    resolve expand check notes strip warningFor generate
  rw [TranslatedEscapes.invariant2_decode_string] at failed
  dsimp only at argument ⊢
  rw [argument]
  exact invariant2_directive_decoder_diagnostic _ p _ name gap body msg supported (.head _)
    valid noSpace separator spaces failed

#print axioms invariant2_single_string_decoder_error
end PegHs.MetaExecution
