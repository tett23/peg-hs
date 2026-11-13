import StrictWhitespaceLexical
import DirectiveAssembly

namespace PegHs.MetaExecution
open EnvironmentEval AssembleValidation

def directiveValues : List Char → Option (List Top)
  | [] => some []
  | '%' :: c :: cs => if CharRule.identStart.accepts c then do
      let tail ← directiveValues (afterDirectiveItem cs)
      let name := String.ofList (c :: cs.takeWhile CharRule.identChar.accepts)
      let raw := (cs.dropWhile CharRule.identChar.accepts).dropWhile PegVerification.isInlineSpace
      return .directive name (String.ofList (DirectiveArgument.argument name (raw.takeWhile (· != '\n')))) :: tail
    else none
  | _ => none
termination_by xs => xs.length
decreasing_by exact invariant1_directive_item_progress cs

private theorem remainingSuffix (c : Char) (cs : List Char) :
    (afterDirectiveItem cs).IsSuffix ('%' :: c :: cs) := by
  apply List.IsSuffix.trans (afterWhitespace_suffix _)
  apply List.IsSuffix.trans (List.dropWhile_suffix _)
  apply List.IsSuffix.trans (List.dropWhile_suffix _)
  apply List.IsSuffix.trans (List.dropWhile_suffix _)
  exact ⟨['%', c], rfl⟩

theorem directiveValues_items (xs pre : List Char) (values : List Top)
    (parsed : directiveValues xs = some values) :
    TopItems (context false (pre ++ xs)) xs.length {} 0 {} := by
  induction xs using (measure (List.length (α := Char))).wf.induction generalizing pre values with
  | h xs ih =>
    cases xs with
    | nil => exact invariant1_top_items_end false _ {}
    | cons marker tail =>
      cases tail with
      | nil => simp [directiveValues] at parsed
      | cons c cs =>
        by_cases markerEq : marker = '%'
        · subst marker
          rw [directiveValues] at parsed
          split at parsed
          · rename_i valid
            cases next : directiveValues (afterDirectiveItem cs) with
            | none => simp [next] at parsed
            | some later =>
              obtain ⟨consumed, splitInput⟩ := remainingSuffix c cs
              have tail := ih _ (invariant1_directive_item_progress cs) (pre ++ consumed) later next
              rw [List.append_assoc, splitInput] at tail
              exact invariant1_directive_then_items pre c cs valid tail
          · contradiction
        · simp [directiveValues, markerEq] at parsed

#print axioms directiveValues_items
end PegHs.MetaExecution
