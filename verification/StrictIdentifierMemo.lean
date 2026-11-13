import StrictWhitespaceMemo
import StrictIdentifier

namespace PegHs.MetaExecution
open MemoRecognition MemoTrace EnvironmentEval

private noncomputable def captureReply (input : List Char) (remaining : Nat) : Reply → Option (Result (List Char))
  | .ok rest _ => some (.ok (Utf8Terminals.byteOffset input (input.length - rest))
      (matchedText input remaining rest))
  | .fail => some .fail
  | .throwLabel .. => none

private noncomputable def identResult (input : List Char) : List Char → Result (List Char)
  | [] => .fail
  | c :: cs => if CharRule.identStart.accepts c then
      .ok (Utf8Terminals.byteOffset input
        (input.length - (cs.dropWhile CharRule.identChar.accepts).length))
        (c :: cs.takeWhile CharRule.identChar.accepts)
    else .fail

theorem invariant1_identifier_memo_trace (input : List Char)
    (effects : Nat → Entry (List Char)) (enabled : Bool) (state : State)
    (calls : List (List Char × List Char × Env))
    (valid : ∀ call ∈ calls, call.1 ++ call.2.1 = input) :
    let run := runMemo enabled (suffixEntry input (identResult input) effects)
      (calls.map fun call => call.1.utf8Encode.size) state
    run.results = calls.map (fun call => identResult input call.2.1) ∧
    ∀ call ∈ calls, ∃ fuel reply,
      runFuel (context false input) fuel ((context false input).rules 8)
        call.2.1.length call.2.2 = some reply ∧
      captureReply input call.2.1.length reply = some (identResult input call.2.1) := by
  refine ⟨suffix_trace input _ effects enabled state calls valid, ?_⟩
  rintro ⟨pre, xs, env⟩ member
  obtain rfl := valid _ member
  obtain ⟨fuel, observed⟩ := invariant1_derivation_has_fuel (invariant1_strict_identifier pre xs env)
  refine ⟨fuel, _, observed, ?_⟩
  cases xs with
  | nil => rfl
  | cons c cs =>
    cases h : CharRule.identStart.accepts c <;>
      simp [captureReply, identResult, h]
    exact invariant1_identifier_capture pre c cs

#print axioms invariant1_identifier_memo_trace
end PegHs.MetaExecution
