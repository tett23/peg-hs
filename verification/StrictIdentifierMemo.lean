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

theorem invariant1_identifier_memo_call (pre xs : List Char) (env : Env)
    (effects : Nat → Entry (List Char)) (enabled : Bool) (state : State)
    (prior : List Nat) (next : Result (List Char) → State → Calls Nat (List Char)) :
    let input := pre ++ xs
    let body := suffixEntry input (identResult input) effects
    let key := pre.utf8Encode.size
    let prefixRun := runMemo enabled body prior state
    let direct := runMemo false body prior state
    let entry := body key
    ∃ fuel reply, runFuel (context false input) fuel ((context false input).rules 8)
      xs.length env = some reply ∧ captureReply input xs.length reply = some entry.result ∧
      prefixRun.results = direct.results ∧
      runCalls enabled body (.call key next) prefixRun.table prefixRun.state =
        (entry.result :: (runCalls false body (next entry.result (replay direct.state entry)) []
          (replay direct.state entry)).1, (runCalls false body (next entry.result (replay direct.state entry))
          [] (replay direct.state entry)).2) := by
  dsimp only
  have valid := invariant1_identifier_memo_trace (pre ++ xs) effects enabled state
    [(pre, xs, env)] (by simp)
  obtain ⟨fuel, reply, observed, value⟩ := valid.2 (pre, xs, env) (by simp)
  have same := runMemo_same_as_unmemo enabled
    (suffixEntry (pre ++ xs) (identResult (pre ++ xs)) effects) prior state
  refine ⟨fuel, reply, observed, ?_, same.1, ?_⟩
  · simpa [suffixEntry, List.utf8Encode_append, ByteArray.extract_append_eq_right] using value
  · rw [runCalls_sound enabled _ _ _ _ (runMemo_invariant enabled _ prior state), same.2]
    rfl

#print axioms invariant1_identifier_memo_call
#print axioms invariant1_identifier_memo_trace
end PegHs.MetaExecution
