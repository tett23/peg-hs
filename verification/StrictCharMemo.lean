import StrictWhitespaceMemo
import StrictSpaceChar

namespace PegHs.MetaExecution
open MemoRecognition MemoTrace EnvironmentEval

private noncomputable def charResult (rule : CharRule) (input : List Char) :
    List Char → Result Unit
  | [] => .fail
  | c :: tail => if rule.accepts c then
      .ok (Utf8Terminals.byteOffset input (input.length - tail.length)) ()
    else .fail

private noncomputable def charReply (input : List Char) : Reply → Option (Result Unit)
  | .ok rest _ => some (.ok (Utf8Terminals.byteOffset input (input.length - rest)) ())
  | .fail => some .fail
  | .throwLabel .. => none

theorem invariant1_char_memo_trace (rule : CharRule) (input : List Char)
    (effects : Nat → Entry Unit) (enabled : Bool) (state : State)
    (calls : List (List Char × List Char × Env))
    (valid : ∀ call ∈ calls, call.1 ++ call.2.1 = input) :
    let run := runMemo enabled (suffixEntry input (charResult rule input) effects)
      (calls.map fun call => call.1.utf8Encode.size) state
    run.results = calls.map (fun call => charResult rule input call.2.1) ∧
    ∀ call ∈ calls, (runFuel (context false input) 5 rule.body call.2.1.length call.2.2).bind
      (charReply input) = some (charResult rule input call.2.1) := by
  refine ⟨suffix_trace input _ effects enabled state calls valid, ?_⟩
  rintro ⟨pre, suffix, env⟩ member
  obtain rfl := valid _ member
  cases suffix with
  | nil =>
    exact congrArg (fun r : Option Reply => r.bind (charReply (pre ++ [])))
      (invariant1_strict_char_eof rule (pre ++ []) env)
  | cons c tail =>
    have step := invariant1_strict_char rule pre c tail env
    dsimp only at step ⊢
    rw [step]
    cases h : rule.accepts c <;> simp [charResult, charReply, h]

#print axioms invariant1_char_memo_trace
end PegHs.MetaExecution
