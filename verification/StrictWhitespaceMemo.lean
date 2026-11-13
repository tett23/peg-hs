import StrictWhitespaceScan
import MemoTrace

namespace PegHs.MetaExecution
open MemoRecognition MemoTrace EnvironmentEval

-- Only recognition is projected here. Diagnostics and dependencies are
-- parameters so the statement cannot depend on their values.
noncomputable def suffixEntry (input : List Char) (recognize : List Char → Result α)
    (effects : Nat → Entry α) (key : Nat) : Entry α :=
  let bytes := input.utf8Encode
  let result := match (bytes.extract key bytes.size).utf8Decode? with
    | none => Result.fail
    | some suffix => recognize suffix.toList
  { effects key with result }

theorem suffix_trace (input : List Char) (recognize : List Char → Result α)
    (effects : Nat → Entry α) (enabled : Bool) (state : State)
    (calls : List (List Char × List Char × Env))
    (valid : ∀ call ∈ calls, call.1 ++ call.2.1 = input) :
    (runMemo enabled (suffixEntry input recognize effects)
      (calls.map fun call => call.1.utf8Encode.size) state).results =
      calls.map fun call => recognize call.2.1 := by
  unfold runMemo
  rw [(runFrom_sound enabled _ _ [] state (empty_invariant _)).1]
  simp only [List.map_map]
  apply List.map_congr_left
  intro call member
  rw [← valid call member]
  simp [suffixEntry, List.utf8Encode_append, ByteArray.extract_append_eq_right]

private noncomputable def wsEntry (input : List Char) := suffixEntry input fun suffix =>
  Result.ok (Utf8Terminals.byteOffset input (input.length - (afterWhitespace suffix).length)) ()

theorem invariant1_strict_ws_memo_trace (input : List Char) (effects : Nat → Entry Unit)
    (enabled : Bool) (state : State) (calls : List (List Char × List Char × Env))
    (valid : ∀ call ∈ calls, call.1 ++ call.2.1 = input) :
    let keys := calls.map fun call => call.1.utf8Encode.size
    let run := runMemo enabled (wsEntry input effects) keys state
    run.results = calls.map (fun call => Result.ok
      (Utf8Terminals.byteOffset input (input.length - (afterWhitespace call.2.1).length)) ()) ∧
    ∀ call ∈ calls, ∃ fuel,
      runFuel (context false input) fuel ((context false input).rules 4) call.2.1.length
        call.2.2 = some (.ok (afterWhitespace call.2.1).length { call.2.2 with resultDepth := 0 }) := by
  constructor
  · exact suffix_trace input _ effects enabled state calls valid
  · intro call member
    rw [← valid call member]
    exact (invariant1_strict_ws_memo_reply _ _ _ _).2 rfl

#print axioms invariant1_strict_ws_memo_trace
end PegHs.MetaExecution
