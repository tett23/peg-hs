import MetaExecution

namespace PegHs.MetaExecution
open EnvironmentEval

def consumesFile (mode : Bool) (source : String) (fuel : Nat) : Bool :=
  let input := source.toList
  let ctx := context mode input
  match runFuel ctx fuel (ctx.rules (startRule mode)) input.length {} with
  | some (.ok 0 _) => true
  | _ => false

theorem file_acceptance_certificate {mode source fuel} (checked : consumesFile mode source fuel) :
    ∃ env, FileResult mode source.toList (.ok 0 env) := by
  simp only [consumesFile] at checked
  split at checked
  · rename_i env observed
    exact ⟨env, invariant1_runFuel_sound observed⟩
  · contradiction

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem invariant1_accept_any_rule (mode : Bool) :
    ∃ env, FileResult mode "S <- .".toList (.ok 0 env) := by
  apply file_acceptance_certificate (fuel := 256)
  cases mode <;> decide +kernel

theorem labelled_result_excludes_acceptance {mode input pos label msg}
    (rejected : FileResult mode input (.throwLabel pos label msg)) :
    ¬ ∃ env, FileResult mode input (.ok 0 env) := by
  obtain ⟨_, _, unique⟩ := invariant1_file_result mode input
  rintro ⟨env, accepted⟩
  exact Reply.noConfusion ((unique _ accepted).trans (unique _ rejected).symm)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem invariant2_invalid_expressions (mode : Bool) :
    FileResult mode "S <- &".toList (.throwLabel 0 "expression" (some "expected an expression")) ∧
    FileResult mode "S <- [z-a]".toList (.throwLabel 1 "range" (some "the range is empty")) ∧
    FileResult mode "S <- '\\u{110000}'".toList (.throwLabel 1 "uescape" (some "invalid \\u escape")) := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold FileResult <;>
    apply invariant1_runFuel_sound (fuel := 512) <;> cases mode <;> decide +kernel

#print axioms invariant2_invalid_expressions
#print axioms invariant1_accept_any_rule
end PegHs.MetaExecution
