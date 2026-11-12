import EnvProjection
import MemoTrace

namespace PegHs.MemoKeyTransfer
open PegHs.EnvProjection PegHs.EnvironmentEval PegHs.MemoRecognition PegHs.MemoTrace

-- A key includes every observation required by the body when each actual
-- invocation is observationally equal to the canonical environment of that
-- key. The result equality is the noninterference obligation for the body.
theorem same_key_result {κ α : Type} (key : κ)
    (canonical : κ → Env) (observed : Env → Result α)
    (body : κ → Entry α) (left right : Env)
    (leftKey : ObsEq left (canonical key))
    (rightKey : ObsEq right (canonical key))
    (bodyCongruent : ∀ env, ObsEq env (canonical key) →
      observed env = (body key).result) :
    observed left = observed right := by
  calc
    observed left = (body key).result := bodyCongruent left leftKey
    _ = observed right := (bodyCongruent right rightKey).symm

theorem trace_result_transfer [DecidableEq κ] {α : Type}
    (body : κ → Entry α) (canonical : κ → Env)
    (observed : κ → Env → Result α)
    (calls : List (κ × Env)) (state : State)
    (keyed : ∀ call ∈ calls, ObsEq call.2 (canonical call.1))
    (bodyCongruent : ∀ key env, ObsEq env (canonical key) →
      observed key env = (body key).result) :
    (runMemo true body (calls.map Prod.fst) state).results =
      calls.map (fun call => observed call.1 call.2) := by
  have sound := (runFrom_sound true body (calls.map Prod.fst) [] state
    (empty_invariant body)).1
  calc
    (runMemo true body (calls.map Prod.fst) state).results =
        (calls.map Prod.fst).map (fun k => (body k).result) := sound
    _ = calls.map (fun call => (body call.1).result) := by simp [List.map_map]
    _ = calls.map (fun call => observed call.1 call.2) :=
      List.map_congr_left (fun call member =>
        (bodyCongruent call.1 call.2 (keyed call member)).symm)

#print axioms same_key_result
#print axioms trace_result_transfer

end PegHs.MemoKeyTransfer
