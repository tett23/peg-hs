import TranslatedRuntimeChoice
import EnvironmentDerivation

namespace PegHs.EnvironmentEval

theorem invariant1_runtime_choice_two (ctx : Inputs) (fuel n : Nat) (env : Env) (a b : Body) :
    translatedChoice [runFuel ctx fuel a n env, runFuel ctx fuel b n env] =
      runFuel ctx (fuel + 1) (.alt a b) n env := by
  simp only [runFuel, translatedChoice]
  cases runFuel ctx fuel a n env with
  | none => rfl
  | some r =>
    cases r <;> try rfl
    cases runFuel ctx fuel b n env with
    | none => rfl
    | some s => cases s <;> rfl

-- The empty runtime choice fails at its input position, as does !epsilon.
def choiceBody (branches : List Body) : Body :=
  branches.foldr .alt (.notAhead .eps)

theorem invariant1_runtime_choice_list {ctx : Inputs} {n : Nat} {env : Env}
    (branches : List (Body × Reply))
    (children : ∀ x ∈ branches, Derives ctx x.1 n env x.2) :
    ∃ r, translatedChoice (branches.map (fun x => some x.2)) = some r ∧
      Derives ctx (choiceBody (branches.map Prod.fst)) n env r := by
  induction branches with
  | nil => exact ⟨.fail, rfl, .notAhead .eps⟩
  | cons first branches ih =>
    obtain ⟨branch, reply⟩ := first
    have head := children (branch, reply) (by simp)
    obtain ⟨r, observed, tail⟩ := ih (fun x h => children x (List.mem_cons_of_mem _ h))
    cases reply with
    | ok pos next => exact ⟨_, rfl, .altLeft head (by simp)⟩
    | throwLabel pos name message => exact ⟨_, rfl, .altLeft head (by simp)⟩
    | fail => exact ⟨r, observed, .altRetry head tail⟩

end PegHs.EnvironmentEval
