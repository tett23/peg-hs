import TranslatedRuntimeChoice

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

end PegHs.EnvironmentEval
