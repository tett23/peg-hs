import EnvRunCongruence

open PegHs.EnvironmentEval PegHs.EnvProjection PegHs.EnvRunCongruence

private def context : Inputs :=
  { rules := fun _ => .eps, terms := fun _ => none,
    sites := fun _ => none, actions := fun _ => none,
    classes := {space := fun _ => false, alpha := fun _ => false, alnum := fun _ => false},
    predicateEnv := fun _ _ => {captured := [], depth := 0},
    hooks := defaultHooks, input := [] }

example : ReplyRel (.ok 0 {}) (.ok 0 {}) :=
  ⟨rfl, ObsEq.refl _⟩
example : OptionReplyRel (runFuel context 3 .eps 0 {})
    (runFuel context 3 .eps 0 {}) := by
  exact ⟨rfl, ObsEq.refl _⟩
