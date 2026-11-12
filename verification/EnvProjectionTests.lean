import EnvProjection

open PegHs.EnvironmentEval PegHs.EnvProjection

private def caller : Env :=
  { depth := 3, captures := [("c", ['a'])], valueDepths := [("e", 2)] }
private def shadowed : Env :=
  { depth := 3, captures := [("c", ['a']), ("c", ['z'])],
    valueDepths := [("e", 2), ("e", 99)] }

-- Invariant 1: shadowed bindings do not change observable values.
private theorem caller_shadowed_obs : ObsEq caller shadowed := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro name
    by_cases h : name = "c"
    · subst name; decide
    · have hc : ("c" == name) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      simp [caller, shadowed, Env.lookup, List.find?, hc]
  · intro name
    by_cases h : name = "e"
    · subst name; decide
    · have he : ("e" == name) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      simp [caller, shadowed, Env.valueDepth, List.find?, he]
  · intro name
    by_cases h : name = "c" <;> simp [caller, shadowed, hasCapture, h]

example : DepthAction.eval caller (.copy "e") =
    DepthAction.eval shadowed (.copy "e") := by decide
example : predicateProjection (some "c") caller =
    predicateProjection (some "c") shadowed := by rfl

example : OptionObsEq
    (PegHs.EnvironmentDepth.enterCall (fun _ => some ("P", "Q", ["d + snd e"])) 0 caller)
    (PegHs.EnvironmentDepth.enterCall (fun _ => some ("P", "Q", ["d + snd e"])) 0 shadowed) :=
  enterCall_congr caller_shadowed_obs _ _

example : OptionObsEq
    (PegHs.EnvironmentDepth.bindShape (fun _ _ _ => none) 0 "x" ['b'] caller)
    (PegHs.EnvironmentDepth.bindShape (fun _ _ _ => none) 0 "x" ['b'] shadowed) :=
  bindShape_congr caller_shadowed_obs _ _ _ _

example : ¬ ObsEq ({ depth := 1 } : Env) ({ depth := 2 } : Env) := by
  intro same
  cases same.depth
