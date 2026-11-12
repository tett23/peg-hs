import MetaExecution
import EnvRunCongruence
import EnvProjectionPredicate

namespace PegHs.MetaEnvCompatible
open EnvironmentEval EnvProjection EnvRunCongruence

private theorem compatible_of_fields (ctx : Inputs)
    (predSpec : ∀ site env, ctx.predicateEnv site env =
      match ctx.sites site with
      | some (kind, _) => PredicateBindings.predicateEnv kind env
      | none => { captured := [], depth := env.depth })
    (hookSpec : ∃ sites shapeAt, ctx.hooks = EnvironmentDepth.hooks sites shapeAt) :
    Compatible ctx := by
  obtain ⟨sites, shapeAt, hooks⟩ := hookSpec
  constructor
  · intro site left right same
    rw [predSpec site left, predSpec site right]
    cases hs : ctx.sites site with
    | none => rfl
    | some pair =>
        rcases pair with ⟨kind, polarity⟩
        simp only [Option.map_some]
        exact congrArg some (actual_predicate_noninterference same ctx.classes kind)
  · intro site left right same
    rw [hooks]
    exact enterCall_congr same sites site
  · intro site name value left right same
    rw [hooks]
    exact bindShape_congr same shapeAt site name value
  · intro site callerLeft callerRight calleeLeft calleeRight callers callees
    rw [hooks]
    exact leaveCall_congr callers callees sites shapeAt site

theorem actual_context_compatible (syntaxMode : Bool) (input : List Char) :
    Compatible (MetaExecution.context syntaxMode input) := by
  apply compatible_of_fields
  · intro site env
    cases syntaxMode <;> rfl
  · cases syntaxMode
    · refine ⟨(fun id => MetaTerminal1.callSites[id]?), (fun _ _ _ => none), ?_⟩
      rfl
    · refine ⟨(fun id => MetaTerminal2.callSites[id]?), (fun _ _ _ => none), ?_⟩
      rfl

theorem actual_runFuel_congr (syntaxMode : Bool) (input : List Char)
    (fuel : Nat) (body : Body) (remaining : Nat)
    (left right : Env) (same : ObsEq left right) :
    OptionReplyRel
      (runFuel (MetaExecution.context syntaxMode input) fuel body remaining left)
      (runFuel (MetaExecution.context syntaxMode input) fuel body remaining right) :=
  runFuel_congr _ (actual_context_compatible syntaxMode input) fuel body remaining left right same

#print axioms actual_runFuel_congr

end PegHs.MetaEnvCompatible
