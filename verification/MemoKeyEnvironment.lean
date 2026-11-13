import MetaEnvCompatible

namespace PegHs.MemoKeyEnvironment
open EnvironmentEval EnvironmentDepth EnvProjection

-- The generated memoArg wrappers key by the value of d. For a one-argument
-- call, enterCall resets all observations except the evaluated depth.
theorem argument_entry_equal_of_depth (sites : Nat → Option CallSite)
    (site : Nat) (caller callee : String) (source : String)
    (left right : Env)
    (hsite : sites site = some (caller, callee, [source]))
    (harg : depthArgOf source = some arg)
    (hdepth : evalDepthArg left arg = evalDepthArg right arg) :
    enterCall sites site left = enterCall sites site right := by
  simp [enterCall, hsite, harg, hdepth]

theorem argument_key_determines_callee (sites : Nat → Option CallSite)
    (site : Nat) (source : String) (left right : Env)
    (hsite : sites site = some ("caller", "callee", [source]))
    (harg : depthArgOf source = some .current)
    (hdepth : left.depth = right.depth) :
    enterCall sites site left = enterCall sites site right := by
  apply argument_entry_equal_of_depth sites site "caller" "callee" source
    left right hsite harg
  simp [evalDepthArg, hdepth]

-- Argument entry reconstructs the callee environment solely from the
-- evaluated depth. Thus the actual rule computation at this offset can
-- use the canonical environment even when callers have different captures.
theorem argument_body_at_key (mode : Bool) (input : List Char)
    (rule fuel offset depth : Nat) (sites : Nat → Option CallSite)
    (site : Nat) (caller target source : String) (env : Env)
    (found : sites site = some (caller, target, [source]))
    (arg : depthArgOf source = some a)
    (value : evalDepthArg env a = some depth) :
    let ctx := MetaExecution.context mode input
    (enterCall sites site env).bind (runFuel ctx fuel (ctx.rules rule) offset) =
      runFuel ctx fuel (ctx.rules rule) offset {depth := depth} := by
  simp [enterCall, found, arg, value]

-- The cached body reply exists for every key. Calls at distinct sites and
-- executions with different fuel limits agree whenever they return a reply.
theorem argument_key_unique_reply (mode : Bool) (input : List Char)
    (rule offset depth : Nat) :
    let ctx := MetaExecution.context mode input
    let sites := fun i : Nat => if mode then MetaTerminal2.callSites[i]?
      else MetaTerminal1.callSites[i]?
    ∃ result : Reply,
      (∃ fuel, runFuel ctx fuel (ctx.rules rule) offset {depth := depth} = some result) ∧
      ∀ site caller target source env a fuel observed,
        sites site = some (caller, target, [source]) →
        depthArgOf source = some a → evalDepthArg env a = some depth →
        (ctx.hooks.enterCall site env).bind (runFuel ctx fuel (ctx.rules rule) offset) =
          some observed → observed = result := by
  dsimp only
  let ctx := MetaExecution.context mode input
  have rules : ctx.rules = (if mode then MetaTerminal2.environmentBody
      else MetaTerminal1.environmentBody) := by cases mode <;> rfl
  obtain ⟨fuel, result, succeeded⟩ := invariant1_actual_environment_total mode ctx rules
    (offset, rule) {depth := depth}
  refine ⟨result, ⟨fuel, succeeded⟩, ?_⟩
  intro site caller target source env a k observed found arg value returned
  let sites := fun i : Nat => if mode then MetaTerminal2.callSites[i]? else MetaTerminal1.callSites[i]?
  have entered : ctx.hooks.enterCall site env = enterCall sites site env := by cases mode <;> rfl
  change (ctx.hooks.enterCall site env).bind _ = some observed at returned
  rw [entered, argument_body_at_key mode input rule k offset depth sites site caller target
    source env found arg value] at returned
  exact invariant1_result_unique ctx returned succeeded

#print axioms argument_key_unique_reply
#print axioms argument_body_at_key

-- For a no-argument call, the same rule/offset key does not itself imply
-- observational equality of entry environments. A local capture can differ.
theorem noarg_key_does_not_determine_observations :
    ¬ ObsEq
      ((enterCall (fun _ => some ("caller", "callee", [])) 0 ({} : Env)).getD {})
      ((enterCall (fun _ => some ("caller", "callee", [])) 0
        (({} : Env).put "x" ['a'])).getD {}) := by
  intro same
  have h := same.capture "x"
  simp [enterCall, Env.put, Env.lookup] at h

#print axioms argument_entry_equal_of_depth
#print axioms noarg_key_does_not_determine_observations

end PegHs.MemoKeyEnvironment
