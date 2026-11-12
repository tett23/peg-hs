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
