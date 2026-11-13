import MemoKeyEnvironment

open PegHs.EnvironmentEval PegHs.MemoKeyEnvironment

example (sites : Nat → Option PegHs.EnvironmentDepth.CallSite)
    (site : Nat) (source : String) (left right : Env)
    (hsite : sites site = some ("caller", "callee", [source]))
    (harg : PegHs.EnvironmentDepth.depthArgOf source = some .current)
    (hdepth : left.depth = right.depth) :
    PegHs.EnvironmentDepth.enterCall sites site left =
      PegHs.EnvironmentDepth.enterCall sites site right :=
  argument_key_determines_callee sites site source left right hsite harg hdepth

example (mode : Bool) (input : List Char) (rule fuel offset depth : Nat)
    (sites : Nat → Option PegHs.EnvironmentDepth.CallSite)
    (site : Nat) (caller target source : String) (env : Env)
    (found : sites site = some (caller, target, [source]))
    (arg : PegHs.EnvironmentDepth.depthArgOf source = some a)
    (value : PegHs.EnvironmentDepth.evalDepthArg env a = some depth) :
    let ctx := PegHs.MetaExecution.context mode input
    (PegHs.EnvironmentDepth.enterCall sites site env).bind
      (runFuel ctx fuel (ctx.rules rule) offset) =
      runFuel ctx fuel (ctx.rules rule) offset {depth := depth} :=
  argument_body_at_key mode input rule fuel offset depth sites site caller target source env found arg value
