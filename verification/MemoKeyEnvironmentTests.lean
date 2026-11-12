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
