import NoArgInputReads

open PegHs.EnvironmentEval PegHs.NoArgInputReads

example (ctx : Inputs) (fuel site remaining : Nat) (left right : Env) :
    status (runFuel ctx fuel (.star (.terminal site)) remaining left) =
      status (runFuel ctx fuel (.star (.terminal site)) remaining right) :=
  terminal_star_ignores_env ctx fuel site remaining left right

example (syntaxMode : Bool) (input : List Char)
    (fuel remaining : Nat) (left right : Env) :
    let ctx := PegHs.MetaExecution.context syntaxMode input
    status (runFuel ctx fuel (ctx.rules 7) remaining left) =
      status (runFuel ctx fuel (ctx.rules 7) remaining right) :=
  actual_inlineSp_ignores_env syntaxMode input fuel remaining left right
