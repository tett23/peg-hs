import MetaExecution

namespace PegHs.NoArgInputReads
open EnvironmentEval ConcreteTerminal

inductive Status where
  | ok (remaining : Nat)
  | fail
  | throwLabel (position : Nat) (name : String) (message : Option String)
  deriving DecidableEq

def status : Option Reply → Option Status
  | none => none
  | some (.ok remaining _) => some (.ok remaining)
  | some .fail => some .fail
  | some (.throwLabel position name message) =>
      some (.throwLabel position name message)

private theorem terminal_ignores_env (ctx : Inputs) (fuel site remaining : Nat)
    (left right : Env) :
    status (runFuel ctx fuel (.terminal site) remaining left) =
      status (runFuel ctx fuel (.terminal site) remaining right) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases ht : ctx.terms site with
      | none => simp [runFuel, ht, status]
      | some term =>
          cases ho : terminalOracle term ctx.input remaining with
          | none => simp [runFuel, ht, ho, status]
          | some rest =>
              by_cases hrest : rest < remaining <;>
                simp [runFuel, ht, ho, hrest, status]

private theorem terminal_loop_ignores_env (ctx : Inputs) (fuel site remaining : Nat)
    (left right : Env) :
    status (runFuel ctx fuel (.starLoop (.terminal site)) remaining left) =
      status (runFuel ctx fuel (.starLoop (.terminal site)) remaining right) := by
  induction fuel generalizing remaining left right with
  | zero => rfl
  | succ fuel ih =>
      cases fuel with
      | zero => simp [runFuel, status]
      | succ fuel =>
          cases ht : ctx.terms site with
          | none => simp [runFuel, ht, status]
          | some term =>
              cases ho : terminalOracle term ctx.input remaining with
              | none => simp [runFuel, ht, ho, status]
              | some rest =>
                  by_cases hrest : rest < remaining
                  · simp [runFuel, ht, ho, hrest]
                    change status (runFuel ctx (fuel + 1) (.starLoop (.terminal site)) rest left) =
                      status (runFuel ctx (fuel + 1) (.starLoop (.terminal site)) rest right)
                    exact ih rest left right
                  · simp [runFuel, ht, ho, hrest, status]

theorem terminal_star_ignores_env (ctx : Inputs) (fuel site remaining : Nat)
    (left right : Env) :
    status (runFuel ctx fuel (.star (.terminal site)) remaining left) =
      status (runFuel ctx fuel (.star (.terminal site)) remaining right) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simpa only [runFuel] using terminal_loop_ignores_env ctx fuel site remaining
        {left with resultDepth := 0} {right with resultDepth := 0}

-- ExtractSelfHostedFile.hs maps rule 7 to InlineSp in both metagrammars.
theorem actual_inlineSp_ignores_env (syntaxMode : Bool) (input : List Char)
    (fuel remaining : Nat) (left right : Env) :
    let ctx := MetaExecution.context syntaxMode input
    status (runFuel ctx fuel (ctx.rules 7) remaining left) =
      status (runFuel ctx fuel (ctx.rules 7) remaining right) := by
  cases syntaxMode with
  | false =>
      change status (runFuel (MetaExecution.peg input) fuel
        (MetaTerminal1.environmentBody 7) remaining left) =
        status (runFuel (MetaExecution.peg input) fuel
          (MetaTerminal1.environmentBody 7) remaining right)
      have body : MetaTerminal1.environmentBody 7 = .star (.terminal 5) := by
        decide +kernel
      rw [body]
      exact terminal_star_ignores_env _ fuel 5 remaining left right
  | true =>
      change status (runFuel (MetaExecution.syntaxPeg input) fuel
        (MetaTerminal2.environmentBody 7) remaining left) =
        status (runFuel (MetaExecution.syntaxPeg input) fuel
          (MetaTerminal2.environmentBody 7) remaining right)
      have body : MetaTerminal2.environmentBody 7 = .star (.terminal 6) := by
        decide +kernel
      rw [body]
      exact terminal_star_ignores_env _ fuel 6 remaining left right

#print axioms actual_inlineSp_ignores_env

end PegHs.NoArgInputReads
