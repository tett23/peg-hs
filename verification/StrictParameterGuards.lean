import SelfHostedFileProof

namespace PegHs.MetaExecution
open EnvironmentEval

private def guardBody (site : Nat) (name msg : String) : Body :=
  .label name (some msg) (.predicate site)

private def guards (delimiter : Body) : Body :=
  .seq (guardBody 4 "argument" "expected an argument")
    (.seq (guardBody 5 "paramform" "expected a parameter of the form name :: Type")
      (.seq (guardBody 6 "paramtype" "expected a parameter type") delimiter))

private theorem rejected {ctx : Inputs} {site n : Nat} {env : Env} {name msg : String}
    (h : predicateTest ctx site env ≠ some true) :
    Derives ctx (guardBody site name msg) n env (.throwLabel n name (some msg)) :=
  Derives.label (r := .fail) (.predicateFail (by cases v : predicateTest ctx site env <;> simp_all))

private theorem accepted {ctx : Inputs} {site n : Nat} {env : Env} {name msg : String}
    (h : predicateTest ctx site env = some true) :
    Derives ctx (guardBody site name msg) n env (.ok n {env with resultDepth := 0}) :=
  Derives.label (r := .ok ..) (.predicateOk h)

theorem invariant2_parameter_guard_order (input : List Char) (n : Nat) (env : Env)
    (delimiter : Body) (r : Reply)
    (last : Derives (context false input) delimiter n {env with resultDepth := 0} r) :
    let ctx := context false input
    let next := {env with resultDepth := 0}
    Derives ctx (guards delimiter) n env
      (if predicateTest ctx 4 env != some true then .throwLabel n "argument" (some "expected an argument")
       else if predicateTest ctx 5 next != some true then
         .throwLabel n "paramform" (some "expected a parameter of the form name :: Type")
       else if predicateTest ctx 6 next != some true then .throwLabel n "paramtype" (some "expected a parameter type")
       else r) := by
  dsimp only
  simp only [bne_iff_ne, ne_eq, ite_not]
  split <;> rename_i a
  · apply Derives.seqOk (accepted a)
    split <;> rename_i b
    · apply Derives.seqOk (accepted b)
      split <;> rename_i c
      · exact .seqOk (accepted c) last
      · exact .seqCarryThrow (rejected c)
    · exact .seqCarryThrow (rejected b)
  · exact .seqCarryThrow (rejected a)

theorem invariant2_parameter_guard_shape :
    translatedStrictParamChunk = .seq (.call 47 4) (.seq (.bind 27 "l" (.call 48 3))
      (.seq (.bind 28 "c" (.capture (.call 49 51)))
        (guards (.label "argcode" none (.ahead (.terminal 29)))))) := rfl

#print axioms invariant2_parameter_guard_order
end PegHs.MetaExecution
