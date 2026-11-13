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

theorem invariant2_parameter_capture_tests (input : List Char) (env : Env) :
    let ctx := context false input
    let next := {env with resultDepth := 0}
    let captured := env.lookup "c"
    let result := ParameterPredicates.classify GhcPredicates.space GhcPredicates.alpha
      GhcPredicates.alnum captured
    predicateTest ctx 4 env = some (!(ParameterPredicates.strip GhcPredicates.space captured).isEmpty) ∧
    predicateTest ctx 5 next = some (result != .formError) ∧
    predicateTest ctx 6 next = some (match result with | .ok .. => true | _ => false) := by
  dsimp only
  have site (i : Nat) (k : SemanticPredicates.Kind)
      (h : (context false input).sites i = some (k, true)) (e : Env) :
      predicateTest (context false input) i e =
        some (SemanticPredicates.eval GhcPredicates.classes k (PredicateBindings.predicateEnv k e)) := by
    unfold predicateTest
    simp only [h]
    change some (SemanticPredicates.eval GhcPredicates.classes k
      (match (context false input).sites i with
      | some (kind, _) => PredicateBindings.predicateEnv kind e
      | none => {captured := [], depth := e.depth})) = _
    rw [h]
  rw [site 4 .argument (by change (context false []).sites 4 = _; decide +kernel), site 5 .paramForm (by change (context false []).sites 5 = _; decide +kernel),
    site 6 .paramType (by change (context false []).sites 6 = _; decide +kernel)]
  exact ⟨rfl, rfl, rfl⟩

theorem invariant2_parameter_rule_reply (input : List Char) (start here stop : Nat)
    (initial spaced located captured : Env) (r : Reply)
    (ws : Derives (context false input) (.call 47 4) start initial (.ok here spaced))
    (loc : Derives (context false input) (.bind 27 "l" (.call 48 3)) here spaced (.ok here located))
    (code : Derives (context false input) (.bind 28 "c" (.capture (.call 49 51)))
      here located (.ok stop captured))
    (delimiter : Derives (context false input) (.label "argcode" none (.ahead (.terminal 29)))
      stop {captured with resultDepth := 0} r) :
    let text := captured.lookup "c"
    Derives (context false input) translatedStrictParamChunk start initial
      (if (ParameterPredicates.strip GhcPredicates.space text).isEmpty then
        .throwLabel stop "argument" (some "expected an argument")
       else match ParameterPredicates.classify GhcPredicates.space GhcPredicates.alpha GhcPredicates.alnum text with
       | .formError => .throwLabel stop "paramform" (some "expected a parameter of the form name :: Type")
       | .typeError => .throwLabel stop "paramtype" (some "expected a parameter type")
       | .ok .. => r) := by
  rw [invariant2_parameter_guard_shape]
  apply Derives.seqOk ws
  apply Derives.seqOk loc
  apply Derives.seqOk code
  have h := invariant2_parameter_guard_order input stop captured _ r delimiter
  obtain ⟨a, b, c⟩ := invariant2_parameter_capture_tests input captured
  dsimp only at h ⊢
  rw [a, b, c] at h
  cases empty : (ParameterPredicates.strip GhcPredicates.space (captured.lookup "c")).isEmpty <;>
    cases result : ParameterPredicates.classify GhcPredicates.space GhcPredicates.alpha GhcPredicates.alnum
      (captured.lookup "c") <;> simpa [empty, result] using h

#print axioms invariant2_parameter_rule_reply
#print axioms invariant2_parameter_capture_tests
#print axioms invariant2_parameter_guard_order
end PegHs.MetaExecution
