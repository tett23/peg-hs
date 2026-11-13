import SelfHostedFileProof
import TerminalCursor
import StrictWhitespaceScan

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

private def delimiterRanges := [(',', ','), (')', ')')]

def parameterDelimiterReply (suffix : List Char) (env : Env) : Reply :=
  if suffix.head?.any (ConcreteTerminal.classHas delimiterRanges) then .ok suffix.length env
  else .throwLabel suffix.length "argcode" none

set_option maxRecDepth 8192 in
theorem invariant2_parameter_delimiter (pre suffix : List Char) (env : Env) :
    Derives (context false (pre ++ suffix)) (.label "argcode" none (.ahead (.terminal 29)))
      suffix.length env (parameterDelimiterReply suffix env) := by
  let ctx := context false (pre ++ suffix)
  have term : ctx.terms 29 = some (.cls delimiterRanges) := rfl
  have src : ctx.input = pre ++ suffix := rfl
  apply invariant1_runFuel_sound (fuel := 3)
  change runFuel ctx 3 _ _ _ = _
  simp only [runFuel, term, src, ConcreteTerminal.invariant1_oracle_suffix]
  cases suffix with
  | nil => rfl
  | cons c rest =>
    cases h : ConcreteTerminal.classHas delimiterRanges c <;>
      simp [ConcreteTerminal.matchTerm, parameterDelimiterReply, h]

private def bindHere (env : Env) : Env :=
  (({env with resultDepth := 0} : Env).put "l" []).putDepth "l" 0

set_option maxRecDepth 8192 in
private theorem parameter_here (input : List Char) (n : Nat) (env : Env) :
    Derives (context false input) (.bind 27 "l" (.call 48 3)) n env (.ok n (bindHere env)) := by
  let ctx := context false input
  have here : Derives ctx (ctx.rules 3) n env (.ok n {env with resultDepth := 0}) := Derives.eps
  have call : Derives ctx (.call 48 3) n env (.ok n {env with resultDepth := 0}) :=
    Derives.call (callee := env) (by rfl) here
  have bind := Derives.bind (site := 27) (name := "l") call
  have binds : ctx.hooks.bindValue 27 "l" [] {env with resultDepth := 0} = some (bindHere env) := rfl
  simpa only [bindResult, matchedText, Nat.sub_self, List.take_zero, binds] using bind

set_option maxRecDepth 8192 in
theorem invariant2_parameter_rule_reply (before xs pre suffix : List Char)
    (sameInput : before ++ xs = pre ++ suffix) (initial parsed : Env)
    (code : Derives (context false (pre ++ suffix)) (.call 49 51)
      (afterWhitespace xs).length (bindHere {initial with resultDepth := 0}) (.ok suffix.length parsed)) :
    let text := matchedText (pre ++ suffix) (afterWhitespace xs).length suffix.length
    let captured := (parsed.put "c" text).putDepth "c" parsed.resultDepth
    Derives (context false (pre ++ suffix)) translatedStrictParamChunk xs.length initial
      (if (ParameterPredicates.strip GhcPredicates.space text).isEmpty then
        .throwLabel suffix.length "argument" (some "expected an argument")
       else match ParameterPredicates.classify GhcPredicates.space GhcPredicates.alpha GhcPredicates.alnum text with
       | .formError => .throwLabel suffix.length "paramform" (some "expected a parameter of the form name :: Type")
       | .typeError => .throwLabel suffix.length "paramtype" (some "expected a parameter type")
       | .ok .. => parameterDelimiterReply suffix {captured with resultDepth := 0}) := by
  rw [invariant2_parameter_guard_shape]
  have scan := invariant1_strict_whitespace_scan before xs initial
  rw [sameInput] at scan
  have ws : Derives (context false (pre ++ suffix)) (.call 47 4) xs.length initial
      (.ok (afterWhitespace xs).length {initial with resultDepth := 0}) :=
    Derives.call (ctx := context false (pre ++ suffix)) (site := 47) (rule := 4) (env := initial) (callee := initial) (by rfl) scan
  apply Derives.seqOk ws
  apply Derives.seqOk (parameter_here _ _ _)
  let text := matchedText (pre ++ suffix) (afterWhitespace xs).length suffix.length
  let captured := (parsed.put "c" text).putDepth "c" parsed.resultDepth
  have bound : Derives (context false (pre ++ suffix)) (.bind 28 "c" (.capture (.call 49 51)))
      (afterWhitespace xs).length (bindHere {initial with resultDepth := 0}) (.ok suffix.length captured) :=
    Derives.bind (Derives.capture code)
  apply Derives.seqOk bound
  have h := invariant2_parameter_guard_order (pre ++ suffix) suffix.length captured _ _
    (invariant2_parameter_delimiter pre suffix _)
  obtain ⟨a, b, c⟩ := invariant2_parameter_capture_tests (pre ++ suffix) captured
  dsimp only at h ⊢
  rw [a, b, c] at h
  have lookup : captured.lookup "c" = text := rfl
  rw [lookup] at h
  cases empty : (ParameterPredicates.strip GhcPredicates.space text).isEmpty <;>
    cases result : ParameterPredicates.classify GhcPredicates.space GhcPredicates.alpha GhcPredicates.alnum
      text <;> simpa [← show text = matchedText (pre ++ suffix) (afterWhitespace xs).length suffix.length from rfl, empty, result] using h

set_option maxRecDepth 8192 in
theorem invariant2_parameter_code_throw (before xs : List Char) (initial : Env)
    (pos : Nat) (label : String) (msg : Option String)
    (code : Derives (context false (before ++ xs)) (.call 49 51)
      (afterWhitespace xs).length (bindHere {initial with resultDepth := 0}) (.throwLabel pos label msg)) :
    Derives (context false (before ++ xs)) translatedStrictParamChunk xs.length initial
      (.throwLabel pos label msg) := by
  let ctx := context false (before ++ xs)
  have scan := invariant1_strict_whitespace_scan before xs initial
  have ws : Derives ctx (.call 47 4) xs.length initial
      (.ok (afterWhitespace xs).length {initial with resultDepth := 0}) :=
    Derives.call (ctx := ctx) (site := 47) (rule := 4) (env := initial) (callee := initial) (by rfl) scan
  rw [invariant2_parameter_guard_shape]
  apply Derives.seqOk ws
  apply Derives.seqOk (parameter_here _ _ _)
  exact .seqCarryThrow (Derives.bind (Derives.capture code))

set_option maxRecDepth 8192 in
theorem invariant2_argcode_at_comma (pre tail : List Char) (env : Env) :
    let suffix := ',' :: tail
    Derives (context false (pre ++ suffix)) (.call 49 51) suffix.length env
      (.ok suffix.length {env with resultDepth := 0}) := by
  let suffix := ',' :: tail
  let ctx := context false (pre ++ suffix)
  let cleared := {env with resultDepth := 0}
  have term : ctx.terms 94 = some (.lit [',']) := rfl
  have src : ctx.input = pre ++ suffix := rfl
  have comma : runFuel ctx 1 (.terminal 94) suffix.length cleared =
      some (.ok tail.length {cleared with resultDepth := 0}) := by
    have hit : ConcreteTerminal.terminalOracle (.lit [',']) ctx.input suffix.length = some tail.length := by
      rw [src, ConcreteTerminal.invariant1_oracle_suffix]
      rfl
    simp only [runFuel, term, hit]
    simp [suffix]
  have stop : Derives ctx (.notAhead (.terminal 94)) suffix.length cleared .fail :=
    Derives.notAhead (invariant1_runFuel_sound comma)
  have body : Derives ctx (ctx.rules 51) suffix.length env (.ok suffix.length cleared) :=
    Derives.star (.loopStop (.seqCarryFail stop))
  exact Derives.call (ctx := ctx) (site := 49) (rule := 51) (env := env) (callee := env) (by rfl) body

theorem invariant2_empty_parameter_before_comma (before xs pre tail : List Char) (initial : Env)
    (sameInput : before ++ xs = pre ++ ',' :: tail)
    (comma : afterWhitespace xs = ',' :: tail) :
    Derives (context false (before ++ xs)) translatedStrictParamChunk xs.length initial
      (.throwLabel (',' :: tail).length "argument" (some "expected an argument")) := by
  let env := bindHere {initial with resultDepth := 0}
  have code := invariant2_argcode_at_comma pre tail env
  have full := invariant2_parameter_rule_reply before xs pre (',' :: tail) sameInput initial _
    (by simpa only [comma] using code)
  rw [sameInput]
  simpa [comma, matchedText, ParameterPredicates.strip] using full

private theorem loop_ne_fail (ctx : Inputs) (body : Body) (n : Nat) (env : Env) :
    ¬ Derives ctx (.starLoop body) n env .fail := by
  induction n using Nat.strongRecOn generalizing env with
  | ind n ih =>
    intro evaluated
    cases evaluated with
    | loopMore step smaller rest => exact ih _ smaller _ rest

set_option maxRecDepth 8192 in
theorem invariant2_argcode_ne_fail (input : List Char) (n : Nat) (env : Env) :
    ¬ Derives (context false input) (.call 49 51) n env .fail := by
  intro evaluated
  generalize eq : Reply.fail = reply at evaluated
  cases evaluated with
  | callMissing missing =>
    have enter : (context false input).hooks.enterCall 49 env = some env := rfl
    simp [enter] at missing
  | call enter body =>
    rename_i inner
    cases inner <;> try contradiction
    change Derives _ (.star _) _ _ .fail at body
    cases body with
    | star loop => exact loop_ne_fail _ _ _ _ loop

#print axioms invariant2_argcode_ne_fail
#print axioms invariant2_empty_parameter_before_comma
#print axioms invariant2_argcode_at_comma
#print axioms invariant2_parameter_code_throw
#print axioms invariant2_parameter_rule_reply
#print axioms invariant2_parameter_capture_tests
#print axioms invariant2_parameter_guard_order
end PegHs.MetaExecution
