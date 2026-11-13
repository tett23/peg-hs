import SelfHostedFileProof
import TerminalCursor
import StrictWhitespaceScan
import DirectiveFailure
import StrictIdentifier
import StrictWhitespaceLexical

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

set_option maxRecDepth 8192 in
theorem invariant2_argcode_outcomes (input : List Char) (n : Nat) (env : Env) :
    (∃ rest next, rest ≤ n ∧ Derives (context false input) (.call 49 51) n env (.ok rest next)) ∨
    (∃ pos name msg, Derives (context false input) (.call 49 51) n env (.throwLabel pos name msg)) := by
  let ctx := context false input
  obtain ⟨fuel, reply, observed⟩ := invariant1_actual_environment_total false ctx rfl (n, 51) env
  have call := Derives.call (ctx := ctx) (site := 49) (rule := 51) (env := env) (callee := env)
    (by rfl) (invariant1_runFuel_sound observed)
  cases reply with
  | fail => exact False.elim (invariant2_argcode_ne_fail input n env call)
  | ok rest inner =>
    exact .inl ⟨rest, _, invariant1_success_remaining_le call rest _ rfl, call⟩
  | throwLabel pos name msg => exact .inr ⟨pos, name, msg, call⟩

theorem invariant2_parameter_outcomes (before xs : List Char) (initial : Env) :
    ∃ reply, Derives (context false (before ++ xs)) translatedStrictParamChunk xs.length initial reply ∧
      reply ≠ .fail := by
  let input := before ++ xs
  let env := bindHere {initial with resultDepth := 0}
  rcases invariant2_argcode_outcomes input (afterWhitespace xs).length env with
    ⟨rest, parsed, bound, code⟩ | ⟨pos, label, msg, code⟩
  · have scan := invariant1_strict_whitespace_scan before xs initial
    have le := invariant1_success_remaining_le scan _ _ rfl
    have within : rest ≤ input.length := by simp [input]; omega
    let k := input.length - rest
    have splitInput : before ++ xs = input.take k ++ input.drop k := (List.take_append_drop k input).symm
    have len : (input.drop k).length = rest := by simp [k]; omega
    have adapted : Derives (context false (input.take k ++ input.drop k)) (.call 49 51)
        (afterWhitespace xs).length env (.ok (input.drop k).length parsed) := by
      rw [← splitInput, len]; exact code
    have full := invariant2_parameter_rule_reply before xs _ _ splitInput initial parsed adapted
    rw [← splitInput] at full
    refine ⟨_, full, ?_⟩
    split
    · simp
    · split <;> try simp
      unfold parameterDelimiterReply
      split <;> simp
  · exact ⟨_, invariant2_parameter_code_throw before xs initial pos label msg code, by simp⟩

set_option maxRecDepth 8192 in
theorem invariant2_parameter_chunks_throw (input : List Char) (n pos : Nat) (env : Env)
    (label : String) (msg : Option String)
    (chunk : Derives (context false input) translatedStrictParamChunk n env (.throwLabel pos label msg)) :
    Derives (context false input) translatedStrictParamChunks n env (.throwLabel pos label msg) := by
  let ctx := context false input
  have call : Derives ctx (.call 44 19) n env (.throwLabel pos label msg) :=
    Derives.call (ctx := ctx) (site := 44) (rule := 19) (env := env) (callee := env) (by rfl) chunk
  exact .altLeft (.seqCarryThrow (Derives.bind call)) (by simp)

set_option maxRecDepth 8192 in
theorem invariant1_parameter_list_reply (before xs : List Char) (initial : Env) (reply : Reply)
    (chunks : Derives (context false (before ++ '(' :: xs)) translatedStrictParamChunks xs.length
      {initial with resultDepth := 0} reply) :
    Derives (context false (before ++ '(' :: xs)) translatedStrictParamList ('(' :: xs).length initial
      (callResult (context false (before ++ '(' :: xs)) 43 {initial with resultDepth := 0} reply) := by
  let ctx := context false (before ++ '(' :: xs)
  let next := {initial with resultDepth := 0}
  have openTerm : ctx.terms 26 = some (.lit ['(']) := rfl
  have hit : ConcreteTerminal.terminalOracle (.lit ['(']) ctx.input ('(' :: xs).length = some xs.length := by
    change ConcreteTerminal.terminalOracle _ (before ++ '(' :: xs) _ = _
    rw [ConcreteTerminal.invariant1_oracle_suffix]
    rfl
  have openStep : runFuel ctx 1 (.terminal 26) ('(' :: xs).length initial = some (.ok xs.length next) := by
    simp only [runFuel, openTerm, hit]
    simp [next]
  apply Derives.seqOk (invariant1_runFuel_sound openStep)
  exact Derives.call (ctx := ctx) (site := 43) (rule := 18) (env := next) (callee := next) (by rfl) chunks

theorem invariant2_parameter_list_throw (before xs : List Char) (initial : Env)
    (pos : Nat) (label : String) (msg : Option String)
    (chunks : Derives (context false (before ++ '(' :: xs)) translatedStrictParamChunks xs.length
      {initial with resultDepth := 0} (.throwLabel pos label msg)) :
    Derives (context false (before ++ '(' :: xs)) translatedStrictParamList ('(' :: xs).length initial
      (.throwLabel pos label msg) := by
  exact invariant1_parameter_list_reply before xs initial _ chunks

theorem invariant2_parameter_list_first_throw (before xs : List Char) (initial : Env)
    (pos : Nat) (label : String) (msg : Option String)
    (chunk : Derives (context false (before ++ '(' :: xs)) translatedStrictParamChunk xs.length
      {initial with resultDepth := 0} (.throwLabel pos label msg)) :
    Derives (context false (before ++ '(' :: xs)) translatedStrictParamList ('(' :: xs).length initial
      (.throwLabel pos label msg) := by
  exact invariant2_parameter_list_throw before xs initial pos label msg
    (invariant2_parameter_chunks_throw _ _ _ _ _ _ chunk)

theorem invariant2_parameter_list_empty_first (before xs pre tail : List Char) (initial : Env)
    (sameInput : (before ++ ['(']) ++ xs = pre ++ ',' :: tail)
    (comma : afterWhitespace xs = ',' :: tail) :
    Derives (context false (before ++ '(' :: xs)) translatedStrictParamList ('(' :: xs).length initial
      (.throwLabel (',' :: tail).length "argument" (some "expected an argument")) := by
  apply invariant2_parameter_list_first_throw
  simpa only [List.append_assoc, List.singleton_append] using
    invariant2_empty_parameter_before_comma (before ++ ['(']) xs pre tail {initial with resultDepth := 0} sameInput comma

set_option maxRecDepth 8192 in
private theorem parameter_comma (pre tail : List Char) (bound : Env) :
    runFuel (context false (pre ++ ',' :: tail)) 1 (.terminal 27) (',' :: tail).length bound =
      some (.ok tail.length {bound with resultDepth := 0}) := by
  let ctx := context false (pre ++ ',' :: tail)
  have term : ctx.terms 27 = some (.lit [',']) := rfl
  have hit : ConcreteTerminal.terminalOracle (.lit [',']) ctx.input (',' :: tail).length = some tail.length := by
    change ConcreteTerminal.terminalOracle _ (pre ++ ',' :: tail) _ = _
    rw [ConcreteTerminal.invariant1_oracle_suffix]
    rfl
  change runFuel ctx 1 _ _ _ = _
  simp only [runFuel, term, hit]
  simp

set_option maxRecDepth 8192 in
theorem invariant2_parameter_chunks_tail_throw (pre tail : List Char) (start pos : Nat)
    (env bound : Env) (label : String) (msg : Option String)
    (first : Derives (context false (pre ++ ',' :: tail)) (.bind 24 "p" (.call 44 19))
      start env (.ok (',' :: tail).length bound))
    (rest : Derives (context false (pre ++ ',' :: tail)) translatedStrictParamChunks tail.length
      {bound with resultDepth := 0} (.throwLabel pos label msg)) :
    Derives (context false (pre ++ ',' :: tail)) translatedStrictParamChunks start env
      (.throwLabel pos label msg) := by
  let ctx := context false (pre ++ ',' :: tail)
  let next := {bound with resultDepth := 0}
  have call : Derives ctx (.call 45 18) tail.length next (.throwLabel pos label msg) :=
    Derives.call (ctx := ctx) (site := 45) (rule := 18) (env := next) (callee := next) (by rfl) rest
  exact .altLeft (.seqOk first (.seqOk (invariant1_runFuel_sound (parameter_comma pre tail bound)) (Derives.bind call))) (by simp)

set_option maxRecDepth 8192 in
theorem invariant1_parameter_chunks_tail_success (pre tail : List Char) (start stop : Nat)
    (env bound inner : Env)
    (first : Derives (context false (pre ++ ',' :: tail)) (.bind 24 "p" (.call 44 19))
      start env (.ok (',' :: tail).length bound))
    (rest : Derives (context false (pre ++ ',' :: tail)) translatedStrictParamChunks tail.length
      {bound with resultDepth := 0} (.ok stop inner)) :
    ∃ finalEnv, Derives (context false (pre ++ ',' :: tail)) translatedStrictParamChunks start env
      (.ok stop finalEnv) := by
  let ctx := context false (pre ++ ',' :: tail)
  let next := {bound with resultDepth := 0}
  have call : Derives ctx (.call 45 18) tail.length next (.ok stop {next with resultDepth := inner.resultDepth}) :=
    Derives.call (ctx := ctx) (site := 45) (rule := 18) (env := next) (callee := next) (by rfl) rest
  exact ⟨_, .altLeft (.seqOk first (.seqOk (invariant1_runFuel_sound (parameter_comma pre tail bound)) (Derives.bind call))) (by simp)⟩

set_option maxRecDepth 8192 in
theorem invariant1_parameter_chunks_last (pre tail : List Char) (start : Nat) (env inner : Env)
    (chunk : Derives (context false (pre ++ ')' :: tail)) translatedStrictParamChunk start env
      (.ok (')' :: tail).length inner)) :
    ∃ finalEnv, Derives (context false (pre ++ ')' :: tail)) translatedStrictParamChunks start env
      (.ok tail.length finalEnv) := by
  let ctx := context false (pre ++ ')' :: tail)
  let n := (')' :: tail).length
  let caller := {env with resultDepth := inner.resultDepth}
  let bound := (caller.put "p" (matchedText ctx.input start n)).putDepth "p" caller.resultDepth
  have first : Derives ctx (.bind 24 "p" (.call 44 19)) start env (.ok n bound) :=
    Derives.bind (Derives.call (ctx := ctx) (site := 44) (rule := 19) (env := env) (callee := env) (by rfl) chunk)
  have last : Derives ctx (.bind 26 "p" (.call 46 19)) start env (.ok n bound) :=
    Derives.bind (Derives.call (ctx := ctx) (site := 46) (rule := 19) (env := env) (callee := env) (by rfl) chunk)
  have comma : ctx.terms 27 = some (.lit [',']) := rfl
  have close : ctx.terms 28 = some (.lit [')']) := rfl
  have oracle (c : Char) : ConcreteTerminal.terminalOracle (.lit [c]) ctx.input n =
      (ConcreteTerminal.matchTerm (.lit [c]) (')' :: tail)).map List.length :=
    ConcreteTerminal.invariant1_oracle_suffix _ pre _
  have miss : ConcreteTerminal.terminalOracle (.lit [',']) ctx.input n = none := (oracle ',').trans rfl
  have hit : ConcreteTerminal.terminalOracle (.lit [')']) ctx.input n = some tail.length := (oracle ')').trans rfl
  have retry : runFuel ctx 1 (.terminal 27) n bound = some .fail := by simp only [runFuel, comma, miss]
  have finish : runFuel ctx 1 (.terminal 28) n bound = some (.ok tail.length {bound with resultDepth := 0}) := by
    simp only [runFuel, close, hit]
    simp [n]
  exact ⟨_, .altRetry (.seqOk first (.seqCarryFail (invariant1_runFuel_sound retry)))
    (.seqOk last (invariant1_runFuel_sound finish))⟩

set_option maxRecDepth 8192 in
theorem invariant1_parameter_list_absent (before xs : List Char) (initial : Env)
    (absent : xs.head? ≠ some '(') :
    Derives (context false (before ++ xs)) translatedStrictParamList xs.length initial .fail := by
  let ctx := context false (before ++ xs)
  have term : ctx.terms 26 = some (.lit ['(']) := rfl
  have missing : ConcreteTerminal.matchTerm (.lit ['(']) xs = none := by
    cases xs with
    | nil => rfl
    | cons c cs =>
      have ne : '(' ≠ c := by intro eq; subst c; exact absent rfl
      simp [ConcreteTerminal.matchTerm, ConcreteTerminal.matchLiteral, ne]
  have miss := ConcreteTerminal.invariant1_oracle_suffix (.lit ['(']) before xs
  rw [missing] at miss
  have run : runFuel ctx 1 (.terminal 26) xs.length initial = some .fail := by
    have src : ctx.input = before ++ xs := rfl
    simp only [runFuel, term, src, miss, Option.map_none]
  exact .seqCarryFail (invariant1_runFuel_sound run)

set_option maxRecDepth 8192 in
theorem invariant1_declaration_optional_parameters_absent (before xs : List Char) (env : Env)
    (absent : xs.head? ≠ some '(') :
    let ctx := context false (before ++ xs)
    let next := Reply.ok xs.length {env with resultDepth := 0}
    Derives ctx (.alt (.bind 12 "ps" (.call 19 17)) .eps) xs.length env next ∧
      Derives ctx (.alt (.call 31 17) .eps) xs.length env next := by
  let ctx := context false (before ++ xs)
  have missing := invariant1_parameter_list_absent before xs env absent
  have annotation : Derives ctx (.call 19 17) xs.length env .fail :=
    Derives.call (ctx := ctx) (site := 19) (rule := 17) (env := env) (callee := env) (by rfl) missing
  have fallback : Derives ctx (.call 31 17) xs.length env .fail :=
    Derives.call (ctx := ctx) (site := 31) (rule := 17) (env := env) (callee := env) (by rfl) missing
  exact ⟨.altRetry (Derives.bind annotation) .eps, .altRetry fallback .eps⟩

set_option maxRecDepth 8192 in
theorem invariant2_declaration_optional_parameters_throw (input : List Char) (n pos : Nat) (env : Env)
    (label : String) (msg : Option String)
    (bad : Derives (context false input) translatedStrictParamList n env (.throwLabel pos label msg)) :
    let ctx := context false input
    let err := Reply.throwLabel pos label msg
    Derives ctx (.alt (.bind 12 "ps" (.call 19 17)) .eps) n env err ∧
      Derives ctx (.alt (.call 31 17) .eps) n env err := by
  let ctx := context false input
  have annotation : Derives ctx (.call 19 17) n env (.throwLabel pos label msg) :=
    Derives.call (ctx := ctx) (site := 19) (rule := 17) (env := env) (callee := env) (by rfl) bad
  have fallback : Derives ctx (.call 31 17) n env (.throwLabel pos label msg) :=
    Derives.call (ctx := ctx) (site := 31) (rule := 17) (env := env) (callee := env) (by rfl) bad
  exact ⟨.altLeft (Derives.bind annotation) (by simp), .altLeft fallback (by simp)⟩

set_option maxRecDepth 8192 in
theorem invariant2_declaration_parameter_throw (input : List Char) (start named params pos : Nat)
    (initial located nameEnv paramEnv : Env) (label : String) (msg : Option String)
    (here : Derives (context false input) (.bind 9 "l" (.call 16 3)) start initial (.ok start located))
    (name : Derives (context false input) (.bind 10 "n" (.call 17 8)) start located (.ok named nameEnv))
    (templates : Derives (context false input) (.alt (.bind 11 "tps" (.call 18 14)) .eps)
      named nameEnv (.ok params paramEnv))
    (bad : Derives (context false input) translatedStrictParamList params paramEnv (.throwLabel pos label msg)) :
    Derives (context false input) translatedStrictDeclaration start initial (.throwLabel pos label msg) := by
  have parameter := (invariant2_declaration_optional_parameters_throw input params pos paramEnv label msg bad).1
  exact .altLeft (.seqOk here (.seqOk name (.seqOk templates (.seqCarryThrow parameter)))) (by simp)

set_option maxRecDepth 8192 in
theorem invariant1_declaration_name (pre : List Char) (c : Char) (cs : List Char) (env : Env)
    (valid : CharRule.identStart.accepts c = true) :
    let ctx := context false (pre ++ c :: cs)
    let n := (c :: cs).length
    let located := bindHere env
    let text := c :: cs.takeWhile CharRule.identChar.accepts
    Derives ctx (.bind 9 "l" (.call 16 3)) n env (.ok n located) ∧
      Derives ctx (.bind 10 "n" (.call 17 8)) n located
        (.ok (cs.dropWhile CharRule.identChar.accepts).length ((located.put "n" text).putDepth "n" 0)) := by
  let ctx := context false (pre ++ c :: cs)
  let n := (c :: cs).length
  have here : Derives ctx (ctx.rules 3) n env (.ok n {env with resultDepth := 0}) := Derives.eps
  have called : Derives ctx (.call 16 3) n env (.ok n {env with resultDepth := 0}) :=
    Derives.call (callee := env) (by rfl) here
  have position := Derives.bind (site := 9) (name := "l") called
  simp only [bindResult, matchedText, Nat.sub_self, List.take_zero] at position
  refine ⟨position, ?_⟩
  have parsed := invariant1_strict_identifier pre (c :: cs) (bindHere env)
  simp only [valid, ite_true] at parsed
  have name := Derives.call (ctx := ctx) (site := 17) (rule := 8) (env := bindHere env)
    (callee := bindHere env) (by rfl) parsed
  have bound := Derives.bind (site := 10) (name := "n") name
  change Derives ctx _ _ _ (.ok _ (((bindHere env).put "n"
    (matchedText (pre ++ c :: cs) (c :: cs).length (cs.dropWhile CharRule.identChar.accepts).length)).putDepth "n" 0)) at bound
  rw [invariant1_identifier_capture] at bound
  exact bound

set_option maxRecDepth 8192 in
private theorem templates_before_parameters (pre xs : List Char) (env : Env) :
    Derives (context false (pre ++ '(' :: xs)) (.alt (.bind 11 "tps" (.call 18 14)) .eps)
      ('(' :: xs).length env (.ok ('(' :: xs).length {env with resultDepth := 0}) := by
  let ctx := context false (pre ++ '(' :: xs)
  have term : ctx.terms 20 = some (.lit ['<']) := rfl
  have miss : ConcreteTerminal.terminalOracle (.lit ['<']) ctx.input ('(' :: xs).length = none := by
    change ConcreteTerminal.terminalOracle _ (pre ++ '(' :: xs) _ = _
    rw [ConcreteTerminal.invariant1_oracle_suffix]
    rfl
  have failed : runFuel ctx 1 (.terminal 20) ('(' :: xs).length env = some .fail := by
    simp only [runFuel, term, miss]
  have body : Derives ctx (ctx.rules 14) ('(' :: xs).length env .fail :=
    .seqCarryFail (invariant1_runFuel_sound failed)
  have call : Derives ctx (.call 18 14) ('(' :: xs).length env .fail :=
    Derives.call (callee := env) (by rfl) body
  exact .altRetry (Derives.bind call) .eps

theorem invariant2_declaration_empty_parameter (pre : List Char) (c : Char) (cs xs tail : List Char)
    (env : Env) (valid : CharRule.identStart.accepts c = true)
    (afterName : cs.dropWhile CharRule.identChar.accepts = '(' :: xs)
    (comma : afterWhitespace xs = ',' :: tail) :
    Derives (context false (pre ++ c :: cs)) translatedStrictDeclaration (c :: cs).length env
      (.throwLabel (',' :: tail).length "argument" (some "expected an argument")) := by
  obtain ⟨ws, suffix⟩ := afterWhitespace_suffix xs
  have splitXs := suffix.symm
  rw [comma] at splitXs
  obtain ⟨here, name⟩ := invariant1_declaration_name pre c cs env valid
  rw [afterName] at name
  let namePrefix := pre ++ c :: cs.takeWhile CharRule.identChar.accepts
  have splitInput : pre ++ c :: cs = namePrefix ++ '(' :: xs := by
    simp [namePrefix, List.append_assoc, ← afterName]
  apply invariant2_declaration_parameter_throw _ _ _ _ _ _ _ _ _ _ _ here name
  · rw [splitInput]
    exact templates_before_parameters _ _ _
  · rw [splitInput]
    apply invariant2_parameter_list_empty_first namePrefix xs (((namePrefix ++ ['(']) ++ ws)) tail _ _ comma
    simp only [List.append_assoc, splitXs]

set_option maxRecDepth 8192 in
theorem invariant2_top_item_declaration_throw (pre : List Char) (c : Char) (cs : List Char)
    (ordinary : '%' ≠ c) (pos : Nat) (label : String) (msg : Option String)
    (decl : Derives (context false (pre ++ c :: cs)) translatedStrictDeclaration (c :: cs).length {}
      (.throwLabel pos label msg)) :
    Derives (context false (pre ++ c :: cs)) (.call 1 1) (c :: cs).length {} (.throwLabel pos label msg) := by
  let ctx := context false (pre ++ c :: cs)
  let n := (c :: cs).length
  let err := Reply.throwLabel pos label msg
  have miss (site : Nat) (tail : List Char) (env : Env)
      (term : ctx.terms site = some (.lit ('%' :: tail))) : Derives ctx (.terminal site) n env .fail := by
    have oracle := ConcreteTerminal.invariant1_oracle_suffix (.lit ('%' :: tail)) pre (c :: cs)
    simp [ConcreteTerminal.matchTerm, ConcreteTerminal.matchLiteral, ordinary] at oracle
    apply invariant1_runFuel_sound (fuel := 1)
    have src : ctx.input = pre ++ c :: cs := rfl
    simp [runFuel, term, src, n, oracle]
  have block : Derives ctx (ctx.rules 11) n {} .fail := .seqCarryFail (miss 8 ['{'] {} rfl)
  have here : Derives ctx (ctx.rules 3) n {} (.ok n {}) := Derives.eps
  have call : Derives ctx (.call 12 3) n {} (.ok n {}) := Derives.call (callee := {}) (by rfl) here
  have directive : Derives ctx (ctx.rules 12) n {} .fail :=
    .seqOk (Derives.bind call) (.seqCarryFail (miss 12 [] _ rfl))
  have one : Derives ctx (ctx.rules 2) n {} err :=
    .altRetry (Derives.call (callee := {}) (by rfl) block)
      (.altRetry (Derives.call (callee := {}) (by rfl) directive) (Derives.call (ctx := ctx) (site := 6) (rule := 13) (env := {}) (callee := {}) (by rfl) decl))
  have top : Derives ctx (.call 2 2) n {} err := Derives.call (callee := {}) (by rfl) one
  have item : Derives ctx (ctx.rules 1) n {} err := .seqCarryThrow top
  exact Derives.call (callee := {}) (by rfl) item

theorem invariant2_file_empty_parameter (pre : List Char) (c : Char) (cs xs tail : List Char)
    (ends : List Nat) (valid : CharRule.identStart.accepts c = true) (ordinary : '%' ≠ c)
    (afterName : cs.dropWhile CharRule.identChar.accepts = '(' :: xs)
    (comma : afterWhitespace xs = ',' :: tail)
    (items : let input := pre ++ c :: cs
      ItemStepsTo (context false input) (c :: cs).length (afterWhitespace input).length ends) :
    FileResult false (pre ++ c :: cs) (.throwLabel (',' :: tail).length "argument" (some "expected an argument")) := by
  have decl := invariant2_declaration_empty_parameter pre c cs xs tail {} valid afterName comma
  exact file_item_throw _ _ ends items (invariant2_top_item_declaration_throw pre c cs ordinary _ _ _ decl)

#print axioms invariant2_file_empty_parameter
#print axioms invariant2_top_item_declaration_throw
#print axioms invariant2_declaration_empty_parameter
#print axioms invariant1_declaration_name
#print axioms invariant2_declaration_parameter_throw
#print axioms invariant2_declaration_optional_parameters_throw
#print axioms invariant1_declaration_optional_parameters_absent
#print axioms invariant1_parameter_list_absent
#print axioms invariant1_parameter_list_reply
#print axioms invariant1_parameter_chunks_tail_success
#print axioms invariant1_parameter_chunks_last
#print axioms invariant2_parameter_chunks_tail_throw
#print axioms invariant2_parameter_list_first_throw
#print axioms invariant2_parameter_list_empty_first
#print axioms invariant2_parameter_outcomes
#print axioms invariant2_argcode_outcomes
#print axioms invariant2_argcode_ne_fail
#print axioms invariant2_empty_parameter_before_comma
#print axioms invariant2_argcode_at_comma
#print axioms invariant2_parameter_code_throw
#print axioms invariant2_parameter_rule_reply
#print axioms invariant2_parameter_capture_tests
#print axioms invariant2_parameter_guard_order
end PegHs.MetaExecution
