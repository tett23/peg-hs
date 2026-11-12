import SelfHostedFileProof
import TerminalCursor

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

private def nonNewline (newline anyChar : Nat) : Body := .seq (.notAhead (.terminal newline)) (.terminal anyChar)

private theorem line_step (input pre suffix : List Char) (env : Env)
    {newline anyChar : Nat}
    (nl : (context false input).terms newline = some (.lit ['\n']))
    (any : (context false input).terms anyChar = some .any)
    (cursor : input = pre ++ suffix) :
    runFuel (context false input) 4 (nonNewline newline anyChar) suffix.length env = some
      (match suffix with
       | [] => .fail
       | c :: tail => if c = '\n' then .fail else .ok tail.length {env with resultDepth := 0}) := by
  let ctx := context false input
  change ctx.terms newline = _ at nl
  change ctx.terms anyChar = _ at any
  have src : ctx.input = pre ++ suffix := cursor
  have oracle (term : Terminal) := invariant1_oracle_at_cursor (term := term) src
    (remaining := suffix.length) rfl
  change runFuel ctx 4 (nonNewline newline anyChar) suffix.length env = _
  cases suffix with
  | nil =>
    simp only [List.length_nil] at oracle
    simp [nonNewline, runFuel, nl, any, oracle, matchTerm, matchLiteral]
  | cons c tail =>
    simp only [List.length_cons] at oracle
    by_cases h : c = '\n'
    · subst c
      simp [nonNewline, runFuel, nl, oracle, matchTerm, matchLiteral]
    · have ne := Ne.symm h
      simp [nonNewline, runFuel, nl, any, oracle, matchTerm, matchLiteral, h, ne]

private theorem line_loop (input suffix pre : List Char) (env : Env)
    {newline anyChar : Nat}
    (nl : (context false input).terms newline = some (.lit ['\n']))
    (any : (context false input).terms anyChar = some .any)
    (cursor : input = pre ++ suffix) (zero : env.resultDepth = 0) :
    Derives (context false input) (.starLoop (nonNewline newline anyChar)) suffix.length env
      (.ok (suffix.dropWhile (· != '\n')).length env) := by
  induction suffix generalizing pre with
  | nil =>
    exact .loopStop (invariant1_runFuel_sound (line_step input pre [] env nl any cursor))
  | cons c tail ih =>
    have step := line_step input pre (c :: tail) env nl any cursor
    by_cases same : c = '\n'
    · subst c
      simp only [ite_true] at step
      exact .loopStop (invariant1_runFuel_sound step)
    · simp only [same, ite_false] at step
      have reset : {env with resultDepth := 0} = env := by cases env; simp_all
      rw [reset] at step
      have next := ih (pre ++ [c]) (by simpa using cursor)
      rw [List.dropWhile_cons_of_pos (p := (· != '\n')) (show (c != '\n') = true by simp [same])]
      apply Derives.loopMore (invariant1_runFuel_sound step) (Nat.lt_succ_self _)
      simpa using next

theorem invariant1_directive_argument_scan (pre xs : List Char) (env : Env) :
    Derives (context false (pre ++ xs)) (.capture (.star (.seq (.notAhead (.terminal 13)) (.terminal 14))))
      xs.length env (.ok (xs.dropWhile (· != '\n')).length {env with resultDepth := 0}) :=
  .capture (.star (line_loop _ xs pre _ (newline := 13) (anyChar := 14) rfl rfl rfl rfl))

theorem invariant1_strict_comment (pre text : List Char) (env : Env) :
    let input := pre ++ '#' :: text
    Derives (context false input) translatedStrictComment ('#' :: text).length env
      (.ok (text.dropWhile (· != '\n')).length {env with resultDepth := 0}) := by
  dsimp only
  let ctx := context false (pre ++ '#' :: text)
  have hash : ctx.terms 2 = some (.lit ['#']) := rfl
  have src : ctx.input = pre ++ '#' :: text := rfl
  have term : runFuel ctx 1 (.terminal 2) ('#' :: text).length env =
      some (.ok text.length {env with resultDepth := 0}) := by
    have step := invariant1_oracle_suffix (.lit ['#']) pre ('#' :: text)
    simp [matchTerm, matchLiteral] at step
    simp [runFuel, hash, src, step]
  exact .seqOk (invariant1_runFuel_sound term) (.star
    (line_loop _ text (pre ++ ['#']) {env with resultDepth := 0} (newline := 3) (anyChar := 4) rfl rfl (by simp) rfl))

theorem invariant1_strict_comment_missing_hash (pre suffix : List Char) (env : Env)
    (missing : suffix.head? ≠ some '#') :
    Derives (context false (pre ++ suffix)) translatedStrictComment suffix.length env .fail := by
  let ctx := context false (pre ++ suffix)
  have hash : ctx.terms 2 = some (.lit ['#']) := rfl
  have src : ctx.input = pre ++ suffix := rfl
  have step := invariant1_oracle_at_cursor (term := .lit ['#']) src
    (remaining := suffix.length) rfl
  have rejected : matchTerm (.lit ['#']) suffix = none := by
    cases suffix with
    | nil => rfl
    | cons c cs =>
      have different : '#' ≠ c := by intro h; subst c; exact missing rfl
      simp [matchTerm, matchLiteral, different]
  rw [rejected] at step
  have failed : runFuel ctx 1 (.terminal 2) suffix.length env = some .fail := by
    simp only [runFuel, hash, step, Option.map_none]
  exact .seqCarryFail (invariant1_runFuel_sound failed)

#print axioms invariant1_strict_comment_missing_hash
#print axioms invariant1_strict_comment
end PegHs.MetaExecution
