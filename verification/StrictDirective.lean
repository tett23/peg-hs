import StrictIdentifier

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

theorem invariant1_translated_directive (input : List Char) :
    translatedStrictDirective = (context false input).rules 12 := rfl

private theorem missing_ident (pre xs : List Char) (env : Env)
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true) :
    Derives (context false (pre ++ xs)) translatedStrictIdent xs.length env .fail := by
  cases xs with
  | nil => exact invariant1_strict_identifier pre [] env
  | cons c cs =>
    have no : CharRule.identStart.accepts c = false := by simpa using bad
    simpa only [no, Bool.false_eq_true, ite_false] using invariant1_strict_identifier pre (c :: cs) env

theorem invariant2_directive_missing_name (pre xs : List Char) (env : Env)
    (bad : xs.head?.all (fun c => !(CharRule.identStart.accepts c)) = true) :
    let input := pre ++ '%' :: xs
    Derives (context false input) translatedStrictDirective (xs.length + 1) env
      (.throwLabel xs.length "ident" (some "expected an identifier")) := by
  let input := pre ++ '%' :: xs
  let ctx := context false input
  let n := xs.length + 1
  let cleared := {env with resultDepth := 0}
  let loc := (cleared.put "l" (matchedText input n n)).putDepth "l" 0
  have here : Derives ctx (ctx.rules 3) n env (.ok n cleared) := Derives.eps
  have ent : ctx.hooks.enterCall 12 env = some env := rfl
  have call : Derives ctx (.call 12 3) n env (.ok n cleared) := Derives.call ent here
  have bound : Derives ctx (.bind 5 "l" (.call 12 3)) n env (.ok n loc) :=
    Derives.bind call
  have term : ctx.terms 12 = some (.lit ['%']) := rfl
  have src : ctx.input = pre ++ '%' :: xs := rfl
  have oracle := invariant1_oracle_suffix (.lit ['%']) pre ('%' :: xs)
  simp [matchTerm, matchLiteral] at oracle
  have percent : runFuel ctx 1 (.terminal 12) n loc = some (.ok xs.length loc) := by
    simp [n, runFuel, term, src, oracle, loc, Env.putDepth, Env.put, cleared]
  have ident := missing_ident (pre ++ ['%']) xs loc bad
  have split : (pre ++ ['%']) ++ xs = input := by simp [input]
  rw [split] at ident
  have missing : Derives ctx (ctx.rules 8) xs.length loc .fail := ident
  have entered : ctx.hooks.enterCall 13 loc = some loc := rfl
  have failed : Derives ctx (.call 13 8) xs.length loc .fail := Derives.call entered missing
  have label := Derives.label (name := "ident") (msg := some "expected an identifier") failed
  exact .seqOk bound (.seqOk (invariant1_runFuel_sound percent)
    (.seqCarryThrow (Derives.bind (site := 6) (name := "n") label)))

#print axioms invariant2_directive_missing_name
end PegHs.MetaExecution
