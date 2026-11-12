import MetaExecution
import TerminalCursor

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

def verbatimEnd : List Char → Bool
  | a :: b :: _ => a == '}' && b == '%'
  | _ => false

def verbatimRest : List Char → List Char
  | [] => []
  | c :: cs => if verbatimEnd (c :: cs) then c :: cs else verbatimRest cs

def verbatimChar (mode : Bool) : Body :=
  .seq (.notAhead (.terminal (if mode then 10 else 9))) (.terminal (if mode then 11 else 10))

private theorem one (mode : Bool) (input pre xs : List Char) (env : Env)
    (cursor : input = pre ++ xs) :
    runFuel (context mode input) 4 (verbatimChar mode) xs.length env = some
      (match xs with
       | [] => .fail
       | c :: cs => if verbatimEnd (c :: cs) then .fail else .ok cs.length {env with resultDepth := 0}) := by
  let ctx := context mode input
  have close : ctx.terms (if mode then 10 else 9) = some (.lit ['}', '%']) := by cases mode <;> rfl
  have any : ctx.terms (if mode then 11 else 10) = some .any := by cases mode <;> rfl
  have source : ctx.input = pre ++ xs := by rw [← cursor]; cases mode <;> rfl
  have oracle (term : Terminal) := invariant1_oracle_at_cursor (term := term) source (remaining := xs.length) rfl
  change runFuel ctx 4 (verbatimChar mode) xs.length env = _
  cases xs with
  | nil =>
    simp only [List.length_nil] at oracle
    simp [verbatimChar, runFuel, close, any, oracle, matchTerm, matchLiteral]
  | cons a xs =>
    cases xs with
    | nil =>
      simp only [List.length_cons, List.length_nil] at oracle
      by_cases h : a = '}'
      · subst a; simp [verbatimChar, verbatimEnd, runFuel, close, any, oracle, matchTerm, matchLiteral]
      · have ne := Ne.symm h
        simp [verbatimChar, verbatimEnd, runFuel, close, any, oracle, matchTerm, matchLiteral, ne]
    | cons b cs =>
      simp only [List.length_cons] at oracle
      by_cases ha : a = '}'
      · subst a
        by_cases hb : b = '%'
        · subst b; simp [verbatimChar, verbatimEnd, runFuel, close, oracle, matchTerm, matchLiteral, show cs.length < cs.length + 1 + 1 by omega]
        · have ne := Ne.symm hb
          simp [verbatimChar, verbatimEnd, runFuel, close, any, oracle, matchTerm, matchLiteral, hb, ne]
      · have ne := Ne.symm ha
        simp [verbatimChar, verbatimEnd, runFuel, close, any, oracle, matchTerm, matchLiteral, ha, ne]

private theorem scanLoop (mode : Bool) (input pre xs : List Char) (env : Env)
    (cursor : input = pre ++ xs) (zero : env.resultDepth = 0) :
    Derives (context mode input) (.starLoop (verbatimChar mode)) xs.length env
      (.ok (verbatimRest xs).length env) := by
  induction xs generalizing pre with
  | nil => exact .loopStop (invariant1_runFuel_sound (one mode input pre [] env cursor))
  | cons c cs ih =>
    have step := one mode input pre (c :: cs) env cursor
    cases h : verbatimEnd (c :: cs) with
    | true =>
      simpa [verbatimRest, h] using Derives.loopStop (invariant1_runFuel_sound (by simpa [h] using step))
    | false =>
      have reset : {env with resultDepth := 0} = env := by cases env; simp_all
      simp only [h, Bool.false_eq_true, ite_false, reset] at step
      rw [verbatimRest]; simp only [h, Bool.false_eq_true, ite_false]
      apply Derives.loopMore (invariant1_runFuel_sound step) (Nat.lt_succ_self _)
      simpa using ih (pre ++ [c]) (by simpa using cursor)

theorem invariant1_verbatim_scan (mode : Bool) (pre xs : List Char) (env : Env) :
    Derives (context mode (pre ++ xs)) (.star (verbatimChar mode)) xs.length env
      (.ok (verbatimRest xs).length {env with resultDepth := 0}) :=
  .star (scanLoop mode _ pre xs _ rfl rfl)

-- Connect the two sets of site numbers to the body extracted from each file.
theorem invariant1_verbatim_rule_shape (mode : Bool) (input : List Char) :
    (context mode input).rules 11 =
      .seq (.terminal (if mode then 9 else 8))
        (.seq (.bind 3 "l" (.call 11 3))
          (.seq (.bind 4 "b" (.capture (.star (verbatimChar mode))))
            (.label "verbatim" (some "unterminated %{ block") (.terminal (if mode then 12 else 11))))) := by
  cases mode <;> rfl

#print axioms invariant1_verbatim_scan
end PegHs.MetaExecution
