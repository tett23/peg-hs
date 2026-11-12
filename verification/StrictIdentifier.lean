import StrictSpaceChar

namespace PegHs.MetaExecution
open EnvironmentEval
set_option maxRecDepth 8192

private def charCall (initial : Bool) : Body := if initial then .call 9 9 else .call 10 10
private def charRule (initial : Bool) : CharRule := if initial then .identStart else .identChar

private theorem ident_call (initial : Bool) (pre : List Char) (c : Char) (cs : List Char) (env : Env) :
    Derives (context false (pre ++ c :: cs)) (charCall initial) (c :: cs).length env
      (if (charRule initial).accepts c then .ok cs.length {env with resultDepth := 0} else .fail) := by
  let ctx := context false (pre ++ c :: cs)
  have step := invariant1_strict_char (charRule initial) pre c cs env
  dsimp only at step
  let site := if initial then 9 else 10
  have entered : ctx.hooks.enterCall site env = some env := by cases initial <;> rfl
  have body : (charRule initial).body = ctx.rules site := by cases initial <;> rfl
  rw [body] at step
  cases h : (charRule initial).accepts c <;> rw [h] at step
  all_goals
    have called := Derives.call (ctx := ctx) (rule := site) entered (invariant1_runFuel_sound step)
    cases initial <;> exact called

private theorem ident_call_eof (initial : Bool) (input : List Char) (env : Env) :
    Derives (context false input) (charCall initial) 0 env .fail := by
  let ctx := context false input
  let site := if initial then 9 else 10
  have entered : ctx.hooks.enterCall site env = some env := by cases initial <;> rfl
  have body : (charRule initial).body = ctx.rules site := by cases initial <;> rfl
  have step := invariant1_strict_char_eof (charRule initial) input env
  rw [body] at step
  have called := Derives.call (ctx := ctx) (rule := site) entered (invariant1_runFuel_sound step)
  cases initial <;> exact called

private theorem ident_tail (input pre cs : List Char) (env : Env)
    (cursor : input = pre ++ cs) (zero : env.resultDepth = 0) :
    Derives (context false input) (.starLoop (.call 10 10)) cs.length env
      (.ok (cs.dropWhile CharRule.identChar.accepts).length env) := by
  induction cs generalizing pre with
  | nil => exact .loopStop (ident_call_eof false input env)
  | cons c cs ih =>
    have call := ident_call false pre c cs env
    rw [← cursor] at call
    change Derives _ (.call 10 10) _ _ (if CharRule.identChar.accepts c then _ else _) at call
    cases h : CharRule.identChar.accepts c with
    | false =>
      rw [h] at call
      simpa [List.dropWhile, h] using Derives.loopStop call
    | true =>
      have reset : {env with resultDepth := 0} = env := by cases env; simp_all
      simp only [h, ite_true, reset] at call
      simp only [List.dropWhile_cons_of_pos h]
      apply Derives.loopMore call (Nat.lt_succ_self _)
      simpa using ih (pre ++ [c]) (by simpa using cursor)

theorem invariant1_strict_identifier (pre xs : List Char) (env : Env) :
    Derives (context false (pre ++ xs)) translatedStrictIdent xs.length env
      (match xs with
       | [] => .fail
       | c :: cs => if CharRule.identStart.accepts c then
           .ok (cs.dropWhile CharRule.identChar.accepts).length {env with resultDepth := 0}
         else .fail) := by
  apply Derives.capture
  cases xs with
  | nil => exact .seqCarryFail (ident_call_eof true _ env)
  | cons c cs =>
    have call := ident_call true pre c cs env
    change Derives _ (.call 9 9) _ _ (if CharRule.identStart.accepts c then _ else _) at call
    cases h : CharRule.identStart.accepts c with
    | false =>
      simp only [h, Bool.false_eq_true, ite_false] at call ⊢
      exact .seqCarryFail call
    | true =>
      simp only [h, ite_true] at call ⊢
      exact .seqOk call (.star (ident_tail (pre ++ c :: cs) (pre ++ [c]) cs _ (by simp) rfl))

-- The capture primitive returns the consumed text at a successful endpoint.
theorem invariant1_identifier_capture (pre : List Char) (c : Char) (cs : List Char) :
    matchedText (pre ++ c :: cs) (c :: cs).length
        (cs.dropWhile CharRule.identChar.accepts).length =
      c :: cs.takeWhile CharRule.identChar.accepts := by
  let accepted := cs.takeWhile CharRule.identChar.accepts
  let suffix := cs.dropWhile CharRule.identChar.accepts
  have parts : accepted ++ suffix = cs := List.takeWhile_append_dropWhile
  have lengths := congrArg List.length parts
  simp only [List.length_append] at lengths
  have width : (c :: cs).length - suffix.length = (c :: accepted).length := by
    simp only [List.length_cons]; omega
  unfold matchedText
  change ((pre ++ c :: cs).drop ((pre ++ c :: cs).length - (c :: cs).length)).take
    ((c :: cs).length - suffix.length) = c :: accepted
  rw [width]
  simp only [List.length_append, Nat.add_sub_cancel, List.drop_left]
  conv => lhs; rw [← parts]
  change ((c :: accepted) ++ suffix).take (c :: accepted).length = _
  simp

#print axioms invariant1_identifier_capture
#print axioms invariant1_strict_identifier
end PegHs.MetaExecution
