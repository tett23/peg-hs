import WindowReplay
import PrefixReplay

namespace PegHs.EnvironmentEval
open ConcreteTerminal

-- Follow the same child calls as runFuel. A failed branch counts even if
-- ordered choice later succeeds, and both lookahead operators count reads.
def readsFit (ctx : Inputs) : Nat → Body → Nat → Env → Bool
  | 0, _, _, _ => false
  | f + 1, b, n, env =>
    match b with
    | .eps | .predicate _ => true
    | .terminal site => (ctx.terms site).all (fun term => readWidth term ≤ n)
    | .call site rule => (ctx.hooks.enterCall site env).all (readsFit ctx f (ctx.rules rule) n)
    | .seq a b => readsFit ctx f a n env && match runFuel ctx f a n env with
      | some (.ok rest next) => readsFit ctx f b rest next
      | _ => true
    | .alt a b => readsFit ctx f a n env && match runFuel ctx f a n env with
      | some .fail => readsFit ctx f b n env
      | _ => true
    | .star a => readsFit ctx f (.starLoop a) n {env with resultDepth := 0}
    | .starLoop a => readsFit ctx f a n env && match runFuel ctx f a n env with
      | some (.ok rest next) => if rest < n then readsFit ctx f (.starLoop a) rest
          {next with resultDepth := max env.resultDepth next.resultDepth} else true
      | _ => true
    | .ahead a | .notAhead a | .label _ _ a | .capture a | .bind _ _ a | .action _ a =>
      readsFit ctx f a n env

theorem invariant1_window_run {ctx : Inputs} {f b n env r}
    (observed : runFuel ctx f b n env = some r)
    (fits : readsFit ctx f b n env = true) (within : n ≤ ctx.input.length)
    (extra : List Char) :
    Derives (appendInput ctx extra) b (n + extra.length) env (r.shift extra.length) := by
  induction f generalizing b n env r with
  | zero => simp [runFuel] at observed
  | succ f ih =>
    have localStep := invariant1_runFuel_sound observed
    unfold runFuel at observed
    unfold readsFit at fits
    cases b with
    | eps => cases observed; exact .eps
    | terminal site =>
      apply shift_terminal_leaf extra within _ localStep
      intro term found
      simpa [found] using fits
    | predicate site =>
      cases localStep with
      | predicateOk test => exact .predicateOk test
      | predicateFail test => exact .predicateFail test
    | capture a => exact .capture (ih observed fits within)
    | star a => exact .star (ih observed fits within)
    | call site rule =>
      cases h : ctx.hooks.enterCall site env with
      | none => simp [h] at observed; subst r; exact .callMissing h
      | some callee =>
        cases hr : runFuel ctx f (ctx.rules rule) n callee with
        | none => simp [h, hr] at observed
        | some inner =>
          have d := ih hr (by simpa [h] using fits) within
          have eq : callResult ctx site env inner = r := by cases inner <;> simpa [callResult, h, hr] using observed
          rw [← eq, ← shift_call]
          exact .call h d
    | seq a b =>
      have both := Bool.and_eq_true_iff.mp fits
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have d := ih hr both.1 within
        cases inner with
        | fail => simp [hr] at observed; subst r; exact .seqCarryFail d
        | throwLabel pos name msg => simp [hr] at observed; subst r; exact .seqCarryThrow d
        | ok rest next =>
          have bound := invariant1_success_remaining_le (invariant1_runFuel_sound hr) _ _ rfl
          exact .seqOk d (ih (by simpa [hr] using observed) (by simpa [hr] using both.2) (Nat.le_trans bound within))
    | alt a b =>
      have both := Bool.and_eq_true_iff.mp fits
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have d := ih hr both.1 within
        cases inner with
        | fail => exact .altRetry d (ih (by simpa [hr] using observed) (by simpa [hr] using both.2) within)
        | ok rest next => simp [hr] at observed; subst r; exact .altLeft d (by simp [Reply.shift])
        | throwLabel pos name msg => simp [hr] at observed; subst r; exact .altLeft d (by simp [Reply.shift])
    | ahead a =>
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have eq : aheadResult n env inner = r := by
          cases inner <;> simpa [aheadResult, hr] using observed
        rw [← eq, ← (shift_lookahead n env inner extra.length).1]
        exact .ahead (ih hr fits within)
    | notAhead a =>
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have eq : notAheadResult n env inner = r := by
          cases inner <;> simpa [notAheadResult, hr] using observed
        rw [← eq, ← (shift_lookahead n env inner extra.length).2]
        exact .notAhead (ih hr fits within)
    | label name msg a =>
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have eq : labelResult n name msg inner = r := by
          cases inner <;> simpa [labelResult, hr] using observed
        rw [← eq, ← shift_label n name msg inner extra.length]
        exact .label (ih hr fits within)
    | bind site name a =>
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have eq : bindResult ctx site name n inner = r := by
          cases inner with
          | ok rest e =>
            cases v : ctx.hooks.bindValue site name (matchedText ctx.input n rest) e <;> simpa [bindResult, hr, v] using observed
          | fail | throwLabel => simpa [bindResult, hr] using observed
        rw [← eq, ← shift_binding ctx extra site name n within inner]
        exact .bind (ih hr fits within)
    | action site a =>
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have eq : actionResult ctx site inner = r := by
          cases inner with
          | ok rest e =>
            cases v : ctx.actions site >>= DepthAction.eval e <;> simpa [actionResult, hr, v] using observed
          | fail | throwLabel => simpa [actionResult, hr] using observed
        rw [← eq, ← shift_action ctx extra site inner]
        exact .action (ih hr fits within)
    | starLoop a =>
      have both := Bool.and_eq_true_iff.mp fits
      cases hr : runFuel ctx f a n env with
      | none => simp [hr] at observed
      | some inner =>
        have d := ih hr both.1 within
        cases inner with
        | fail => simp [hr] at observed; subst r; exact .loopStop d
        | throwLabel pos name msg => simp [hr] at observed; subst r; exact .loopThrow d
        | ok rest next =>
          have bound := invariant1_success_remaining_le (invariant1_runFuel_sound hr) _ _ rfl
          by_cases progress : rest < n
          · exact .loopMore d (by omega) (ih (by simpa [hr, progress] using observed)
              (by simpa [hr, progress] using both.2) (Nat.le_trans bound within))
          · have same : rest = n := by omega
            subst rest
            simp [hr] at observed
            subst r
            exact .loopZero d

set_option maxRecDepth 8192 in
theorem invariant1_actual_rule_window (mode : Bool) (before window extra : List Char)
    (rule fuel n : Nat) (env : Env) (r : Reply) (bound : n ≤ window.length)
    (observed : runFuel (MetaExecution.context mode window) fuel
      ((MetaExecution.context mode window).rules rule) n env = some r)
    (fits : readsFit (MetaExecution.context mode window) fuel
      ((MetaExecution.context mode window).rules rule) n env = true) :
    Derives (MetaExecution.context mode (before ++ (window ++ extra)))
      ((MetaExecution.context mode (window ++ extra)).rules rule)
      (n + extra.length) env (r.shift extra.length) := by
  let ctx := MetaExecution.context mode window
  have input : ctx.input = window := by cases mode <;> rfl
  have shifted := invariant1_window_run observed fits (input.symm ▸ bound) extra
  apply (invariant1_actual_rule_prepend_iff mode before (window ++ extra)
    rule _ env _ (by simp; omega)).mpr
  have ctxEq : appendInput ctx extra = MetaExecution.context mode (window ++ extra) := by
    cases mode <;> rfl
  have rulesEq : ctx.rules = (MetaExecution.context mode (window ++ extra)).rules := by
    cases mode <;> rfl
  change Derives (appendInput ctx extra) (ctx.rules rule) _ env _ at shifted
  rw [ctxEq, rulesEq] at shifted
  exact shifted

#print axioms invariant1_actual_rule_window
#print axioms invariant1_window_run
end PegHs.EnvironmentEval
