import EnvironmentFuel
import ConcreteTerminal

namespace PegHs.EnvironmentEval

open PegHs.ConcreteTerminal

def predicateTest (ctx : Inputs) (site : Nat) (env : Env) : Option Bool := do
  let (kind, polarity) ← ctx.sites site
  some (PegHs.SemanticPredicates.eval ctx.classes kind
    (ctx.predicateEnv site env) == polarity)

def callResult (ctx : Inputs) (site : Nat) (caller : Env) : Reply → Reply
  | .ok rest callee => .ok rest (ctx.hooks.leaveCall site caller callee)
  | .fail => .fail
  | .throwLabel pos name msg => .throwLabel pos name msg

def aheadResult (n : Nat) (env : Env) : Reply → Reply
  | .ok _ _ => .ok n env
  | _ => .fail

def notAheadResult (n : Nat) (env : Env) : Reply → Reply
  | .ok _ _ => .fail
  | _ => .ok n env

def labelResult (n : Nat) (name : String) (msg : Option String) : Reply → Reply
  | .fail => .throwLabel n name msg
  | other => other

def bindResult (ctx : Inputs) (site : Nat) (name : String)
    (n : Nat) : Reply → Reply
  | .ok rest inner =>
      match ctx.hooks.bindValue site name (matchedText ctx.input n rest) inner with
      | some bound => .ok rest bound
      | none => .fail
  | other => other

def actionResult (ctx : Inputs) (site : Nat) : Reply → Reply
  | .ok rest inner =>
      match ctx.actions site >>= DepthAction.eval inner with
      | some depth => .ok rest { inner with resultDepth := depth }
      | none => .fail
  | other => other

inductive Derives (ctx : Inputs) : Body → Nat → Env → Reply → Prop where
  | eps {n env} : Derives ctx .eps n env (.ok n { env with resultDepth := 0 })
  | terminalOk {site n env rest term} :
      ctx.terms site = some term → TerminalStep term ctx.input n rest → rest < n →
      Derives ctx (.terminal site) n env (.ok rest { env with resultDepth := 0 })
  | terminalFail {site n env} :
      (ctx.terms site = none ∨
        ∃ term, ctx.terms site = some term ∧
          ¬∃ rest, TerminalStep term ctx.input n rest ∧ rest < n) →
      Derives ctx (.terminal site) n env .fail
  | predicateOk {site n env} : predicateTest ctx site env = some true →
      Derives ctx (.predicate site) n env (.ok n { env with resultDepth := 0 })
  | predicateFail {site n env} :
      (predicateTest ctx site env = none ∨ predicateTest ctx site env = some false) →
      Derives ctx (.predicate site) n env .fail
  | callMissing {site rule n env} : ctx.hooks.enterCall site env = none →
      Derives ctx (.call site rule) n env .fail
  | call {site rule n env callee r} : ctx.hooks.enterCall site env = some callee →
      Derives ctx (ctx.rules rule) n callee r →
      Derives ctx (.call site rule) n env (callResult ctx site env r)
  | seqCarryFail {a b n env} : Derives ctx a n env .fail →
      Derives ctx (.seq a b) n env .fail
  | seqCarryThrow {a b n env pos name msg} :
      Derives ctx a n env (.throwLabel pos name msg) →
      Derives ctx (.seq a b) n env (.throwLabel pos name msg)
  | seqOk {a b n env mid next r} : Derives ctx a n env (.ok mid next) →
      Derives ctx b mid next r → Derives ctx (.seq a b) n env r
  | altLeft {a b n env r} : Derives ctx a n env r → r ≠ .fail →
      Derives ctx (.alt a b) n env r
  | altRetry {a b n env r} : Derives ctx a n env .fail →
      Derives ctx b n env r → Derives ctx (.alt a b) n env r
  | ahead {a n env r} : Derives ctx a n env r →
      Derives ctx (.ahead a) n env (aheadResult n env r)
  | notAhead {a n env r} : Derives ctx a n env r →
      Derives ctx (.notAhead a) n env (notAheadResult n env r)
  | star {a n env r} : Derives ctx (.starLoop a) n { env with resultDepth := 0 } r →
      Derives ctx (.star a) n env r
  | loopStop {a n env} : Derives ctx a n env .fail →
      Derives ctx (.starLoop a) n env (.ok n env)
  | loopThrow {a n env pos name msg} :
      Derives ctx a n env (.throwLabel pos name msg) →
      Derives ctx (.starLoop a) n env (.throwLabel pos name msg)
  | loopZero {a n env next} : Derives ctx a n env (.ok n next) →
      Derives ctx (.starLoop a) n env (.ok n env)
  | loopMore {a n env mid next r} : Derives ctx a n env (.ok mid next) → mid < n →
      Derives ctx (.starLoop a) mid
        { next with resultDepth := max env.resultDepth next.resultDepth } r →
      Derives ctx (.starLoop a) n env r
  | label {a n env name msg r} : Derives ctx a n env r →
      Derives ctx (.label name msg a) n env (labelResult n name msg r)
  | capture {a n env r} : Derives ctx a n env r →
      Derives ctx (.capture a) n env r
  | bind {a n env site name r} : Derives ctx a n env r →
      Derives ctx (.bind site name a) n env (bindResult ctx site name n r)
  | action {a n env site r} : Derives ctx a n env r →
      Derives ctx (.action site a) n env (actionResult ctx site r)

theorem invariant1_success_remaining_le {ctx body n env r}
    (h : Derives ctx body n env r) :
    ∀ rest next, r = .ok rest next → rest ≤ n := by
  induction h with
  | eps | predicateOk => intro rest next eq; cases eq; omega
  | terminalOk _ _ progress => intro rest next eq; cases eq; omega
  | terminalFail | predicateFail | callMissing | seqCarryFail | seqCarryThrow |
    loopThrow => intro rest next eq; cases eq
  | @call site rule n env callee childResult entered child ih =>
      intro rest next eq
      cases childResult with
      | ok mid callee =>
          change Reply.ok mid (ctx.hooks.leaveCall site env callee) =
            Reply.ok rest next at eq
          cases eq
          exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq

  | seqOk _ _ ih₁ ih₂ =>
      intro rest next eq
      exact Nat.le_trans (ih₂ rest next eq) (ih₁ _ _ rfl)
  | altLeft _ _ ih => intro rest next eq; exact ih rest next eq
  | altRetry _ _ _ ih => intro rest next eq; exact ih rest next eq
  | @ahead a n env childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok _ _ => cases eq; omega
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | @notAhead a n env childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok _ _ => cases eq
      | fail => cases eq; omega
      | throwLabel _ _ _ => cases eq; omega
  | star _ ih => intro rest next eq; exact ih rest next eq
  | loopStop | loopZero => intro rest next eq; cases eq; omega
  | loopMore _ _ _ ih₁ ih₂ =>
      intro rest next eq
      exact Nat.le_trans (ih₂ rest next eq) (ih₁ _ _ rfl)
  | @label a n env name msg childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          change Reply.ok mid inner = Reply.ok rest next at eq
          cases eq
          exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | capture _ ih => intro rest next eq; exact ih rest next eq
  | @bind a n env site name childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          cases hb : ctx.hooks.bindValue site name (matchedText ctx.input n mid) inner with
          | none => simp [bindResult, hb] at eq
          | some bound =>
              simp only [bindResult, hb] at eq
              cases eq
              exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | @action a n env site childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          cases ha : ctx.actions site >>= DepthAction.eval inner with
          | none => simp [actionResult, ha] at eq
          | some depth =>
              simp only [actionResult, ha] at eq
              cases eq
              exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq


theorem invariant1_runFuel_sound {ctx fuel body n env r}
    (observed : runFuel ctx fuel body n env = some r) :
    Derives ctx body n env r := by
  induction fuel generalizing body n env r with
  | zero => simp [runFuel] at observed
  | succ fuel ih =>
      cases body with
      | eps => simp [runFuel] at observed; subst r; exact .eps
      | terminal site =>
          cases ht : ctx.terms site with
          | none =>
              simp [runFuel, ht] at observed
              subst r
              exact .terminalFail (.inl ht)
          | some term =>
              cases hit : terminalOracle term ctx.input n with
              | none =>
                  simp [runFuel, ht, hit] at observed
                  subst r
                  have rejected := (invariant1_terminalOracle_reject term ctx.input n).mp hit
                  exact .terminalFail (.inr ⟨term, ht, by
                    rintro ⟨rest, step, _⟩
                    exact rejected ⟨rest, step⟩⟩)
              | some rest =>
                  by_cases progress : rest < n
                  · simp [runFuel, ht, hit, progress] at observed
                    subst r
                    exact .terminalOk ht
                      ((invariant1_terminalOracle_iff term ctx.input n rest).mp hit) progress
                  · simp [runFuel, ht, hit, progress] at observed
                    subst r
                    exact .terminalFail (.inr ⟨term, ht, by
                      rintro ⟨other, step, advances⟩
                      have accepted :=
                        (invariant1_terminalOracle_iff term ctx.input n other).mpr step
                      rw [hit] at accepted
                      cases accepted
                      exact progress advances⟩)
      | predicate site =>
          cases hs : ctx.sites site with
          | none =>
              simp [runFuel, hs] at observed
              subst r
              exact .predicateFail (.inl (by simp [predicateTest, hs]))
          | some kp =>
              obtain ⟨kind, polarity⟩ := kp
              by_cases yes : (PegHs.SemanticPredicates.eval ctx.classes kind
                  (ctx.predicateEnv site env) == polarity) = true
              · simp [runFuel, hs, yes] at observed
                subst r
                exact .predicateOk (by simp [predicateTest, hs, yes])
              · have no : (PegHs.SemanticPredicates.eval ctx.classes kind
                    (ctx.predicateEnv site env) == polarity) = false := by
                  cases value : (PegHs.SemanticPredicates.eval ctx.classes kind
                    (ctx.predicateEnv site env) == polarity) <;> simp_all
                simp [runFuel, hs, no] at observed
                subst r
                exact .predicateFail (.inr (by simp [predicateTest, hs, no]))
      | call site rule =>
          cases entered : ctx.hooks.enterCall site env with
          | none =>
              simp [runFuel, entered] at observed
              subst r
              exact .callMissing entered
          | some callee =>
              cases child : runFuel ctx fuel (ctx.rules rule) n callee with
              | none => simp [runFuel, entered, child] at observed
              | some result =>
                  cases result with
                  | ok rest inner =>
                      simp [runFuel, entered, child] at observed
                      subst r
                      exact .call entered (ih child)
                  | fail =>
                      simp [runFuel, entered, child] at observed
                      subst r
                      exact .call entered (ih child)
                  | throwLabel pos name msg =>
                      simp [runFuel, entered, child] at observed
                      subst r
                      exact .call entered (ih child)
      | seq a b =>
          cases left : runFuel ctx fuel a n env with
          | none => simp [runFuel, left] at observed
          | some result =>
              cases result with
              | fail =>
                  simp [runFuel, left] at observed
                  subst r
                  exact .seqCarryFail (ih left)
              | throwLabel pos name msg =>
                  simp [runFuel, left] at observed
                  subst r
                  exact .seqCarryThrow (ih left)
              | ok mid next =>
                  cases right : runFuel ctx fuel b mid next with
                  | none => simp [runFuel, left, right] at observed
                  | some result =>
                      simp [runFuel, left, right] at observed
                      subst r
                      exact .seqOk (ih left) (ih right)
      | alt a b =>
          cases left : runFuel ctx fuel a n env with
          | none => simp [runFuel, left] at observed
          | some result =>
              cases result with
              | fail =>
                  cases right : runFuel ctx fuel b n env with
                  | none => simp [runFuel, left, right] at observed
                  | some result =>
                      simp [runFuel, left, right] at observed
                      subst r
                      exact .altRetry (ih left) (ih right)
              | ok rest next =>
                  simp [runFuel, left] at observed
                  subst r
                  exact .altLeft (ih left) (by simp)
              | throwLabel pos name msg =>
                  simp [runFuel, left] at observed
                  subst r
                  exact .altLeft (ih left) (by simp)
      | ahead a =>
          cases child : runFuel ctx fuel a n env with
          | none => simp [runFuel, child] at observed
          | some result =>
              cases result <;> simp [runFuel, child] at observed <;> subst r <;>
                first | exact .ahead (ih child) | skip
      | notAhead a =>
          cases child : runFuel ctx fuel a n env with
          | none => simp [runFuel, child] at observed
          | some result =>
              cases result <;> simp [runFuel, child] at observed <;> subst r <;>
                first | exact .notAhead (ih child) | skip
      | star a => exact .star (ih (by simpa [runFuel] using observed))
      | starLoop a =>
          cases child : runFuel ctx fuel a n env with
          | none => simp [runFuel, child] at observed
          | some result =>
              cases result with
              | fail =>
                  simp [runFuel, child] at observed
                  subst r
                  exact .loopStop (ih child)
              | throwLabel pos name msg =>
                  simp [runFuel, child] at observed
                  subst r
                  exact .loopThrow (ih child)
              | ok mid next =>
                  by_cases progress : mid < n
                  · cases rest : runFuel ctx fuel (.starLoop a) mid
                      { next with resultDepth := max env.resultDepth next.resultDepth } with
                    | none => simp [runFuel, child, progress, rest] at observed
                    | some result =>
                        simp [runFuel, child, progress, rest] at observed
                        subst r
                        exact .loopMore (ih child) progress (ih rest)
                  · simp [runFuel, child, progress] at observed
                    subst r
                    have same : mid = n := by
                      have bounded := invariant1_success_remaining_le (ih child) mid next rfl
                      omega
                    subst mid
                    exact .loopZero (ih child)
      | label name msg a =>
          cases child : runFuel ctx fuel a n env with
          | none => simp [runFuel, child] at observed
          | some result =>
              cases result <;> simp [runFuel, child] at observed <;> subst r <;>
                first | exact .label (ih child) | skip
      | capture a => exact .capture (ih (by simpa [runFuel] using observed))
      | bind site name a =>
          cases child : runFuel ctx fuel a n env with
          | none => simp [runFuel, child] at observed
          | some result =>
              cases result with
              | fail =>
                  simp [runFuel, child] at observed
                  subst r
                  exact .bind (ih child)
              | throwLabel pos label msg =>
                  simp [runFuel, child] at observed
                  subst r
                  exact .bind (ih child)
              | ok rest inner =>
                  cases bound : ctx.hooks.bindValue site name
                      (matchedText ctx.input n rest) inner with
                  | none =>
                      simp [runFuel, child, bound] at observed
                      subst r
                      have derived : Derives ctx (.bind site name a) n env
                          (bindResult ctx site name n (.ok rest inner)) := .bind (ih child)
                      simpa [bindResult, bound] using derived
                  | some boundEnv =>
                      simp [runFuel, child, bound] at observed
                      subst r
                      have derived : Derives ctx (.bind site name a) n env
                          (bindResult ctx site name n (.ok rest inner)) := .bind (ih child)
                      simpa [bindResult, bound] using derived
      | action site a =>
          cases child : runFuel ctx fuel a n env with
          | none => simp [runFuel, child] at observed
          | some result =>
              cases result with
              | fail =>
                  simp [runFuel, child] at observed
                  subst r
                  exact .action (ih child)
              | throwLabel pos label msg =>
                  simp [runFuel, child] at observed
                  subst r
                  exact .action (ih child)
              | ok rest inner =>
                  cases value : ctx.actions site >>= DepthAction.eval inner with
                  | none =>
                      simp [runFuel, child, value] at observed
                      subst r
                      have derived : Derives ctx (.action site a) n env
                          (actionResult ctx site (.ok rest inner)) := .action (ih child)
                      simpa [actionResult, value] using derived
                  | some depth =>
                      simp [runFuel, child, value] at observed
                      subst r
                      have derived : Derives ctx (.action site a) n env
                          (actionResult ctx site (.ok rest inner)) := .action (ih child)
                      simpa [actionResult, value] using derived

#print axioms invariant1_runFuel_sound

theorem invariant1_derivation_has_fuel {ctx body n env r}
    (h : Derives ctx body n env r) :
    ∃ fuel, runFuel ctx fuel body n env = some r := by
  induction h with
  | eps => exact ⟨1, rfl⟩
  | terminalOk matched step progress =>
      have hit := (invariant1_terminalOracle_iff _ _ _ _).mpr step
      exact ⟨1, by simp [runFuel, matched, hit, progress]⟩
  | @terminalFail site n env failure =>
      cases failure with
      | inl absent => exact ⟨1, by simp [runFuel, absent]⟩
      | inr present =>
          obtain ⟨term, matched, rejected⟩ := present
          cases hit : terminalOracle term ctx.input n with
          | none => exact ⟨1, by simp [runFuel, matched, hit]⟩
          | some rest =>
              have step := (invariant1_terminalOracle_iff term ctx.input n rest).mp hit
              have noProgress : ¬rest < n := fun p => rejected ⟨rest, step, p⟩
              exact ⟨1, by simp [runFuel, matched, hit, noProgress]⟩
  | @predicateOk site n env accepted =>
      unfold predicateTest at accepted
      cases hs : ctx.sites site with
      | none => simp [hs] at accepted
      | some kp =>
          obtain ⟨kind, polarity⟩ := kp
          simp [hs] at accepted
          exact ⟨1, by simp [runFuel, hs, accepted]⟩
  | @predicateFail site n env rejected =>
      cases rejected with
      | inl absent =>
          unfold predicateTest at absent
          cases hs : ctx.sites site with
          | none => exact ⟨1, by simp [runFuel, hs]⟩
          | some kp => simp [hs] at absent
      | inr no =>
          unfold predicateTest at no
          cases hs : ctx.sites site with
          | none => simp [hs] at no
          | some kp =>
              obtain ⟨kind, polarity⟩ := kp
              simp [hs] at no
              exact ⟨1, by simp [runFuel, hs, no]⟩
  | callMissing absent => exact ⟨1, by simp [runFuel, absent]⟩
  | @call site rule n env callee childResult entered child ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult with
      | ok rest inner => exact ⟨fuel + 1, by simp [runFuel, entered, result, callResult]⟩
      | fail => exact ⟨fuel + 1, by simp [runFuel, entered, result, callResult]⟩
      | throwLabel pos name msg =>
          exact ⟨fuel + 1, by simp [runFuel, entered, result, callResult]⟩
  | seqCarryFail _ ih | seqCarryThrow _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | seqOk _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := invariant1_fuel_stable ctx (Nat.le_max_left f₁ f₂) h₁
      have h₂' := invariant1_fuel_stable ctx (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', h₂']⟩
  | @altLeft a b n env childResult child notFail ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult with
      | fail => exact False.elim (notFail rfl)
      | ok rest next => exact ⟨fuel + 1, by simp [runFuel, result]⟩
      | throwLabel pos name msg => exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | altRetry _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := invariant1_fuel_stable ctx (Nat.le_max_left f₁ f₂) h₁
      have h₂' := invariant1_fuel_stable ctx (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', h₂']⟩
  | @ahead a n env childResult child ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult <;> exact ⟨fuel + 1, by simp [runFuel, result, aheadResult]⟩
  | @notAhead a n env childResult child ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult <;> exact ⟨fuel + 1, by simp [runFuel, result, notAheadResult]⟩
  | star _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simpa [runFuel] using result⟩
  | loopStop _ ih | loopThrow _ ih | loopZero _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | loopMore _ progress _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := invariant1_fuel_stable ctx (Nat.le_max_left f₁ f₂) h₁
      have h₂' := invariant1_fuel_stable ctx (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', progress, h₂']⟩
  | @label a n env name msg childResult child ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult <;> exact ⟨fuel + 1, by simp [runFuel, result, labelResult]⟩
  | capture _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simpa [runFuel] using result⟩
  | @bind a n env site name childResult child ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult with
      | fail => exact ⟨fuel + 1, by simp [runFuel, result, bindResult]⟩
      | throwLabel pos label msg =>
          exact ⟨fuel + 1, by simp [runFuel, result, bindResult]⟩
      | ok rest inner =>
          cases hb : ctx.hooks.bindValue site name
              (matchedText ctx.input n rest) inner with
          | none => exact ⟨fuel + 1, by simp [runFuel, result, bindResult, hb]⟩
          | some bound => exact ⟨fuel + 1, by simp [runFuel, result, bindResult, hb]⟩
  | @action a n env site childResult child ih =>
      obtain ⟨fuel, result⟩ := ih
      cases childResult with
      | fail => exact ⟨fuel + 1, by simp [runFuel, result, actionResult]⟩
      | throwLabel pos label msg =>
          exact ⟨fuel + 1, by simp [runFuel, result, actionResult]⟩
      | ok rest inner =>
          cases ha : ctx.actions site >>= DepthAction.eval inner with
          | none => exact ⟨fuel + 1, by simp [runFuel, result, actionResult, ha]⟩
          | some depth => exact ⟨fuel + 1, by simp [runFuel, result, actionResult, ha]⟩

theorem invariant1_env_exec_iff {ctx body n env r} :
    Derives ctx body n env r ↔ ∃ fuel, runFuel ctx fuel body n env = some r := by
  constructor
  · exact invariant1_derivation_has_fuel
  · rintro ⟨fuel, observed⟩
    exact invariant1_runFuel_sound observed

#print axioms invariant1_env_exec_iff

theorem invariant1_success_consumes {ctx body n env r}
    (h : Derives ctx body n env r) :
    ∀ rest next, r = .ok rest next →
      ∃ k, n = rest + k ∧
        PegHs.CallOrder.Consumes (fun rule => erase (ctx.rules rule)) (erase body) k := by
  induction h with
  | eps | predicateOk =>
      intro rest next eq
      cases eq
      exact ⟨0, by simp, .empty⟩
  | @terminalOk site n env rest term _ _ progress =>
      intro target next eq
      cases eq
      obtain ⟨k, hk⟩ : ∃ k, n - rest = k + 1 := ⟨n - rest - 1, by omega⟩
      exact ⟨k + 1, by omega, .token k⟩
  | terminalFail | predicateFail | callMissing | seqCarryFail | seqCarryThrow |
    loopThrow => intro rest next eq; cases eq
  | @call site rule n env callee childResult entered child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          change Reply.ok mid (ctx.hooks.leaveCall site env inner) =
            Reply.ok rest next at eq
          cases eq
          obtain ⟨k, length, consumed⟩ := ih _ _ rfl
          exact ⟨k, length, .call consumed⟩
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | seqOk _ _ ih₁ ih₂ =>
      intro rest next eq
      obtain ⟨i, len₁, consumed₁⟩ := ih₁ _ _ rfl
      obtain ⟨j, len₂, consumed₂⟩ := ih₂ rest next eq
      exact ⟨i + j, by omega, .seq consumed₁ consumed₂⟩
  | altLeft _ _ ih =>
      intro rest next eq
      obtain ⟨k, length, consumed⟩ := ih rest next eq
      exact ⟨k, length, .left consumed⟩
  | altRetry _ _ _ ih =>
      intro rest next eq
      obtain ⟨k, length, consumed⟩ := ih rest next eq
      exact ⟨k, length, .right consumed⟩
  | @ahead a n env childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok _ _ => cases eq; exact ⟨0, by simp, .look⟩
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | @notAhead a n env childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok _ _ => cases eq
      | fail => cases eq; exact ⟨0, by simp, .look⟩
      | throwLabel _ _ _ => cases eq; exact ⟨0, by simp, .look⟩
  | star _ ih => intro rest next eq; exact ih rest next eq
  | loopStop | loopZero =>
      intro rest next eq
      cases eq
      exact ⟨0, by simp, .stop⟩
  | loopMore _ _ _ ih₁ ih₂ =>
      intro rest next eq
      obtain ⟨i, len₁, consumed₁⟩ := ih₁ _ _ rfl
      obtain ⟨j, len₂, consumed₂⟩ := ih₂ rest next eq
      exact ⟨i + j, by omega, .more consumed₁ consumed₂⟩
  | @label a n env name msg childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          change Reply.ok mid inner = Reply.ok rest next at eq
          cases eq
          exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | capture _ ih => intro rest next eq; exact ih rest next eq
  | @bind a n env site name childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          cases hb : ctx.hooks.bindValue site name (matchedText ctx.input n mid) inner with
          | none => simp [bindResult, hb] at eq
          | some bound =>
              simp only [bindResult, hb] at eq
              cases eq
              exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq
  | @action a n env site childResult child ih =>
      intro rest next eq
      cases childResult with
      | ok mid inner =>
          cases ha : ctx.actions site >>= DepthAction.eval inner with
          | none => simp [actionResult, ha] at eq
          | some depth =>
              simp only [actionResult, ha] at eq
              cases eq
              exact ih _ _ rfl
      | fail => cases eq
      | throwLabel _ _ _ => cases eq

#print axioms invariant1_success_consumes

inductive DirectCall (ctx : Inputs) : Body → Nat → Env → Nat → Nat → Prop where
  | here (site rule n env) : DirectCall ctx (.call site rule) n env rule n
  | seqLeft {a b n env rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.seq a b) n env rule spot
  | seqRight {a b n env mid next rule spot} :
      Derives ctx a n env (.ok mid next) → DirectCall ctx b mid next rule spot →
      DirectCall ctx (.seq a b) n env rule spot
  | altLeft {a b n env rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.alt a b) n env rule spot
  | altRight {a b n env rule spot} : Derives ctx a n env .fail →
      DirectCall ctx b n env rule spot → DirectCall ctx (.alt a b) n env rule spot
  | ahead {a n env rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.ahead a) n env rule spot
  | notAhead {a n env rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.notAhead a) n env rule spot
  | star {a n env rule spot} :
      DirectCall ctx (.starLoop a) n { env with resultDepth := 0 } rule spot →
      DirectCall ctx (.star a) n env rule spot
  | loopFirst {a n env rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.starLoop a) n env rule spot
  | loopLater {a n env mid next rule spot} :
      Derives ctx a n env (.ok mid next) → mid < n →
      DirectCall ctx (.starLoop a) mid
        { next with resultDepth := max env.resultDepth next.resultDepth } rule spot →
      DirectCall ctx (.starLoop a) n env rule spot
  | label {a n env name msg rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.label name msg a) n env rule spot
  | capture {a n env rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.capture a) n env rule spot
  | bind {a n env site name rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.bind site name a) n env rule spot
  | action {a n env site rule spot} : DirectCall ctx a n env rule spot →
      DirectCall ctx (.action site a) n env rule spot

theorem invariant1_direct_reaches {ctx body n env rule spot}
    (attempt : DirectCall ctx body n env rule spot) :
    ∃ k, n = spot + k ∧
      PegHs.CallOrder.Reaches (fun name => erase (ctx.rules name))
        (erase body) rule k := by
  induction attempt with
  | here _ rule n env => exact ⟨0, by omega, .call rule⟩
  | seqLeft _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .seqLeft reach⟩
  | seqRight first _ ih =>
      obtain ⟨i, len, consumed⟩ := invariant1_success_consumes first _ _ rfl
      obtain ⟨j, eq, reach⟩ := ih
      exact ⟨i + j, by omega, .seqRight consumed reach⟩
  | altLeft _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .altLeft reach⟩
  | altRight _ _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .altRight reach⟩
  | ahead _ ih | notAhead _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .look reach⟩
  | star _ ih => exact ih
  | loopFirst _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .first reach⟩
  | loopLater first progress _ ih =>
      obtain ⟨i, len, consumed⟩ := invariant1_success_consumes first _ _ rfl
      obtain ⟨j, eq, reach⟩ := ih
      have positive : 0 < i := by omega
      exact ⟨i + j, by omega, .later positive consumed reach⟩
  | label _ ih | capture _ ih | bind _ ih | action _ ih => exact ih

#print axioms invariant1_direct_reaches

private def bodySize : Body → Nat
  | .eps | .terminal _ | .predicate _ | .call _ _ => 1
  | .seq a b | .alt a b => bodySize a + bodySize b + 1
  | .ahead a | .notAhead a | .capture a | .label _ _ a | .bind _ _ a |
    .action _ a | .starLoop a => bodySize a + 1
  | .star a => bodySize a + 2

theorem invariant1_rule_total {ctx known rank}
    (checked : ∀ rule,
      PegHs.CallOrder.validRule known rank rule (erase (ctx.rules rule)) = true) :
    ∀ state : Nat × Nat, ∀ env : Env,
      ∃ r, Derives ctx (ctx.rules state.2) state.1 env r := by
  intro state
  induction state using (PegHs.CallOrder.invariant1_call_wellFounded checked).induction with
  | h state ih =>
      have descend {callee spot}
          (nested : PegHs.CallOrder.Nested (fun rule => erase (ctx.rules rule))
            (spot, callee) state) (env : Env) :
          ∃ r, Derives ctx (ctx.rules callee) spot env r :=
        ih (spot, callee) nested env
      let rec go (body : Body) (n : Nat) (env : Env)
          (lift : ∀ callee spot,
            DirectCall ctx body n env callee spot →
            PegHs.CallOrder.Nested (fun rule => erase (ctx.rules rule))
              (spot, callee) state) :
          ∃ r, Derives ctx body n env r := by
        cases body with
        | eps => exact ⟨.ok n { env with resultDepth := 0 }, .eps⟩
        | terminal site =>
            cases ht : ctx.terms site with
            | none => exact ⟨.fail, .terminalFail (.inl ht)⟩
            | some term =>
                cases hit : terminalOracle term ctx.input n with
                | none =>
                    have rejected := (invariant1_terminalOracle_reject term ctx.input n).mp hit
                    exact ⟨.fail, .terminalFail (.inr ⟨term, ht, by
                      rintro ⟨rest, step, _⟩
                      exact rejected ⟨rest, step⟩⟩)⟩
                | some rest =>
                    have step := (invariant1_terminalOracle_iff term ctx.input n rest).mp hit
                    by_cases progress : rest < n
                    · exact ⟨.ok rest { env with resultDepth := 0 },
                        .terminalOk ht step progress⟩
                    · exact ⟨.fail, .terminalFail (.inr ⟨term, ht, by
                        rintro ⟨other, otherStep, advances⟩
                        have accepted :=
                          (invariant1_terminalOracle_iff term ctx.input n other).mpr otherStep
                        rw [hit] at accepted
                        cases accepted
                        exact progress advances⟩)⟩
        | predicate site =>
            cases hp : predicateTest ctx site env with
            | none => exact ⟨.fail, .predicateFail (.inl hp)⟩
            | some result =>
                cases result with
                | false => exact ⟨.fail, .predicateFail (.inr hp)⟩
                | true => exact ⟨.ok n { env with resultDepth := 0 }, .predicateOk hp⟩
        | call site rule =>
            cases entered : ctx.hooks.enterCall site env with
            | none => exact ⟨.fail, .callMissing entered⟩
            | some callee =>
                obtain ⟨r, evaluated⟩ :=
                  descend (lift rule n (.here site rule n env)) callee
                exact ⟨callResult ctx site env r, .call entered evaluated⟩
        | seq a b =>
            obtain ⟨ra, evaluatedA⟩ := go a n env (fun callee spot call =>
              lift callee spot (.seqLeft call))
            cases ra with
            | fail => exact ⟨.fail, .seqCarryFail evaluatedA⟩
            | throwLabel pos name msg =>
                exact ⟨.throwLabel pos name msg, .seqCarryThrow evaluatedA⟩
            | ok mid next =>
                obtain ⟨rb, evaluatedB⟩ := go b mid next (fun callee spot call =>
                  lift callee spot (.seqRight evaluatedA call))
                exact ⟨rb, .seqOk evaluatedA evaluatedB⟩
        | alt a b =>
            obtain ⟨ra, evaluatedA⟩ := go a n env (fun callee spot call =>
              lift callee spot (.altLeft call))
            cases ra with
            | ok rest next => exact ⟨.ok rest next, .altLeft evaluatedA (by simp)⟩
            | throwLabel pos name msg =>
                exact ⟨.throwLabel pos name msg, .altLeft evaluatedA (by simp)⟩
            | fail =>
                obtain ⟨rb, evaluatedB⟩ := go b n env (fun callee spot call =>
                  lift callee spot (.altRight evaluatedA call))
                exact ⟨rb, .altRetry evaluatedA evaluatedB⟩
        | ahead a =>
            obtain ⟨r, evaluated⟩ := go a n env (fun callee spot call =>
              lift callee spot (.ahead call))
            exact ⟨aheadResult n env r, .ahead evaluated⟩
        | notAhead a =>
            obtain ⟨r, evaluated⟩ := go a n env (fun callee spot call =>
              lift callee spot (.notAhead call))
            exact ⟨notAheadResult n env r, .notAhead evaluated⟩
        | star a =>
            obtain ⟨r, evaluated⟩ := go (.starLoop a) n
              { env with resultDepth := 0 } (fun callee spot call =>
                lift callee spot (.star call))
            exact ⟨r, .star evaluated⟩
        | starLoop a =>
            obtain ⟨ra, evaluatedA⟩ := go a n env (fun callee spot call =>
              lift callee spot (.loopFirst call))
            cases ra with
            | fail => exact ⟨.ok n env, .loopStop evaluatedA⟩
            | throwLabel pos name msg =>
                exact ⟨.throwLabel pos name msg, .loopThrow evaluatedA⟩
            | ok mid next =>
                by_cases progress : mid < n
                · obtain ⟨rb, evaluatedB⟩ := go (.starLoop a) mid
                    { next with resultDepth := max env.resultDepth next.resultDepth }
                    (fun callee spot call =>
                      lift callee spot (.loopLater evaluatedA progress call))
                  exact ⟨rb, .loopMore evaluatedA progress evaluatedB⟩
                · have same : mid = n := by
                    have bounded := invariant1_success_remaining_le evaluatedA mid next rfl
                    omega
                  subst mid
                  exact ⟨.ok n env, .loopZero evaluatedA⟩
        | label name msg a =>
            obtain ⟨r, evaluated⟩ := go a n env (fun callee spot call =>
              lift callee spot (.label call))
            exact ⟨labelResult n name msg r, .label evaluated⟩
        | capture a =>
            obtain ⟨r, evaluated⟩ := go a n env (fun callee spot call =>
              lift callee spot (.capture call))
            exact ⟨r, .capture evaluated⟩
        | bind site name a =>
            obtain ⟨r, evaluated⟩ := go a n env (fun callee spot call =>
              lift callee spot (.bind call))
            exact ⟨bindResult ctx site name n r, .bind evaluated⟩
        | action site a =>
            obtain ⟨r, evaluated⟩ := go a n env (fun callee spot call =>
              lift callee spot (.action call))
            exact ⟨actionResult ctx site r, .action evaluated⟩
      termination_by (n, bodySize body)
      decreasing_by
        all_goals simp_wf
        all_goals try (have bounded := invariant1_success_remaining_le evaluatedA _ _ rfl)
        all_goals simp_all [bodySize]
        all_goals omega
      intro env
      exact go (ctx.rules state.2) state.1 env (fun callee spot call =>
        invariant1_direct_reaches call)

theorem invariant1_rule_executable {ctx known rank}
    (checked : ∀ rule,
      PegHs.CallOrder.validRule known rank rule (erase (ctx.rules rule)) = true)
    (state : Nat × Nat) (env : Env) :
    ∃ fuel r, runFuel ctx fuel (ctx.rules state.2) state.1 env = some r := by
  obtain ⟨r, derivation⟩ := invariant1_rule_total checked state env
  obtain ⟨fuel, observed⟩ := invariant1_derivation_has_fuel derivation
  exact ⟨fuel, r, observed⟩

#print axioms invariant1_rule_executable
end PegHs.EnvironmentEval
