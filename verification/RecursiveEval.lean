import CallOrder

namespace PegHs.RecursiveEval

open CallOrder

-- The token oracle either consumes a positive amount or fails. Semantic
-- predicates and values are outside Body; a non-advancing token fails.
inductive Result where
  | ok (remaining : Nat)
  | fail
  deriving DecidableEq, Repr

inductive Derives (rules : Nat → Body) (token : Nat → Option Nat) :
    Body → Nat → Result → Prop where
  | eps {n} : Derives rules token .eps n (.ok n)
  | tokenOk {n m} : token n = some m → m < n → Derives rules token .token n (.ok m)
  | tokenFail {n} : (token n = none ∨ ∃ m, token n = some m ∧ n ≤ m) →
      Derives rules token .token n .fail
  | call {rule n r} : Derives rules token (rules rule) n r →
      Derives rules token (.call rule) n r
  | seqOk {a b n m k} : Derives rules token a n (.ok m) →
      Derives rules token b m (.ok k) → Derives rules token (.seq a b) n (.ok k)
  | seqLeftFail {a b n} : Derives rules token a n .fail →
      Derives rules token (.seq a b) n .fail
  | seqRightFail {a b n m} : Derives rules token a n (.ok m) →
      Derives rules token b m .fail → Derives rules token (.seq a b) n .fail
  | altLeft {a b n r} : Derives rules token a n (.ok r) →
      Derives rules token (.alt a b) n (.ok r)
  | altRight {a b n r} : Derives rules token a n .fail →
      Derives rules token b n r → Derives rules token (.alt a b) n r
  | altFail {a b n} : Derives rules token a n .fail →
      Derives rules token b n .fail → Derives rules token (.alt a b) n .fail
  | lookOk {a n m} : Derives rules token a n (.ok m) →
      Derives rules token (.look a) n (.ok n)
  | lookFail {a n} : Derives rules token a n .fail →
      Derives rules token (.look a) n .fail
  | starFail {a n} : Derives rules token a n .fail →
      Derives rules token (.star a) n (.ok n)
  | starZero {a n} : Derives rules token a n (.ok n) →
      Derives rules token (.star a) n (.ok n)
  | starMore {a n m k} : Derives rules token a n (.ok m) → m < n →
      Derives rules token (.star a) m (.ok k) →
      Derives rules token (.star a) n (.ok k)

-- The relation is not defined with fuel: failure remains failure, and a
-- zero-width repetition stops rather than continuing at the same position.
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat) :
    Derives rules token (.alt .eps .token) n (.ok n) :=
  .altLeft .eps
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat) :
    Derives rules token (.star .eps) n (.ok n) :=
  .starZero .eps
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat)
    (failure : token n = none) :
    Derives rules token (.look .token) n .fail :=
  .lookFail (.tokenFail (.inl failure))
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat)
    (failure : token n = none) :
    Derives rules token (.alt .token .eps) n (.ok n) :=
  .altRight (.tokenFail (.inl failure)) .eps
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat)
    (failure : token n = none) :
    Derives rules token (.star .token) n (.ok n) :=
  .starFail (.tokenFail (.inl failure))

-- A successful derivation consumes exactly the prefix measured by Consumes.
theorem invariant1_success_consumes {rules token e n r}
    (h : Derives rules token e n r) :
    ∀ m, r = .ok m → ∃ k, n = m + k ∧ Consumes rules e k := by
  induction h with
  | eps =>
      intro m eq
      cases eq
      exact ⟨0, by simp, .empty⟩
  | @tokenOk n m _ progress =>
      intro target eq
      cases eq
      have positive : 0 < n - m := by omega
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      exact ⟨k + 1, by omega, .token k⟩
  | tokenFail =>
      intro m eq
      cases eq
  | call _ ih =>
      intro m eq
      obtain ⟨k, length, consumed⟩ := ih m eq
      exact ⟨k, length, .call consumed⟩
  | seqOk first second ih₁ ih₂ =>
      intro target eq
      cases eq
      obtain ⟨i, len₁, consume₁⟩ := ih₁ _ rfl
      obtain ⟨j, len₂, consume₂⟩ := ih₂ _ rfl
      exact ⟨i + j, by omega, .seq consume₁ consume₂⟩
  | seqLeftFail | seqRightFail =>
      intro m eq
      cases eq
  | altLeft first ih =>
      intro target eq
      obtain ⟨k, length, consumed⟩ := ih target eq
      exact ⟨k, length, .left consumed⟩
  | altRight _ second _ ih =>
      intro target eq
      obtain ⟨k, length, consumed⟩ := ih target eq
      exact ⟨k, length, .right consumed⟩
  | altFail =>
      intro m eq
      cases eq
  | lookOk =>
      intro target eq
      cases eq
      exact ⟨0, by simp, .look⟩
  | lookFail =>
      intro m eq
      cases eq
  | starFail | starZero =>
      intro target eq
      cases eq
      exact ⟨0, by simp, .stop⟩
  | starMore first progress rest ih₁ ih₂ =>
      intro target eq
      cases eq
      obtain ⟨i, len₁, consume₁⟩ := ih₁ _ rfl
      obtain ⟨j, len₂, consume₂⟩ := ih₂ _ rfl
      exact ⟨i + j, by omega, .more consume₁ consume₂⟩

#print axioms invariant1_success_consumes

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

-- Calls actually attempted, including failed alternatives and lookahead.
inductive DirectCall (rules : Nat → Body) (token : Nat → Option Nat) :
    Body → Nat → Nat → Nat → Prop where
  | here (rule n) : DirectCall rules token (.call rule) n rule n
  | seqLeft {a b n rule spot} : DirectCall rules token a n rule spot →
      DirectCall rules token (.seq a b) n rule spot
  | seqRight {a b n mid rule spot} : Derives rules token a n (.ok mid) →
      DirectCall rules token b mid rule spot →
      DirectCall rules token (.seq a b) n rule spot
  | altLeft {a b n rule spot} : DirectCall rules token a n rule spot →
      DirectCall rules token (.alt a b) n rule spot
  | altRight {a b n rule spot} : Derives rules token a n .fail →
      DirectCall rules token b n rule spot →
      DirectCall rules token (.alt a b) n rule spot
  | look {a n rule spot} : DirectCall rules token a n rule spot →
      DirectCall rules token (.look a) n rule spot
  | starFirst {a n rule spot} : DirectCall rules token a n rule spot →
      DirectCall rules token (.star a) n rule spot
  | starLater {a n mid rule spot} : Derives rules token a n (.ok mid) → mid < n →
      DirectCall rules token (.star a) mid rule spot →
      DirectCall rules token (.star a) n rule spot

theorem invariant1_direct_reaches {rules token e n rule spot}
    (h : DirectCall rules token e n rule spot) :
    ∃ k, n = spot + k ∧ Reaches rules e rule k := by
  induction h with
  | here rule n => exact ⟨0, by omega, .call rule⟩
  | seqLeft _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .seqLeft reach⟩
  | seqRight first _ ih =>
      obtain ⟨i, len, consume⟩ := invariant1_success_consumes first _ rfl
      obtain ⟨j, eq, reach⟩ := ih
      exact ⟨i + j, by omega, .seqRight consume reach⟩
  | altLeft _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .altLeft reach⟩
  | altRight _ _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .altRight reach⟩
  | look _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .look reach⟩
  | starFirst _ ih =>
      obtain ⟨k, eq, reach⟩ := ih
      exact ⟨k, eq, .first reach⟩
  | starLater first progress _ ih =>
      obtain ⟨i, len, consume⟩ := invariant1_success_consumes first _ rfl
      obtain ⟨j, eq, reach⟩ := ih
      have positive : 0 < i := by omega
      exact ⟨i + j, by omega, .later positive consume reach⟩

theorem invariant1_direct_nested {rules token caller callee n m}
    (h : DirectCall rules token (rules caller) n callee m) :
    Nested rules (m, callee) (n, caller) :=
  invariant1_direct_reaches h

theorem invariant1_direct_accessible {rules known rank token}
    (checked : ∀ rule, validRule known rank rule (rules rule) = true)
    {caller callee n m}
    (h : DirectCall rules token (rules caller) n callee m) :
    Acc (Nested rules) (m, callee) := by
  have parent := (invariant1_call_wellFounded checked).apply (n, caller)
  exact Acc.inv parent (invariant1_direct_nested h)

#print axioms invariant1_direct_reaches
#print axioms invariant1_direct_nested
#print axioms invariant1_direct_accessible

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

-- A bounded observer. None records an incomplete attempt, never a PEG
-- failure. The fuel is reduced for every recursive subevaluation.
def runFuel (rules : Nat → Body) (token : Nat → Option Nat) :
    Nat → Body → Nat → Option Result
  | 0, _, _ => none
  | fuel + 1, e, n =>
      match e with
      | .eps => some (.ok n)
      | .token =>
          match token n with
          | none => some .fail
          | some m => if m < n then some (.ok m) else some .fail
      | .call rule => runFuel rules token fuel (rules rule) n
      | .seq a b =>
          match runFuel rules token fuel a n with
          | none => none
          | some .fail => some .fail
          | some (.ok m) => runFuel rules token fuel b m
      | .alt a b =>
          match runFuel rules token fuel a n with
          | none => none
          | some (.ok m) => some (.ok m)
          | some .fail => runFuel rules token fuel b n
      | .look a =>
          match runFuel rules token fuel a n with
          | none => none
          | some (.ok _) => some (.ok n)
          | some .fail => some .fail
      | .star a =>
          match runFuel rules token fuel a n with
          | none => none
          | some .fail => some (.ok n)
          | some (.ok m) =>
              if m < n then runFuel rules token fuel (.star a) m
              else some (.ok n)

-- The bounded observer must preserve failure and cannot claim a result on
-- exhaustion. It is useful while the total well-founded interpreter is built.
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat) :
    runFuel rules token 0 (.alt .eps .token) n = none := rfl
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat) :
    runFuel rules token 2 (.alt .eps .token) n = some (.ok n) := rfl
example (rules : Nat → Body) (token : Nat → Option Nat) (n : Nat)
    (failure : token n = none) :
    runFuel rules token 2 (.look .token) n = some .fail := by
  simp [runFuel, failure]

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

private theorem success_remaining_le {rules token e n m}
    (h : Derives rules token e n (.ok m)) : m ≤ n := by
  obtain ⟨k, eq, _⟩ := invariant1_success_consumes h m rfl
  omega

private def bodySize : Body → Nat
  | .eps | .token | .call _ => 1
  | .seq a b | .alt a b => bodySize a + bodySize b + 1
  | .look a | .star a => bodySize a + 1

theorem invariant1_rule_total {rules known rank token}
    (checked : ∀ rule, validRule known rank rule (rules rule) = true) :
    ∀ state : Nat × Nat, ∃ r, Derives rules token (rules state.2) state.1 r := by
  intro state
  induction state using (invariant1_call_wellFounded checked).induction with
  | h state ih =>
      have descend {callee spot} (nested : Nested rules (spot, callee) state) :
          ∃ r, Derives rules token (rules callee) spot r :=
        ih (spot, callee) nested
      let rec go (e : Body) (n : Nat)
          (lift : ∀ callee spot, DirectCall rules token e n callee spot →
            Nested rules (spot, callee) state) :
          ∃ r, Derives rules token e n r := by
        cases e with
        | eps => exact ⟨.ok n, .eps⟩
        | token =>
            cases htok : token n with
            | none => exact ⟨.fail, .tokenFail (.inl htok)⟩
            | some m =>
                by_cases progress : m < n
                · exact ⟨.ok m, .tokenOk htok progress⟩
                · exact ⟨.fail, .tokenFail (.inr ⟨m, htok, by omega⟩)⟩
        | call callee =>
            obtain ⟨r, evaluated⟩ := descend (lift callee n (.here callee n))
            exact ⟨r, .call evaluated⟩
        | seq a b =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.seqLeft call))
            cases ra with
            | fail => exact ⟨.fail, .seqLeftFail evaluatedA⟩
            | ok m =>
                obtain ⟨rb, evaluatedB⟩ := go b m (fun callee spot call =>
                  lift callee spot (.seqRight evaluatedA call))
                cases rb with
                | fail => exact ⟨.fail, .seqRightFail evaluatedA evaluatedB⟩
                | ok k => exact ⟨.ok k, .seqOk evaluatedA evaluatedB⟩
        | alt a b =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.altLeft call))
            cases ra with
            | ok m => exact ⟨.ok m, .altLeft evaluatedA⟩
            | fail =>
                obtain ⟨rb, evaluatedB⟩ := go b n (fun callee spot call =>
                  lift callee spot (.altRight evaluatedA call))
                cases rb with
                | ok m => exact ⟨.ok m, .altRight evaluatedA evaluatedB⟩
                | fail => exact ⟨.fail, .altFail evaluatedA evaluatedB⟩
        | look a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.look call))
            cases ra with
            | ok m => exact ⟨.ok n, .lookOk evaluatedA⟩
            | fail => exact ⟨.fail, .lookFail evaluatedA⟩
        | star a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.starFirst call))
            cases ra with
            | fail => exact ⟨.ok n, .starFail evaluatedA⟩
            | ok m =>
                by_cases progress : m < n
                · obtain ⟨rb, evaluatedB⟩ := go (.star a) m (fun callee spot call =>
                    lift callee spot (.starLater evaluatedA progress call))
                  cases rb with
                  | ok k => exact ⟨.ok k, .starMore evaluatedA progress evaluatedB⟩
                  | fail =>
                      -- Star cannot fail once an iteration succeeded.
                      exact ⟨.fail, by cases evaluatedB⟩
                · have same : m = n := by
                    have bounded := success_remaining_le evaluatedA
                    omega
                  subst m
                  exact ⟨.ok n, .starZero evaluatedA⟩
      termination_by (n, bodySize e)
      decreasing_by
        all_goals simp_wf
        all_goals try (have bounded := success_remaining_le evaluatedA)
        all_goals simp_all [bodySize]
        all_goals omega
      exact go (rules state.2) state.1 (fun callee spot call =>
        invariant1_direct_nested call)

#print axioms invariant1_rule_total

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

private theorem runFuel_star_ne_fail (rules : Nat → Body) (token : Nat → Option Nat) :
    ∀ fuel a n, runFuel rules token fuel (.star a) n ≠ some .fail := by
  intro fuel
  induction fuel with
  | zero =>
      intro a n
      simp [runFuel]
  | succ fuel ih =>
      intro a n
      cases ha : runFuel rules token fuel a n with
      | none => simp [runFuel, ha]
      | some ra =>
          cases ra with
          | fail => simp [runFuel, ha]
          | ok m =>
              by_cases progress : m < n
              · simpa [runFuel, ha, progress] using ih a m
              · simp [runFuel, ha, progress]

theorem invariant1_runFuel_sound {rules token fuel e n r}
    (h : runFuel rules token fuel e n = some r) :
    Derives rules token e n r := by
  induction fuel generalizing e n r with
  | zero => simp [runFuel] at h
  | succ fuel ih =>
      cases e with
      | eps =>
          simp [runFuel] at h
          subst r
          exact .eps
      | token =>
          cases ht : token n with
          | none =>
              simp [runFuel, ht] at h
              subst r
              exact .tokenFail (.inl ht)
          | some m =>
              by_cases progress : m < n
              · simp [runFuel, ht, progress] at h
                subst r
                exact .tokenOk ht progress
              · simp [runFuel, ht, progress] at h
                subst r
                exact .tokenFail (.inr ⟨m, ht, by omega⟩)
      | call rule =>
          exact .call (ih (by simpa [runFuel] using h))
      | seq a b =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .seqLeftFail (ih ha)
              | ok m =>
                  cases hb : runFuel rules token fuel b m with
                  | none => simp [runFuel, ha, hb] at h
                  | some rb =>
                      cases rb with
                      | fail =>
                          simp [runFuel, ha, hb] at h
                          subst r
                          exact .seqRightFail (ih ha) (ih hb)
                      | ok k =>
                          simp [runFuel, ha, hb] at h
                          subst r
                          exact .seqOk (ih ha) (ih hb)
      | alt a b =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok m =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .altLeft (ih ha)
              | fail =>
                  cases hb : runFuel rules token fuel b n with
                  | none => simp [runFuel, ha, hb] at h
                  | some rb =>
                      cases rb with
                      | ok m =>
                          simp [runFuel, ha, hb] at h
                          subst r
                          exact .altRight (ih ha) (ih hb)
                      | fail =>
                          simp [runFuel, ha, hb] at h
                          subst r
                          exact .altFail (ih ha) (ih hb)
      | look a =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok m =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .lookOk (ih ha)
              | fail =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .lookFail (ih ha)
      | star a =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .starFail (ih ha)
              | ok m =>
                  by_cases progress : m < n
                  · cases hb : runFuel rules token fuel (.star a) m with
                    | none => simp [runFuel, ha, progress, hb] at h
                    | some rb =>
                        cases rb with
                        | ok k =>
                            simp [runFuel, ha, progress, hb] at h
                            subst r
                            exact .starMore (ih ha) progress (ih hb)
                        | fail =>
                            simp [runFuel, ha, progress, hb] at h
                            subst r
                            exact False.elim ((runFuel_star_ne_fail rules token fuel a m) hb)
                  · simp [runFuel, ha, progress] at h
                    subst r
                    have same : m = n := by
                      have bounded := success_remaining_le (ih ha)
                      omega
                    subst m
                    exact .starZero (ih ha)

#print axioms invariant1_runFuel_sound

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

private theorem runFuel_mono_step (rules : Nat → Body) (token : Nat → Option Nat) :
    ∀ fuel e n r, runFuel rules token fuel e n = some r →
      runFuel rules token (fuel + 1) e n = some r := by
  intro fuel
  induction fuel with
  | zero =>
      intro e n r h
      simp [runFuel] at h
  | succ fuel ih =>
      intro e n r h
      unfold runFuel at h ⊢
      cases e with
      | eps | token => simpa only [runFuel] using h
      | call rule => exact ih (rules rule) n r h
      | seq a b =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | fail => simpa only [ha, ha'] using h
              | ok m =>
                  cases hb : runFuel rules token fuel b m with
                  | none => simp [ha, hb] at h
                  | some rb =>
                      have hb' := ih b m rb hb
                      simpa only [ha, ha', hb, hb'] using h
      | alt a b =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | ok m => simpa only [ha, ha'] using h
              | fail =>
                  cases hb : runFuel rules token fuel b n with
                  | none => simp [ha, hb] at h
                  | some rb =>
                      have hb' := ih b n rb hb
                      simpa only [ha, ha', hb, hb'] using h
      | look a =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              simpa only [ha, ha'] using h
      | star a =>
          cases ha : runFuel rules token fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | fail => simpa only [ha, ha'] using h
              | ok m =>
                  by_cases progress : m < n
                  · cases hb : runFuel rules token fuel (.star a) m with
                    | none => simp [ha, progress, hb] at h
                    | some rb =>
                        have hb' := ih (.star a) m rb hb
                        simpa only [ha, ha', progress, hb, hb'] using h
                  · simpa [ha, ha', progress] using h

#print axioms runFuel_mono_step

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

private theorem runFuel_mono (rules : Nat → Body) (token : Nat → Option Nat)
    {fuel more e n r} (le : fuel ≤ more)
    (h : runFuel rules token fuel e n = some r) :
    runFuel rules token more e n = some r := by
  obtain ⟨extra, rfl⟩ : ∃ extra, more = fuel + extra :=
    ⟨more - fuel, by omega⟩
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
      simpa [Nat.add_assoc] using
        runFuel_mono_step rules token (fuel + extra) e n r (ih (by omega))

theorem invariant1_derivation_has_fuel {rules token e n r}
    (h : Derives rules token e n r) :
    ∃ fuel, runFuel rules token fuel e n = some r := by
  induction h with
  | eps => exact ⟨1, rfl⟩
  | tokenOk matched progress => exact ⟨1, by simp [runFuel, matched, progress]⟩
  | @tokenFail n failure =>
      cases failure with
      | inl none => exact ⟨1, by simp [runFuel, none]⟩
      | inr invalid =>
          obtain ⟨m, matched, noProgress⟩ := invalid
          exact ⟨1, by simp [runFuel, matched, Nat.not_lt.mpr noProgress]⟩
  | call _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simpa [runFuel] using h⟩
  | seqOk _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules token (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules token (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        exact h₂'⟩
  | seqLeftFail _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | seqRightFail _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules token (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules token (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        exact h₂'⟩
  | altLeft _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | altRight _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules token (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules token (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        exact h₂'⟩
  | altFail _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules token (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules token (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        exact h₂'⟩
  | lookOk _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | lookFail _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | starFail _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | starZero _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | starMore _ progress _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules token (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules token (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        simp [progress]
        exact h₂'⟩

#print axioms invariant1_derivation_has_fuel

end PegHs.RecursiveEval

namespace PegHs.RecursiveEval

open CallOrder

private theorem exists_rule_fuel {rules known rank token}
    (checked : ∀ rule, validRule known rank rule (rules rule) = true)
    (state : Nat × Nat) :
    ∃ fuel, (runFuel rules token fuel (rules state.2) state.1).isSome = true := by
  obtain ⟨r, derivation⟩ := invariant1_rule_total (token := token) checked state
  obtain ⟨fuel, h⟩ := invariant1_derivation_has_fuel derivation
  exact ⟨fuel, by simp [h]⟩

-- The executable finite observer and the independent derivation agree. A
-- missing result means only that the chosen bound was too small.
theorem invariant1_exec_iff {rules token e n r} :
    Derives rules token e n r ↔
      ∃ fuel, runFuel rules token fuel e n = some r := by
  constructor
  · exact invariant1_derivation_has_fuel
  · rintro ⟨fuel, h⟩
    exact invariant1_runFuel_sound h

-- Well-founded call order supplies a finite bound for every rule/input pair.
theorem invariant1_rule_executable {rules known rank token}
    (checked : ∀ rule, validRule known rank rule (rules rule) = true)
    (state : Nat × Nat) :
    ∃ fuel r, runFuel rules token fuel (rules state.2) state.1 = some r := by
  obtain ⟨r, derivation⟩ := invariant1_rule_total (token := token) checked state
  obtain ⟨fuel, h⟩ := invariant1_derivation_has_fuel derivation
  exact ⟨fuel, r, h⟩

#print axioms invariant1_exec_iff
#print axioms invariant1_rule_executable

end PegHs.RecursiveEval
