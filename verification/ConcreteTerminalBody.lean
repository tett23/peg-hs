import CallOrder
import ConcreteTerminal
import RecursiveEval

namespace PegHs.ConcreteTerminalBody

open PegHs.CallOrder
open PegHs.ConcreteTerminal
open PegHs.RecursiveEval (Result)

inductive Body where
  | eps
  | terminal (index : Nat)
  | call (rule : Nat)
  | seq (a b : Body)
  | alt (a b : Body)
  | ahead (a : Body)
  | notAhead (a : Body)
  | star (a : Body)
  deriving DecidableEq, Repr

def erase : Body → CallOrder.Body
  | .eps => .eps
  | .terminal _ => .token
  | .call rule => .call rule
  | .seq a b => .seq (erase a) (erase b)
  | .alt a b => .alt (erase a) (erase b)
  | .ahead a | .notAhead a => .look (erase a)
  | .star a => .star (erase a)

def terminalIds : Body → List Nat
  | .eps | .call _ => []
  | .terminal index => [index]
  | .seq a b | .alt a b => terminalIds a ++ terminalIds b
  | .ahead a | .notAhead a | .star a => terminalIds a

-- None is an unfinished finite observation; .fail is a real PEG failure.
-- Every terminal occurrence carries its own index into the extracted table.
def runFuel (rules : Nat → Body) (terms : Nat → Option Terminal)
    (input : List Char) : Nat → Body → Nat → Option Result
  | 0, _, _ => none
  | fuel + 1, body, remaining =>
      match body with
      | .eps => some (.ok remaining)
      | .terminal index =>
          match terms index with
          | none => some .fail
          | some term =>
              match terminalOracle term input remaining with
              | none => some .fail
              | some rest => if rest < remaining then some (.ok rest) else some .fail
      | .call rule => runFuel rules terms input fuel (rules rule) remaining
      | .seq a b =>
          match runFuel rules terms input fuel a remaining with
          | none => none
          | some .fail => some .fail
          | some (.ok rest) => runFuel rules terms input fuel b rest
      | .alt a b =>
          match runFuel rules terms input fuel a remaining with
          | none => none
          | some (.ok rest) => some (.ok rest)
          | some .fail => runFuel rules terms input fuel b remaining
      | .ahead a =>
          match runFuel rules terms input fuel a remaining with
          | none => none
          | some (.ok _) => some (.ok remaining)
          | some .fail => some .fail
      | .notAhead a =>
          match runFuel rules terms input fuel a remaining with
          | none => none
          | some (.ok _) => some .fail
          | some .fail => some (.ok remaining)
      | .star a =>
          match runFuel rules terms input fuel a remaining with
          | none => none
          | some .fail => some (.ok remaining)
          | some (.ok rest) =>
              if rest < remaining then runFuel rules terms input fuel (.star a) rest
              else some (.ok remaining)

private def exampleRules : Nat → Body
  | 0 => .seq (.terminal 0) (.terminal 1)
  | _ => .eps

private def exampleTerms : Nat → Option Terminal
  | 0 => some (.lit ['\n'])
  | 1 => some (.cls [('0', '9')])
  | _ => none

example : runFuel exampleRules exampleTerms ['\n', '5'] 3 (exampleRules 0) 2 =
    some (.ok 0) := by rfl
example : runFuel exampleRules exampleTerms ['\n', ':'] 3 (exampleRules 0) 2 =
    some .fail := by rfl
example : runFuel exampleRules exampleTerms ['\n', '5'] 3 (.notAhead (.terminal 0)) 2 =
    some .fail := by rfl
example : runFuel exampleRules exampleTerms ['\n', '5'] 3 (.notAhead (.terminal 1)) 2 =
    some (.ok 2) := by rfl

end PegHs.ConcreteTerminalBody

namespace PegHs.ConcreteTerminalBody

open PegHs.ConcreteTerminal
open PegHs.RecursiveEval (Result)

inductive Derives (rules : Nat → Body) (terms : Nat → Option Terminal)
    (input : List Char) : Body → Nat → Result → Prop where
  | eps {n} : Derives rules terms input .eps n (.ok n)
  | terminalOk {index n rest term} :
      terms index = some term → TerminalStep term input n rest → rest < n →
      Derives rules terms input (.terminal index) n (.ok rest)
  | terminalFail {index n} :
      (terms index = none ∨
        ∃ term, terms index = some term ∧
          ¬∃ rest, TerminalStep term input n rest ∧ rest < n) →
      Derives rules terms input (.terminal index) n .fail
  | call {rule n r} : Derives rules terms input (rules rule) n r →
      Derives rules terms input (.call rule) n r
  | seqOk {a b n mid rest} : Derives rules terms input a n (.ok mid) →
      Derives rules terms input b mid (.ok rest) →
      Derives rules terms input (.seq a b) n (.ok rest)
  | seqLeftFail {a b n} : Derives rules terms input a n .fail →
      Derives rules terms input (.seq a b) n .fail
  | seqRightFail {a b n mid} : Derives rules terms input a n (.ok mid) →
      Derives rules terms input b mid .fail →
      Derives rules terms input (.seq a b) n .fail
  | altLeft {a b n rest} : Derives rules terms input a n (.ok rest) →
      Derives rules terms input (.alt a b) n (.ok rest)
  | altRight {a b n r} : Derives rules terms input a n .fail →
      Derives rules terms input b n r → Derives rules terms input (.alt a b) n r
  | aheadOk {a n rest} : Derives rules terms input a n (.ok rest) →
      Derives rules terms input (.ahead a) n (.ok n)
  | aheadFail {a n} : Derives rules terms input a n .fail →
      Derives rules terms input (.ahead a) n .fail
  | notAheadOk {a n} : Derives rules terms input a n .fail →
      Derives rules terms input (.notAhead a) n (.ok n)
  | notAheadFail {a n rest} : Derives rules terms input a n (.ok rest) →
      Derives rules terms input (.notAhead a) n .fail
  | starFail {a n} : Derives rules terms input a n .fail →
      Derives rules terms input (.star a) n (.ok n)
  | starZero {a n} : Derives rules terms input a n (.ok n) →
      Derives rules terms input (.star a) n (.ok n)
  | starMore {a n mid rest} : Derives rules terms input a n (.ok mid) → mid < n →
      Derives rules terms input (.star a) mid (.ok rest) →
      Derives rules terms input (.star a) n (.ok rest)

private theorem runFuel_star_ne_fail (rules : Nat → Body)
    (terms : Nat → Option Terminal) (input : List Char) :
    ∀ fuel a n, runFuel rules terms input fuel (.star a) n ≠ some .fail := by
  intro fuel
  induction fuel with
  | zero => intro a n; simp [runFuel]
  | succ fuel ih =>
      intro a n
      cases ha : runFuel rules terms input fuel a n with
      | none => simp [runFuel, ha]
      | some ra =>
          cases ra with
          | fail => simp [runFuel, ha]
          | ok rest =>
              by_cases progress : rest < n
              · simpa [runFuel, ha, progress] using ih a rest
              · simp [runFuel, ha, progress]

private theorem success_remaining_le {rules terms input body n result}
    (h : Derives rules terms input body n result) :
    ∀ rest, result = .ok rest → rest ≤ n := by
  induction h with
  | eps => intro rest eq; cases eq; omega
  | terminalOk _ _ progress => intro rest eq; cases eq; omega
  | terminalFail => intro rest eq; cases eq
  | call _ ih => intro rest eq; exact ih rest eq
  | seqOk _ _ ih₁ ih₂ =>
      intro rest eq
      cases eq
      exact Nat.le_trans (ih₂ _ rfl) (ih₁ _ rfl)
  | seqLeftFail | seqRightFail => intro rest eq; cases eq
  | altLeft _ ih => intro rest eq; exact ih rest eq
  | altRight _ _ _ ih => intro rest eq; exact ih rest eq
  | aheadOk => intro rest eq; cases eq; omega
  | aheadFail => intro rest eq; cases eq
  | notAheadOk => intro rest eq; cases eq; omega
  | notAheadFail => intro rest eq; cases eq
  | starFail | starZero => intro rest eq; cases eq; omega
  | starMore _ _ _ ih₁ ih₂ =>
      intro rest eq
      cases eq
      exact Nat.le_trans (ih₂ _ rfl) (ih₁ _ rfl)

theorem invariant1_runFuel_sound {rules terms input fuel body n result}
    (h : runFuel rules terms input fuel body n = some result) :
    Derives rules terms input body n result := by
  induction fuel generalizing body n result with
  | zero => simp [runFuel] at h
  | succ fuel ih =>
      cases body with
      | eps => simp [runFuel] at h; subst result; exact .eps
      | terminal index =>
          cases ht : terms index with
          | none =>
              simp [runFuel, ht] at h
              subst result
              exact .terminalFail (.inl ht)
          | some term =>
              cases ho : terminalOracle term input n with
              | none =>
                  simp [runFuel, ht, ho] at h
                  subst result
                  have rejected := (invariant1_terminalOracle_reject term input n).mp ho
                  exact .terminalFail (.inr ⟨term, ht, by
                    rintro ⟨rest, step, _⟩
                    exact rejected ⟨rest, step⟩⟩)
              | some rest =>
                  by_cases progress : rest < n
                  · simp [runFuel, ht, ho, progress] at h
                    subst result
                    exact .terminalOk ht
                      ((invariant1_terminalOracle_iff term input n rest).mp ho) progress
                  · simp [runFuel, ht, ho, progress] at h
                    subst result
                    exact .terminalFail (.inr ⟨term, ht, by
                      rintro ⟨other, step, advances⟩
                      have accepted :=
                        (invariant1_terminalOracle_iff term input n other).mpr step
                      rw [ho] at accepted
                      cases accepted
                      exact progress advances⟩)
      | call rule => exact .call (ih (by simpa [runFuel] using h))
      | seq a b =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .seqLeftFail (ih ha)
              | ok mid =>
                  cases hb : runFuel rules terms input fuel b mid with
                  | none => simp [runFuel, ha, hb] at h
                  | some rb =>
                      cases rb with
                      | fail =>
                          simp [runFuel, ha, hb] at h
                          subst result
                          exact .seqRightFail (ih ha) (ih hb)
                      | ok rest =>
                          simp [runFuel, ha, hb] at h
                          subst result
                          exact .seqOk (ih ha) (ih hb)
      | alt a b =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok rest =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .altLeft (ih ha)
              | fail =>
                  cases hb : runFuel rules terms input fuel b n with
                  | none => simp [runFuel, ha, hb] at h
                  | some rb =>
                      simp [runFuel, ha, hb] at h
                      subst result
                      exact .altRight (ih ha) (ih hb)
      | ahead a =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok rest =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .aheadOk (ih ha)
              | fail =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .aheadFail (ih ha)
      | notAhead a =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok rest =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .notAheadFail (ih ha)
              | fail =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .notAheadOk (ih ha)
      | star a =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail =>
                  simp [runFuel, ha] at h
                  subst result
                  exact .starFail (ih ha)
              | ok mid =>
                  by_cases progress : mid < n
                  · cases hb : runFuel rules terms input fuel (.star a) mid with
                    | none => simp [runFuel, ha, progress, hb] at h
                    | some rb =>
                        cases rb with
                        | fail =>
                            exact False.elim ((runFuel_star_ne_fail rules terms input fuel a mid) hb)
                        | ok rest =>
                            simp [runFuel, ha, progress, hb] at h
                            subst result
                            exact .starMore (ih ha) progress (ih hb)
                  · simp [runFuel, ha, progress] at h
                    subst result
                    -- Terminal branches and lookahead cannot increase the remaining input.
                    have same : mid = n := by
                      have consumed := success_remaining_le (ih ha) mid rfl
                      omega
                    subst mid
                    exact .starZero (ih ha)

#print axioms invariant1_runFuel_sound

-- The independent derivation must have a finite executable witness.

private theorem runFuel_mono_step (rules : Nat → Body)
    (terms : Nat → Option Terminal) (input : List Char) :
    ∀ fuel body n r, runFuel rules terms input fuel body n = some r →
      runFuel rules terms input (fuel + 1) body n = some r := by
  intro fuel
  induction fuel with
  | zero =>
      intro body n r h
      simp [runFuel] at h
  | succ fuel ih =>
      intro body n r h
      unfold runFuel at h ⊢
      cases body with
      | eps | terminal _ => simpa only [runFuel] using h
      | call rule => exact ih (rules rule) n r h
      | seq a b =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | fail => simpa only [ha, ha'] using h
              | ok m =>
                  cases hb : runFuel rules terms input fuel b m with
                  | none => simp [ha, hb] at h
                  | some rb =>
                      have hb' := ih b m rb hb
                      simpa only [ha, ha', hb, hb'] using h
      | alt a b =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | ok m => simpa only [ha, ha'] using h
              | fail =>
                  cases hb : runFuel rules terms input fuel b n with
                  | none => simp [ha, hb] at h
                  | some rb =>
                      have hb' := ih b n rb hb
                      simpa only [ha, ha', hb, hb'] using h
      | ahead a | notAhead a =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              simpa only [ha, ha'] using h
      | star a =>
          cases ha : runFuel rules terms input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | fail => simpa only [ha, ha'] using h
              | ok m =>
                  by_cases progress : m < n
                  · cases hb : runFuel rules terms input fuel (.star a) m with
                    | none => simp [ha, progress, hb] at h
                    | some rb =>
                        have hb' := ih (.star a) m rb hb
                        simpa only [ha, ha', progress, hb, hb'] using h
                  · simpa [ha, ha', progress] using h

private theorem runFuel_mono (rules : Nat → Body)
    (terms : Nat → Option Terminal) (input : List Char)
    {fuel more body n r} (le : fuel ≤ more)
    (h : runFuel rules terms input fuel body n = some r) :
    runFuel rules terms input more body n = some r := by
  obtain ⟨extra, rfl⟩ : ∃ extra, more = fuel + extra :=
    ⟨more - fuel, by omega⟩
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
      simpa [Nat.add_assoc] using
        runFuel_mono_step rules terms input (fuel + extra) body n r (ih (by omega))

#print axioms runFuel_mono_step

theorem invariant1_derivation_has_fuel {rules terms input body n r}
    (h : Derives rules terms input body n r) :
    ∃ fuel, runFuel rules terms input fuel body n = some r := by
  induction h with
  | eps => exact ⟨1, rfl⟩
  | terminalOk matched step progress =>
      have oracle := (invariant1_terminalOracle_iff _ _ _ _).mpr step
      exact ⟨1, by simp [runFuel, matched, oracle, progress]⟩
  | @terminalFail index n failure =>
      cases failure with
      | inl absent => exact ⟨1, by simp [runFuel, absent]⟩
      | inr present =>
          obtain ⟨term, matched, rejected⟩ := present
          cases oracle : terminalOracle term input n with
          | none => exact ⟨1, by simp [runFuel, matched, oracle]⟩
          | some rest =>
              have step := (invariant1_terminalOracle_iff term input n rest).mp oracle
              have noProgress : ¬rest < n := by
                intro progress
                exact rejected ⟨rest, step, progress⟩
              exact ⟨1, by simp [runFuel, matched, oracle, noProgress]⟩
  | call _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simpa [runFuel] using h⟩
  | seqOk _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules terms input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms input (Nat.le_max_right f₁ f₂) h₂
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
      have h₁' := runFuel_mono rules terms input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms input (Nat.le_max_right f₁ f₂) h₂
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
      have h₁' := runFuel_mono rules terms input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms input (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        exact h₂'⟩
  | aheadOk _ ih | aheadFail _ ih | notAheadOk _ ih | notAheadFail _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | starFail _ ih | starZero _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, h]⟩
  | starMore _ progress _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      let fuel := max f₁ f₂
      have h₁' := runFuel_mono rules terms input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms input (Nat.le_max_right f₁ f₂) h₂
      exact ⟨fuel + 1, by
        simp only [runFuel]
        dsimp [fuel]
        rw [h₁']
        simp [progress]
        exact h₂'⟩

theorem invariant1_exec_iff {rules terms input body n r} :
    Derives rules terms input body n r ↔
      ∃ fuel, runFuel rules terms input fuel body n = some r := by
  constructor
  · exact invariant1_derivation_has_fuel
  · rintro ⟨fuel, h⟩
    exact invariant1_runFuel_sound h

#print axioms invariant1_exec_iff

-- The concrete terminal relation uses the same consumption measure as the
-- extracted call-order certificate.
theorem invariant1_success_consumes {rules terms input body n r}
    (h : Derives rules terms input body n r) :
    ∀ m, r = .ok m →
      ∃ k, n = m + k ∧
        CallOrder.Consumes (fun rule => erase (rules rule)) (erase body) k := by
  induction h with
  | eps =>
      intro m eq
      cases eq
      exact ⟨0, by simp, .empty⟩
  | @terminalOk index n m _ _ _ progress =>
      intro target eq
      cases eq
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      exact ⟨k + 1, by omega, .token k⟩
  | terminalFail => intro m eq; cases eq
  | call _ ih =>
      intro m eq
      obtain ⟨k, length, consumed⟩ := ih m eq
      exact ⟨k, length, .call consumed⟩
  | seqOk _ _ ih₁ ih₂ =>
      intro target eq
      cases eq
      obtain ⟨i, len₁, consume₁⟩ := ih₁ _ rfl
      obtain ⟨j, len₂, consume₂⟩ := ih₂ _ rfl
      exact ⟨i + j, by omega, .seq consume₁ consume₂⟩
  | seqLeftFail | seqRightFail => intro m eq; cases eq
  | altLeft _ ih =>
      intro target eq
      obtain ⟨k, length, consumed⟩ := ih target eq
      exact ⟨k, length, .left consumed⟩
  | altRight _ _ ih₁ ih₂ =>
      intro target eq
      obtain ⟨k, length, consumed⟩ := ih₂ target eq
      exact ⟨k, length, .right consumed⟩
  | aheadOk | notAheadOk =>
      intro target eq
      cases eq
      exact ⟨0, by simp, .look⟩
  | aheadFail | notAheadFail => intro m eq; cases eq
  | starFail | starZero =>
      intro target eq
      cases eq
      exact ⟨0, by simp, .stop⟩
  | starMore _ _ _ ih₁ ih₂ =>
      intro target eq
      cases eq
      obtain ⟨i, len₁, consume₁⟩ := ih₁ _ rfl
      obtain ⟨j, len₂, consume₂⟩ := ih₂ _ rfl
      exact ⟨i + j, by omega, .more consume₁ consume₂⟩

#print axioms invariant1_success_consumes

inductive DirectCall (rules : Nat → Body) (terms : Nat → Option Terminal)
    (input : List Char) : Body → Nat → Nat → Nat → Prop where
  | here (rule n) : DirectCall rules terms input (.call rule) n rule n
  | seqLeft {a b n rule spot} : DirectCall rules terms input a n rule spot →
      DirectCall rules terms input (.seq a b) n rule spot
  | seqRight {a b n mid rule spot} :
      Derives rules terms input a n (.ok mid) →
      DirectCall rules terms input b mid rule spot →
      DirectCall rules terms input (.seq a b) n rule spot
  | altLeft {a b n rule spot} : DirectCall rules terms input a n rule spot →
      DirectCall rules terms input (.alt a b) n rule spot
  | altRight {a b n rule spot} : Derives rules terms input a n .fail →
      DirectCall rules terms input b n rule spot →
      DirectCall rules terms input (.alt a b) n rule spot
  | ahead {a n rule spot} : DirectCall rules terms input a n rule spot →
      DirectCall rules terms input (.ahead a) n rule spot
  | notAhead {a n rule spot} : DirectCall rules terms input a n rule spot →
      DirectCall rules terms input (.notAhead a) n rule spot
  | starFirst {a n rule spot} : DirectCall rules terms input a n rule spot →
      DirectCall rules terms input (.star a) n rule spot
  | starLater {a n mid rule spot} :
      Derives rules terms input a n (.ok mid) → mid < n →
      DirectCall rules terms input (.star a) mid rule spot →
      DirectCall rules terms input (.star a) n rule spot

theorem invariant1_direct_reaches {rules terms input body n rule spot}
    (h : DirectCall rules terms input body n rule spot) :
    ∃ k, n = spot + k ∧
      CallOrder.Reaches (fun name => erase (rules name)) (erase body) rule k := by
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
  | ahead _ ih | notAhead _ ih =>
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

#print axioms invariant1_direct_reaches

private def bodySize : Body → Nat
  | .eps | .terminal _ | .call _ => 1
  | .seq a b | .alt a b => bodySize a + bodySize b + 1
  | .ahead a | .notAhead a | .star a => bodySize a + 1

theorem invariant1_rule_total {rules known rank terms input}
    (checked : ∀ rule,
      CallOrder.validRule known rank rule (erase (rules rule)) = true) :
    ∀ state : Nat × Nat,
      ∃ r, Derives rules terms input (rules state.2) state.1 r := by
  intro state
  induction state using (CallOrder.invariant1_call_wellFounded checked).induction with
  | h state ih =>
      have descend {callee spot}
          (nested : CallOrder.Nested (fun rule => erase (rules rule))
            (spot, callee) state) :
          ∃ r, Derives rules terms input (rules callee) spot r :=
        ih (spot, callee) nested
      let rec go (body : Body) (n : Nat)
          (lift : ∀ callee spot,
            DirectCall rules terms input body n callee spot →
            CallOrder.Nested (fun rule => erase (rules rule))
              (spot, callee) state) :
          ∃ r, Derives rules terms input body n r := by
        cases body with
        | eps => exact ⟨.ok n, .eps⟩
        | terminal index =>
            cases ht : terms index with
            | none => exact ⟨.fail, .terminalFail (.inl ht)⟩
            | some term =>
                cases ho : terminalOracle term input n with
                | none =>
                    have rejected := (invariant1_terminalOracle_reject term input n).mp ho
                    exact ⟨.fail, .terminalFail (.inr ⟨term, ht, by
                      rintro ⟨rest, step, _⟩
                      exact rejected ⟨rest, step⟩⟩)⟩
                | some rest =>
                    have step := (invariant1_terminalOracle_iff term input n rest).mp ho
                    by_cases progress : rest < n
                    · exact ⟨.ok rest, .terminalOk ht step progress⟩
                    · exact ⟨.fail, .terminalFail (.inr ⟨term, ht, by
                        rintro ⟨other, otherStep, advances⟩
                        have accepted :=
                          (invariant1_terminalOracle_iff term input n other).mpr otherStep
                        rw [ho] at accepted
                        cases accepted
                        exact progress advances⟩)⟩
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
                exact ⟨rb, .altRight evaluatedA evaluatedB⟩
        | ahead a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.ahead call))
            cases ra with
            | ok m => exact ⟨.ok n, .aheadOk evaluatedA⟩
            | fail => exact ⟨.fail, .aheadFail evaluatedA⟩
        | notAhead a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.notAhead call))
            cases ra with
            | ok m => exact ⟨.fail, .notAheadFail evaluatedA⟩
            | fail => exact ⟨.ok n, .notAheadOk evaluatedA⟩
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
                  | fail => exact ⟨.fail, by cases evaluatedB⟩
                · have same : m = n := by
                    have bounded := success_remaining_le evaluatedA m rfl
                    omega
                  subst m
                  exact ⟨.ok n, .starZero evaluatedA⟩
      termination_by (n, bodySize body)
      decreasing_by
        all_goals simp_wf
        all_goals try (have bounded := success_remaining_le evaluatedA _ rfl)
        all_goals simp_all [bodySize]
        all_goals omega
      exact go (rules state.2) state.1 (fun callee spot call =>
        invariant1_direct_reaches call)

theorem invariant1_rule_executable {rules known rank terms input}
    (checked : ∀ rule,
      CallOrder.validRule known rank rule (erase (rules rule)) = true)
    (state : Nat × Nat) :
    ∃ fuel r,
      runFuel rules terms input fuel (rules state.2) state.1 = some r := by
  obtain ⟨r, derivation⟩ := invariant1_rule_total checked state
  obtain ⟨fuel, h⟩ := invariant1_derivation_has_fuel derivation
  exact ⟨fuel, r, h⟩

#print axioms invariant1_rule_executable

end PegHs.ConcreteTerminalBody
