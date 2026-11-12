import ConcreteTerminalBody

namespace PegHs.LabeledConcreteBody

open PegHs.ConcreteTerminal

inductive Body where
  | eps
  | terminal (index : Nat)
  | predicate (site : Nat) (polarity : Bool)
  | call (rule : Nat)
  | seq (a b : Body)
  | alt (a b : Body)
  | ahead (a : Body)
  | notAhead (a : Body)
  | star (a : Body)
  | label (name : String) (message : Option String) (a : Body)
  deriving DecidableEq, Repr

inductive Result where
  | ok (remaining : Nat)
  | fail
  | throwLabel (remaining : Nat) (name : String) (message : Option String)
  deriving DecidableEq, Repr

def erase : Body → PegHs.CallOrder.Body
  | .eps | .predicate _ _ => .eps
  | .terminal _ => .token
  | .call rule => .call rule
  | .seq a b => .seq (erase a) (erase b)
  | .alt a b => .alt (erase a) (erase b)
  | .ahead a | .notAhead a => .look (erase a)
  | .star a => .star (erase a)
  | .label _ _ a => erase a

-- predicateOracle receives the predicate site and the character position.
-- The generated site table keeps the source, polarity, and containing rule.
def runFuel (rules : Nat → Body) (terms : Nat → Option Terminal)
    (predicateOracle : Nat → Nat → Bool) (input : List Char) :
    Nat → Body → Nat → Option Result
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
      | .predicate site polarity =>
          if predicateOracle site (input.length - remaining) == polarity
          then some (.ok remaining) else some .fail
      | .call rule => runFuel rules terms predicateOracle input fuel (rules rule) remaining
      | .seq a b =>
          match runFuel rules terms predicateOracle input fuel a remaining with
          | none => none
          | some (.ok rest) => runFuel rules terms predicateOracle input fuel b rest
          | some .fail => some .fail
          | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
      | .alt a b =>
          match runFuel rules terms predicateOracle input fuel a remaining with
          | none => none
          | some .fail => runFuel rules terms predicateOracle input fuel b remaining
          | some result => some result
      | .ahead a =>
          match runFuel rules terms predicateOracle input fuel a remaining with
          | none => none
          | some (.ok _) => some (.ok remaining)
          | some _ => some .fail
      | .notAhead a =>
          match runFuel rules terms predicateOracle input fuel a remaining with
          | none => none
          | some (.ok _) => some .fail
          | some _ => some (.ok remaining)
      | .star a =>
          match runFuel rules terms predicateOracle input fuel a remaining with
          | none => none
          | some .fail => some (.ok remaining)
          | some (.throwLabel pos name msg) => some (.throwLabel pos name msg)
          | some (.ok rest) =>
              if rest < remaining
              then runFuel rules terms predicateOracle input fuel (.star a) rest
              else some (.ok remaining)
      | .label name msg a =>
          match runFuel rules terms predicateOracle input fuel a remaining with
          | none => none
          | some .fail => some (.throwLabel remaining name msg)
          | some result => some result

-- A labelled failure inside an ordered choice is not an ordinary failure.
example : runFuel (fun _ => .eps) (fun _ => none) (fun _ _ => false)
    [] 3 (.alt (.label "inner" none (.terminal 0)) .eps) 0 =
      some (.throwLabel 0 "inner" none) := by rfl

example : runFuel (fun _ => .eps) (fun _ => none) (fun _ _ => false)
    [] 3 (.ahead (.label "inner" none (.terminal 0))) 0 = some .fail := by rfl

example : runFuel (fun _ => .eps) (fun _ => none) (fun _ _ => false)
    [] 3 (.notAhead (.label "inner" none (.terminal 0))) 0 = some (.ok 0) := by rfl

example : runFuel (fun _ => .eps) (fun _ => none) (fun _ _ => false)
    [] 3 (.star (.label "inner" none (.terminal 0))) 0 =
      some (.throwLabel 0 "inner" none) := by rfl

example : runFuel (fun _ => .eps) (fun _ => none) (fun _ _ => false)
    [] 2 (.predicate 0 false) 0 = some (.ok 0) := by rfl

example : runFuel (fun _ => .eps) (fun _ => none) (fun _ _ => false)
    [] 2 (.predicate 0 true) 0 = some .fail := by rfl

-- Independent big-step outcome relation. Throw is distinct from PEG failure.
inductive Derives (rules : Nat → Body) (terms : Nat → Option Terminal)
    (predicateOracle : Nat → Nat → Bool) (input : List Char) :
    Body → Nat → Result → Prop where
  | eps {n} : Derives rules terms predicateOracle input .eps n (.ok n)
  | terminalOk {index n rest term} :
      terms index = some term → TerminalStep term input n rest → rest < n →
      Derives rules terms predicateOracle input (.terminal index) n (.ok rest)
  | terminalFail {index n} :
      (terms index = none ∨
        ∃ term, terms index = some term ∧
          ¬∃ rest, TerminalStep term input n rest ∧ rest < n) →
      Derives rules terms predicateOracle input (.terminal index) n .fail
  | predicateOk {site polarity n} :
      (predicateOracle site (input.length - n) == polarity) = true →
      Derives rules terms predicateOracle input (.predicate site polarity) n (.ok n)
  | predicateFail {site polarity n} :
      (predicateOracle site (input.length - n) == polarity) = false →
      Derives rules terms predicateOracle input (.predicate site polarity) n .fail
  | call {rule n r} : Derives rules terms predicateOracle input (rules rule) n r →
      Derives rules terms predicateOracle input (.call rule) n r
  | seqOk {a b n mid r} :
      Derives rules terms predicateOracle input a n (.ok mid) →
      Derives rules terms predicateOracle input b mid r →
      Derives rules terms predicateOracle input (.seq a b) n r
  | seqFail {a b n} : Derives rules terms predicateOracle input a n .fail →
      Derives rules terms predicateOracle input (.seq a b) n .fail
  | seqThrow {a b n pos name msg} :
      Derives rules terms predicateOracle input a n (.throwLabel pos name msg) →
      Derives rules terms predicateOracle input (.seq a b) n (.throwLabel pos name msg)
  | altOk {a b n r} : Derives rules terms predicateOracle input a n r →
      r ≠ .fail → Derives rules terms predicateOracle input (.alt a b) n r
  | altRetry {a b n r} : Derives rules terms predicateOracle input a n .fail →
      Derives rules terms predicateOracle input b n r →
      Derives rules terms predicateOracle input (.alt a b) n r
  | aheadOk {a n rest} : Derives rules terms predicateOracle input a n (.ok rest) →
      Derives rules terms predicateOracle input (.ahead a) n (.ok n)
  | aheadFail {a n} : Derives rules terms predicateOracle input a n .fail →
      Derives rules terms predicateOracle input (.ahead a) n .fail
  | aheadCatch {a n pos name msg} :
      Derives rules terms predicateOracle input a n (.throwLabel pos name msg) →
      Derives rules terms predicateOracle input (.ahead a) n .fail
  | notAheadFail {a n rest} : Derives rules terms predicateOracle input a n (.ok rest) →
      Derives rules terms predicateOracle input (.notAhead a) n .fail
  | notAheadOk {a n} : Derives rules terms predicateOracle input a n .fail →
      Derives rules terms predicateOracle input (.notAhead a) n (.ok n)
  | notAheadCatch {a n pos name msg} :
      Derives rules terms predicateOracle input a n (.throwLabel pos name msg) →
      Derives rules terms predicateOracle input (.notAhead a) n (.ok n)
  | starStop {a n} : Derives rules terms predicateOracle input a n .fail →
      Derives rules terms predicateOracle input (.star a) n (.ok n)
  | starZero {a n} : Derives rules terms predicateOracle input a n (.ok n) →
      Derives rules terms predicateOracle input (.star a) n (.ok n)
  | starMore {a n mid rest} : Derives rules terms predicateOracle input a n (.ok mid) →
      mid < n → Derives rules terms predicateOracle input (.star a) mid (.ok rest) →
      Derives rules terms predicateOracle input (.star a) n (.ok rest)
  | starMoreThrow {a n mid pos name msg} :
      Derives rules terms predicateOracle input a n (.ok mid) → mid < n →
      Derives rules terms predicateOracle input (.star a) mid (.throwLabel pos name msg) →
      Derives rules terms predicateOracle input (.star a) n (.throwLabel pos name msg)
  | starThrow {a n pos name msg} :
      Derives rules terms predicateOracle input a n (.throwLabel pos name msg) →
      Derives rules terms predicateOracle input (.star a) n (.throwLabel pos name msg)
  | labelOk {a n rest name msg} :
      Derives rules terms predicateOracle input a n (.ok rest) →
      Derives rules terms predicateOracle input (.label name msg a) n (.ok rest)
  | labelFail {a n name msg} :
      Derives rules terms predicateOracle input a n .fail →
      Derives rules terms predicateOracle input (.label name msg a) n (.throwLabel n name msg)
  | labelThrow {a n pos name msg innerName innerMsg} :
      Derives rules terms predicateOracle input a n (.throwLabel pos innerName innerMsg) →
      Derives rules terms predicateOracle input (.label name msg a) n
        (.throwLabel pos innerName innerMsg)

private theorem success_remaining_le {rules terms predicateOracle input body n result}
    (h : Derives rules terms predicateOracle input body n result) :
    ∀ rest, result = .ok rest → rest ≤ n := by
  induction h with
  | eps => intro rest eq; cases eq; omega
  | terminalOk _ _ progress => intro rest eq; cases eq; omega
  | terminalFail | predicateFail | seqFail | seqThrow | aheadFail | aheadCatch |
    notAheadFail | starThrow | starMoreThrow | labelFail | labelThrow =>
      intro rest eq; cases eq
  | predicateOk => intro rest eq; cases eq; omega
  | call _ ih => intro rest eq; exact ih rest eq
  | seqOk _ _ ih₁ ih₂ =>
      intro rest eq
      exact Nat.le_trans (ih₂ rest eq) (ih₁ _ rfl)
  | altOk _ _ ih => intro rest eq; exact ih rest eq
  | altRetry _ _ _ ih => intro rest eq; exact ih rest eq
  | aheadOk | notAheadOk | notAheadCatch | starStop | starZero =>
      intro rest eq; cases eq; omega
  | starMore _ _ _ ih₁ ih₂ =>
      intro rest eq
      exact Nat.le_trans (ih₂ rest eq) (ih₁ _ rfl)
  | labelOk _ ih => intro rest eq; exact ih rest eq

private theorem star_ne_fail {rules terms predicateOracle input fuel a n} :
    runFuel rules terms predicateOracle input fuel (.star a) n ≠ some .fail := by
  induction fuel generalizing n with
  | zero => simp [runFuel]
  | succ fuel ih =>
      cases ha : runFuel rules terms predicateOracle input fuel a n with
      | none => simp [runFuel, ha]
      | some ra =>
          cases ra with
          | fail => simp [runFuel, ha]
          | throwLabel _ _ _ => simp [runFuel, ha]
          | ok rest =>
              by_cases progress : rest < n
              · simpa [runFuel, ha, progress] using ih (n := rest)
              · simp [runFuel, ha, progress]

theorem invariant1_runFuel_sound {rules terms predicateOracle input fuel body n r}
    (h : runFuel rules terms predicateOracle input fuel body n = some r) :
    Derives rules terms predicateOracle input body n r := by
  induction fuel generalizing body n r with
  | zero => simp [runFuel] at h
  | succ fuel ih =>
      cases body with
      | eps => simp [runFuel] at h; subst r; exact .eps
      | terminal index =>
          cases ht : terms index with
          | none => simp [runFuel, ht] at h; subst r; exact .terminalFail (.inl ht)
          | some term =>
              cases ho : terminalOracle term input n with
              | none =>
                  simp [runFuel, ht, ho] at h
                  subst r
                  have rejected := (invariant1_terminalOracle_reject term input n).mp ho
                  exact .terminalFail (.inr ⟨term, ht, by
                    rintro ⟨rest, step, _⟩
                    exact rejected ⟨rest, step⟩⟩)
              | some rest =>
                  by_cases progress : rest < n
                  · simp [runFuel, ht, ho, progress] at h
                    subst r
                    exact .terminalOk ht
                      ((invariant1_terminalOracle_iff term input n rest).mp ho) progress
                  · simp [runFuel, ht, ho, progress] at h
                    subst r
                    exact .terminalFail (.inr ⟨term, ht, by
                      rintro ⟨other, step, advances⟩
                      have accepted :=
                        (invariant1_terminalOracle_iff term input n other).mpr step
                      rw [ho] at accepted
                      cases accepted
                      exact progress advances⟩)
      | predicate site polarity =>
          by_cases hmatch : (predicateOracle site (input.length - n) == polarity) = true
          · simp [runFuel, hmatch] at h
            subst r
            exact .predicateOk hmatch
          · have rejected : (predicateOracle site (input.length - n) == polarity) = false := by
              cases value : (predicateOracle site (input.length - n) == polarity) <;> simp_all
            simp [runFuel, rejected] at h
            subst r
            exact .predicateFail rejected
      | call rule => exact .call (ih (by simpa [runFuel] using h))
      | seq a b =>
          cases ha : runFuel rules terms predicateOracle input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail => simp [runFuel, ha] at h; subst r; exact .seqFail (ih ha)
              | throwLabel pos name msg =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .seqThrow (ih ha)
              | ok mid =>
                  cases hb : runFuel rules terms predicateOracle input fuel b mid with
                  | none => simp [runFuel, ha, hb] at h
                  | some rb =>
                      simp [runFuel, ha, hb] at h
                      subst r
                      exact .seqOk (ih ha) (ih hb)
      | alt a b =>
          cases ha : runFuel rules terms predicateOracle input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail =>
                  cases hb : runFuel rules terms predicateOracle input fuel b n with
                  | none => simp [runFuel, ha, hb] at h
                  | some rb =>
                      simp [runFuel, ha, hb] at h
                      subst r
                      exact .altRetry (ih ha) (ih hb)
              | ok rest =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .altOk (ih ha) (by simp)
              | throwLabel pos name msg =>
                  simp [runFuel, ha] at h
                  subst r
                  exact .altOk (ih ha) (by simp)
      | ahead a =>
          cases ha : runFuel rules terms predicateOracle input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok rest => simp [runFuel, ha] at h; subst r; exact .aheadOk (ih ha)
              | fail => simp [runFuel, ha] at h; subst r; exact .aheadFail (ih ha)
              | throwLabel pos name msg =>
                  simp [runFuel, ha] at h; subst r; exact .aheadCatch (ih ha)
      | notAhead a =>
          cases ha : runFuel rules terms predicateOracle input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | ok rest => simp [runFuel, ha] at h; subst r; exact .notAheadFail (ih ha)
              | fail => simp [runFuel, ha] at h; subst r; exact .notAheadOk (ih ha)
              | throwLabel pos name msg =>
                  simp [runFuel, ha] at h; subst r; exact .notAheadCatch (ih ha)
      | star a =>
          cases ha : runFuel rules terms predicateOracle input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail => simp [runFuel, ha] at h; subst r; exact .starStop (ih ha)
              | throwLabel pos name msg =>
                  simp [runFuel, ha] at h; subst r; exact .starThrow (ih ha)
              | ok mid =>
                  by_cases progress : mid < n
                  · cases hb : runFuel rules terms predicateOracle input fuel (.star a) mid with
                    | none => simp [runFuel, ha, progress, hb] at h
                    | some rb =>
                        cases rb with
                        | fail => exact False.elim (star_ne_fail hb)
                        | ok rest =>
                            simp [runFuel, ha, progress, hb] at h
                            subst r
                            exact .starMore (ih ha) progress (ih hb)
                        | throwLabel pos name msg =>
                            simp [runFuel, ha, progress, hb] at h
                            subst r
                            exact .starMoreThrow (ih ha) progress (ih hb)
                  · simp [runFuel, ha, progress] at h
                    subst r
                    have same : mid = n := by
                      have bounded := success_remaining_le (ih ha) mid rfl
                      omega
                    subst mid
                    exact .starZero (ih ha)
      | label name msg a =>
          cases ha : runFuel rules terms predicateOracle input fuel a n with
          | none => simp [runFuel, ha] at h
          | some ra =>
              cases ra with
              | fail => simp [runFuel, ha] at h; subst r; exact .labelFail (ih ha)
              | ok rest => simp [runFuel, ha] at h; subst r; exact .labelOk (ih ha)
              | throwLabel pos innerName innerMsg =>
                  simp [runFuel, ha] at h; subst r; exact .labelThrow (ih ha)

#print axioms invariant1_runFuel_sound

private theorem runFuel_mono_step (rules : Nat → Body)
    (terms : Nat → Option Terminal) (oracle : Nat → Nat → Bool) (input : List Char) :
    ∀ fuel body n r, runFuel rules terms oracle input fuel body n = some r →
      runFuel rules terms oracle input (fuel + 1) body n = some r := by
  intro fuel
  induction fuel with
  | zero => intro body n r h; simp [runFuel] at h
  | succ fuel ih =>
      intro body n r h
      unfold runFuel at h ⊢
      cases body with
      | eps | terminal _ | predicate _ _ => simpa only [runFuel] using h
      | call rule => exact ih (rules rule) n r h
      | seq a b =>
          cases ha : runFuel rules terms oracle input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | fail | throwLabel _ _ _ => simpa only [ha, ha'] using h
              | ok m =>
                  cases hb : runFuel rules terms oracle input fuel b m with
                  | none => simp [ha, hb] at h
                  | some rb =>
                      have hb' := ih b m rb hb
                      simpa only [ha, ha', hb, hb'] using h
      | alt a b =>
          cases ha : runFuel rules terms oracle input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | ok _ | throwLabel _ _ _ => simpa only [ha, ha'] using h
              | fail =>
                  cases hb : runFuel rules terms oracle input fuel b n with
                  | none => simp [ha, hb] at h
                  | some rb =>
                      have hb' := ih b n rb hb
                      simpa only [ha, ha', hb, hb'] using h
      | ahead a | notAhead a | label _ _ a =>
          cases ha : runFuel rules terms oracle input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              simpa only [ha, ha'] using h
      | star a =>
          cases ha : runFuel rules terms oracle input fuel a n with
          | none => simp [ha] at h
          | some ra =>
              have ha' := ih a n ra ha
              cases ra with
              | fail | throwLabel _ _ _ => simpa only [ha, ha'] using h
              | ok m =>
                  by_cases progress : m < n
                  · cases hb : runFuel rules terms oracle input fuel (.star a) m with
                    | none => simp [ha, progress, hb] at h
                    | some rb =>
                        have hb' := ih (.star a) m rb hb
                        simpa only [ha, ha', progress, hb, hb'] using h
                  · simpa [ha, ha', progress] using h

private theorem runFuel_mono (rules : Nat → Body)
    (terms : Nat → Option Terminal) (oracle : Nat → Nat → Bool) (input : List Char)
    {fuel more body n r} (le : fuel ≤ more)
    (h : runFuel rules terms oracle input fuel body n = some r) :
    runFuel rules terms oracle input more body n = some r := by
  obtain ⟨extra, rfl⟩ : ∃ extra, more = fuel + extra :=
    ⟨more - fuel, by omega⟩
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
      simpa [Nat.add_assoc] using
        runFuel_mono_step rules terms oracle input (fuel + extra) body n r (ih (by omega))

#print axioms runFuel_mono_step

theorem invariant1_derivation_has_fuel {rules terms oracle input body n r}
    (h : Derives rules terms oracle input body n r) :
    ∃ fuel, runFuel rules terms oracle input fuel body n = some r := by
  induction h with
  | eps => exact ⟨1, rfl⟩
  | terminalOk matched step progress =>
      have oracleHit := (invariant1_terminalOracle_iff _ _ _ _).mpr step
      exact ⟨1, by simp [runFuel, matched, oracleHit, progress]⟩
  | @terminalFail index n failure =>
      cases failure with
      | inl absent => exact ⟨1, by simp [runFuel, absent]⟩
      | inr present =>
          obtain ⟨term, matched, rejected⟩ := present
          cases hit : terminalOracle term input n with
          | none => exact ⟨1, by simp [runFuel, matched, hit]⟩
          | some rest =>
              have step := (invariant1_terminalOracle_iff term input n rest).mp hit
              have noProgress : ¬rest < n := fun p => rejected ⟨rest, step, p⟩
              exact ⟨1, by simp [runFuel, matched, hit, noProgress]⟩
  | predicateOk accepted => exact ⟨1, by simp [runFuel, accepted]⟩
  | predicateFail rejected => exact ⟨1, by simp [runFuel, rejected]⟩
  | call _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simpa [runFuel] using result⟩
  | seqOk _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := runFuel_mono rules terms oracle input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms oracle input (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', h₂']⟩
  | seqFail _ ih | seqThrow _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | @altOk a b n branchResult evaluated notFail ih =>
      obtain ⟨fuel, result⟩ := ih
      cases branchResult with
      | fail => exact False.elim (notFail rfl)
      | ok _ => exact ⟨fuel + 1, by simp [runFuel, result]⟩
      | throwLabel _ _ _ => exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | altRetry _ _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := runFuel_mono rules terms oracle input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms oracle input (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', h₂']⟩
  | aheadOk _ ih | aheadFail _ ih | aheadCatch _ ih
  | notAheadFail _ ih | notAheadOk _ ih | notAheadCatch _ ih
  | starStop _ ih | starThrow _ ih | labelOk _ ih | labelFail _ ih
  | labelThrow _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | starZero _ ih =>
      obtain ⟨fuel, result⟩ := ih
      exact ⟨fuel + 1, by simp [runFuel, result]⟩
  | starMore _ progress _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := runFuel_mono rules terms oracle input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms oracle input (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', progress, h₂']⟩
  | starMoreThrow _ progress _ ih₁ ih₂ =>
      obtain ⟨f₁, h₁⟩ := ih₁
      obtain ⟨f₂, h₂⟩ := ih₂
      have h₁' := runFuel_mono rules terms oracle input (Nat.le_max_left f₁ f₂) h₁
      have h₂' := runFuel_mono rules terms oracle input (Nat.le_max_right f₁ f₂) h₂
      exact ⟨max f₁ f₂ + 1, by simp [runFuel, h₁', progress, h₂']⟩

theorem invariant1_exec_iff {rules terms oracle input body n r} :
    Derives rules terms oracle input body n r ↔
      ∃ fuel, runFuel rules terms oracle input fuel body n = some r := by
  constructor
  · exact invariant1_derivation_has_fuel
  · rintro ⟨fuel, h⟩
    exact invariant1_runFuel_sound h

#print axioms invariant1_exec_iff

theorem invariant1_success_consumes {rules terms oracle input body n r}
    (h : Derives rules terms oracle input body n r) :
    ∀ m, r = .ok m →
      ∃ k, n = m + k ∧
        PegHs.CallOrder.Consumes (fun rule => erase (rules rule)) (erase body) k := by
  induction h with
  | eps | predicateOk =>
      intro m eq
      cases eq
      exact ⟨0, by simp, .empty⟩
  | @terminalOk index n m _ _ _ progress =>
      intro target eq
      cases eq
      obtain ⟨k, hk⟩ : ∃ k, n - m = k + 1 := ⟨n - m - 1, by omega⟩
      exact ⟨k + 1, by omega, .token k⟩
  | terminalFail | predicateFail | seqFail | seqThrow | aheadFail | aheadCatch |
    notAheadFail | starThrow | starMoreThrow | labelFail | labelThrow =>
      intro m eq; cases eq
  | call _ ih =>
      intro m eq
      obtain ⟨k, length, consumed⟩ := ih m eq
      exact ⟨k, length, .call consumed⟩
  | seqOk _ _ ih₁ ih₂ =>
      intro target eq
      obtain ⟨i, len₁, consume₁⟩ := ih₁ _ rfl
      obtain ⟨j, len₂, consume₂⟩ := ih₂ target eq
      exact ⟨i + j, by omega, .seq consume₁ consume₂⟩
  | altOk _ _ ih =>
      intro target eq
      obtain ⟨k, length, consumed⟩ := ih target eq
      exact ⟨k, length, .left consumed⟩
  | altRetry _ _ _ ih =>
      intro target eq
      obtain ⟨k, length, consumed⟩ := ih target eq
      exact ⟨k, length, .right consumed⟩
  | aheadOk | notAheadOk | notAheadCatch =>
      intro target eq
      cases eq
      exact ⟨0, by simp, .look⟩
  | starStop | starZero =>
      intro target eq
      cases eq
      exact ⟨0, by simp, .stop⟩
  | starMore _ _ _ ih₁ ih₂ =>
      intro target eq
      obtain ⟨i, len₁, consume₁⟩ := ih₁ _ rfl
      obtain ⟨j, len₂, consume₂⟩ := ih₂ target eq
      exact ⟨i + j, by omega, .more consume₁ consume₂⟩
  | labelOk _ ih =>
      intro target eq
      exact ih target eq

#print axioms invariant1_success_consumes

inductive DirectCall (rules : Nat → Body) (terms : Nat → Option Terminal)
    (oracle : Nat → Nat → Bool) (input : List Char) :
    Body → Nat → Nat → Nat → Prop where
  | here (rule n) : DirectCall rules terms oracle input (.call rule) n rule n
  | seqLeft {a b n rule spot} : DirectCall rules terms oracle input a n rule spot →
      DirectCall rules terms oracle input (.seq a b) n rule spot
  | seqRight {a b n mid rule spot} :
      Derives rules terms oracle input a n (.ok mid) →
      DirectCall rules terms oracle input b mid rule spot →
      DirectCall rules terms oracle input (.seq a b) n rule spot
  | altLeft {a b n rule spot} : DirectCall rules terms oracle input a n rule spot →
      DirectCall rules terms oracle input (.alt a b) n rule spot
  | altRight {a b n rule spot} : Derives rules terms oracle input a n .fail →
      DirectCall rules terms oracle input b n rule spot →
      DirectCall rules terms oracle input (.alt a b) n rule spot
  | ahead {a n rule spot} : DirectCall rules terms oracle input a n rule spot →
      DirectCall rules terms oracle input (.ahead a) n rule spot
  | notAhead {a n rule spot} : DirectCall rules terms oracle input a n rule spot →
      DirectCall rules terms oracle input (.notAhead a) n rule spot
  | starFirst {a n rule spot} : DirectCall rules terms oracle input a n rule spot →
      DirectCall rules terms oracle input (.star a) n rule spot
  | starLater {a n mid rule spot} :
      Derives rules terms oracle input a n (.ok mid) → mid < n →
      DirectCall rules terms oracle input (.star a) mid rule spot →
      DirectCall rules terms oracle input (.star a) n rule spot
  | label {a n rule spot name msg} :
      DirectCall rules terms oracle input a n rule spot →
      DirectCall rules terms oracle input (.label name msg a) n rule spot

theorem invariant1_direct_reaches {rules terms oracle input body n rule spot}
    (h : DirectCall rules terms oracle input body n rule spot) :
    ∃ k, n = spot + k ∧
      PegHs.CallOrder.Reaches (fun name => erase (rules name)) (erase body) rule k := by
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
  | label _ ih => exact ih

#print axioms invariant1_direct_reaches

private def bodySize : Body → Nat
  | .eps | .terminal _ | .predicate _ _ | .call _ => 1
  | .seq a b | .alt a b => bodySize a + bodySize b + 1
  | .ahead a | .notAhead a | .star a | .label _ _ a => bodySize a + 1

theorem invariant1_rule_total {rules known rank terms oracle input}
    (checked : ∀ rule,
      PegHs.CallOrder.validRule known rank rule (erase (rules rule)) = true) :
    ∀ state : Nat × Nat,
      ∃ r, Derives rules terms oracle input (rules state.2) state.1 r := by
  intro state
  induction state using (PegHs.CallOrder.invariant1_call_wellFounded checked).induction with
  | h state ih =>
      have descend {callee spot}
          (nested : PegHs.CallOrder.Nested (fun rule => erase (rules rule))
            (spot, callee) state) :
          ∃ r, Derives rules terms oracle input (rules callee) spot r :=
        ih (spot, callee) nested
      let rec go (body : Body) (n : Nat)
          (lift : ∀ callee spot,
            DirectCall rules terms oracle input body n callee spot →
            PegHs.CallOrder.Nested (fun rule => erase (rules rule))
              (spot, callee) state) :
          ∃ r, Derives rules terms oracle input body n r := by
        cases body with
        | eps => exact ⟨.ok n, .eps⟩
        | terminal index =>
            cases ht : terms index with
            | none => exact ⟨.fail, .terminalFail (.inl ht)⟩
            | some term =>
                cases hit : terminalOracle term input n with
                | none =>
                    have rejected := (invariant1_terminalOracle_reject term input n).mp hit
                    exact ⟨.fail, .terminalFail (.inr ⟨term, ht, by
                      rintro ⟨rest, step, _⟩
                      exact rejected ⟨rest, step⟩⟩)⟩
                | some rest =>
                    have step := (invariant1_terminalOracle_iff term input n rest).mp hit
                    by_cases progress : rest < n
                    · exact ⟨.ok rest, .terminalOk ht step progress⟩
                    · exact ⟨.fail, .terminalFail (.inr ⟨term, ht, by
                        rintro ⟨other, otherStep, advances⟩
                        have accepted :=
                          (invariant1_terminalOracle_iff term input n other).mpr otherStep
                        rw [hit] at accepted
                        cases accepted
                        exact progress advances⟩)⟩
        | predicate site polarity =>
            cases hpred : (oracle site (input.length - n) == polarity) with
            | false => exact ⟨.fail, .predicateFail hpred⟩
            | true => exact ⟨.ok n, .predicateOk hpred⟩
        | call callee =>
            obtain ⟨r, evaluated⟩ := descend (lift callee n (.here callee n))
            exact ⟨r, .call evaluated⟩
        | seq a b =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.seqLeft call))
            cases ra with
            | fail => exact ⟨.fail, .seqFail evaluatedA⟩
            | throwLabel pos name msg => exact ⟨.throwLabel pos name msg, .seqThrow evaluatedA⟩
            | ok m =>
                obtain ⟨rb, evaluatedB⟩ := go b m (fun callee spot call =>
                  lift callee spot (.seqRight evaluatedA call))
                exact ⟨rb, .seqOk evaluatedA evaluatedB⟩
        | alt a b =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.altLeft call))
            cases ra with
            | ok m => exact ⟨.ok m, .altOk evaluatedA (by simp)⟩
            | throwLabel pos name msg =>
                exact ⟨.throwLabel pos name msg, .altOk evaluatedA (by simp)⟩
            | fail =>
                obtain ⟨rb, evaluatedB⟩ := go b n (fun callee spot call =>
                  lift callee spot (.altRight evaluatedA call))
                exact ⟨rb, .altRetry evaluatedA evaluatedB⟩
        | ahead a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.ahead call))
            cases ra with
            | ok m => exact ⟨.ok n, .aheadOk evaluatedA⟩
            | fail => exact ⟨.fail, .aheadFail evaluatedA⟩
            | throwLabel pos name msg => exact ⟨.fail, .aheadCatch evaluatedA⟩
        | notAhead a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.notAhead call))
            cases ra with
            | ok m => exact ⟨.fail, .notAheadFail evaluatedA⟩
            | fail => exact ⟨.ok n, .notAheadOk evaluatedA⟩
            | throwLabel pos name msg => exact ⟨.ok n, .notAheadCatch evaluatedA⟩
        | star a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.starFirst call))
            cases ra with
            | fail => exact ⟨.ok n, .starStop evaluatedA⟩
            | throwLabel pos name msg =>
                exact ⟨.throwLabel pos name msg, .starThrow evaluatedA⟩
            | ok m =>
                by_cases progress : m < n
                · obtain ⟨rb, evaluatedB⟩ := go (.star a) m (fun callee spot call =>
                    lift callee spot (.starLater evaluatedA progress call))
                  cases rb with
                  | ok k => exact ⟨.ok k, .starMore evaluatedA progress evaluatedB⟩
                  | throwLabel pos name msg =>
                      exact ⟨.throwLabel pos name msg, .starMoreThrow evaluatedA progress evaluatedB⟩
                  | fail => exact ⟨.fail, by cases evaluatedB⟩
                · have same : m = n := by
                    have bounded := success_remaining_le evaluatedA m rfl
                    omega
                  subst m
                  exact ⟨.ok n, .starZero evaluatedA⟩
        | label name msg a =>
            obtain ⟨ra, evaluatedA⟩ := go a n (fun callee spot call =>
              lift callee spot (.label call))
            cases ra with
            | ok rest => exact ⟨.ok rest, .labelOk evaluatedA⟩
            | fail => exact ⟨.throwLabel n name msg, .labelFail evaluatedA⟩
            | throwLabel pos innerName innerMsg =>
                exact ⟨.throwLabel pos innerName innerMsg, .labelThrow evaluatedA⟩
      termination_by (n, bodySize body)
      decreasing_by
        all_goals simp_wf
        all_goals try (have bounded := success_remaining_le evaluatedA _ rfl)
        all_goals simp_all [bodySize]
        all_goals omega
      exact go (rules state.2) state.1 (fun callee spot call =>
        invariant1_direct_reaches call)

theorem invariant1_rule_executable {rules known rank terms oracle input}
    (checked : ∀ rule,
      PegHs.CallOrder.validRule known rank rule (erase (rules rule)) = true)
    (state : Nat × Nat) :
    ∃ fuel r,
      runFuel rules terms oracle input fuel (rules state.2) state.1 = some r := by
  obtain ⟨r, derivation⟩ := invariant1_rule_total checked state
  obtain ⟨fuel, h⟩ := invariant1_derivation_has_fuel derivation
  exact ⟨fuel, r, h⟩

#print axioms invariant1_rule_executable

end PegHs.LabeledConcreteBody
