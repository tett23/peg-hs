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

end PegHs.ConcreteTerminalBody
