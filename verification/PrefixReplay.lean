import MetaExecution
import TerminalCursor
import CaptureWindow

namespace PegHs.EnvironmentEval
open ConcreteTerminal

private theorem prepend_oracle (term : Terminal) (pre input : List Char) (n : Nat)
    (bound : n ≤ input.length) :
    terminalOracle term (pre ++ input) n = terminalOracle term input n := by
  let k := input.length - n
  have splitInput := List.take_append_drop k input
  have len : (input.drop k).length = n := by simp [k]; omega
  have one := invariant1_oracle_at_cursor (term := term) splitInput.symm len.symm
  have two := invariant1_oracle_at_cursor (term := term) (before := pre ++ input.take k)
    (suffix := input.drop k) (source := pre ++ input)
    (by simp [List.append_assoc]) len.symm
  exact two.trans one.symm

private theorem prepend_step (term : Terminal) (pre input : List Char) (n rest : Nat)
    (bound : n ≤ input.length) :
    TerminalStep term (pre ++ input) n rest ↔ TerminalStep term input n rest := by
  rw [← invariant1_terminalOracle_iff, ← invariant1_terminalOracle_iff,
    prepend_oracle term pre input n bound]

private theorem prepend_bind (ctx : Inputs) (pre : List Char) (site : Nat) (name : String)
    (n : Nat) (r : Reply) (bound : n ≤ ctx.input.length) :
    bindResult { ctx with input := pre ++ ctx.input } site name n r = bindResult ctx site name n r := by
  cases r with
  | ok rest inner =>
    have same := invariant1_capture_window pre ctx.input [] n rest bound
    simp at same
    simp [bindResult, same]
  | fail | throwLabel => rfl

-- The entry position and every result use remaining lengths. Prepending
-- already consumed text thus needs no change to any stored position.
theorem invariant1_prepend_derivation {ctx body n env r} (pre : List Char)
    (h : Derives ctx body n env r) (bound : n ≤ ctx.input.length) :
    Derives { ctx with input := pre ++ ctx.input } body n env r := by
  induction h with
  | eps => exact .eps
  | terminalOk found step progress => exact .terminalOk found ((prepend_step _ _ _ _ _ bound).mpr step) progress
  | terminalFail bad =>
    apply Derives.terminalFail
    simpa only [prepend_step _ _ _ _ _ bound] using bad
  | predicateOk tested => exact .predicateOk tested
  | predicateFail tested => exact .predicateFail tested
  | callMissing absent => exact .callMissing absent
  | call entered _ ih => exact .call entered (ih bound)
  | seqCarryFail _ ih => exact .seqCarryFail (ih bound)
  | seqCarryThrow _ ih => exact .seqCarryThrow (ih bound)
  | seqOk left _ ih₁ ih₂ =>
    exact .seqOk (ih₁ bound) (ih₂ (Nat.le_trans (invariant1_success_remaining_le left _ _ rfl) bound))
  | altLeft _ ok ih => exact .altLeft (ih bound) ok
  | altRetry _ _ ih₁ ih₂ => exact .altRetry (ih₁ bound) (ih₂ bound)
  | ahead _ ih => exact .ahead (ih bound)
  | notAhead _ ih => exact .notAhead (ih bound)
  | star _ ih => exact .star (ih bound)
  | loopStop _ ih => exact .loopStop (ih bound)
  | loopThrow _ ih => exact .loopThrow (ih bound)
  | loopZero _ ih => exact .loopZero (ih bound)
  | loopMore _ progress _ ih₁ ih₂ => exact .loopMore (ih₁ bound) progress (ih₂ (by omega))
  | label _ ih => exact .label (ih bound)
  | capture _ ih => exact .capture (ih bound)
  | bind _ ih =>
    rw [← prepend_bind ctx pre _ _ _ _ bound]
    exact .bind (ih bound)
  | action _ ih => exact .action (ih bound)

set_option maxRecDepth 8192 in
theorem invariant1_actual_rule_prepend_iff (mode : Bool) (pre input : List Char)
    (rule n : Nat) (env : Env) (r : Reply) (bound : n ≤ input.length) :
    Derives (MetaExecution.context mode (pre ++ input))
        ((MetaExecution.context mode input).rules rule) n env r ↔
      Derives (MetaExecution.context mode input)
        ((MetaExecution.context mode input).rules rule) n env r := by
  let ctx := MetaExecution.context mode input
  have same : MetaExecution.context mode (pre ++ input) = {ctx with input := pre ++ ctx.input} := by
    cases mode <;> rfl
  have localInput : ctx.input = input := by cases mode <;> rfl
  rw [← localInput] at bound
  constructor
  · intro whole
    obtain ⟨fuel, value, observed⟩ := invariant1_actual_environment_total mode ctx
      (by cases mode <;> rfl) (n, rule) env
    have sub := invariant1_runFuel_sound observed
    have larger := invariant1_prepend_derivation pre sub bound
    rw [same] at whole
    obtain ⟨a, ha⟩ := invariant1_derivation_has_fuel larger
    obtain ⟨b, hb⟩ := invariant1_derivation_has_fuel whole
    have eq := invariant1_result_unique _ ha hb
    exact eq ▸ sub
  · intro sub
    rw [same]
    exact invariant1_prepend_derivation pre sub bound

end PegHs.EnvironmentEval
