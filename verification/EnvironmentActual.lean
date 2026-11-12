import EnvironmentDerivation
import ConcreteTables

namespace PegHs.EnvironmentEval

theorem invariant1_peg_environment_erasure (n : Nat) :
    erase (MetaTerminal1.environmentBody n) = Meta1.rules n := by
  by_cases h : n < 59
  · exact MetaTerminal1.invariant1_environment_erasure ⟨n, h⟩
  · have bodyMiss : MetaTerminal1.environmentBodyTable[n]? = none :=
      Array.getElem?_eq_none (by change 59 ≤ n; omega)
    have callMiss : Meta1.table[n]? = none :=
      Array.getElem?_eq_none (by change 59 ≤ n; omega)
    simp [MetaTerminal1.environmentBody, bodyMiss, Meta1.rules, Meta1.entry,
      callMiss, erase]

theorem invariant1_syntax_environment_erasure (n : Nat) :
    erase (MetaTerminal2.environmentBody n) = Meta2.rules n := by
  by_cases h : n < 63
  · exact MetaTerminal2.invariant1_environment_erasure ⟨n, h⟩
  · have bodyMiss : MetaTerminal2.environmentBodyTable[n]? = none :=
      Array.getElem?_eq_none (by change 63 ≤ n; omega)
    have callMiss : Meta2.table[n]? = none :=
      Array.getElem?_eq_none (by change 63 ≤ n; omega)
    simp [MetaTerminal2.environmentBody, bodyMiss, Meta2.rules, Meta2.entry,
      callMiss, erase]

theorem invariant1_actual_environment_total (syntaxMode : Bool) (ctx : Inputs)
    (sameRules : ctx.rules = if syntaxMode then MetaTerminal2.environmentBody
      else MetaTerminal1.environmentBody)
    (state : Nat × Nat) (env : Env) :
    ∃ fuel r, runFuel ctx fuel (ctx.rules state.2) state.1 env = some r := by
  cases syntaxMode with
  | false =>
      have checked : ∀ rule, PegHs.CallOrder.validRule Meta1.known Meta1.rank rule
          (erase (ctx.rules rule)) = true := by
        intro rule
        simpa [sameRules, invariant1_peg_environment_erasure] using
          Meta1.invariant1_checked rule
      exact invariant1_rule_executable checked state env
  | true =>
      have checked : ∀ rule, PegHs.CallOrder.validRule Meta2.known Meta2.rank rule
          (erase (ctx.rules rule)) = true := by
        intro rule
        simpa [sameRules, invariant1_syntax_environment_erasure] using
          Meta2.invariant1_checked rule
      exact invariant1_rule_executable checked state env

#print axioms invariant1_actual_environment_total

end PegHs.EnvironmentEval
