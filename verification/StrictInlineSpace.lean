import SelfHostedFileProof
import Lexical
import TerminalCursor

namespace PegHs.MetaExecution
open EnvironmentEval ConcreteTerminal
set_option maxRecDepth 8192

private def horizontal := [(' ', ' '), ('\t', '\t')]

private theorem class_agrees (c : Char) : classHas horizontal c = PegVerification.isInlineSpace c := by
  have singleton (x : Char) :
      (decide (x.toNat ≤ c.toNat) && decide (c.toNat ≤ x.toNat)) = (c == x) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨fun ⟨lo, hi⟩ => Char.toNat_inj.mp (Nat.le_antisymm hi lo), fun h => h ▸ ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
  change ((_ && _ || (_ && _ || false)) : Bool) = _
  simp only [Bool.or_false, singleton, PegVerification.isInlineSpace]

private theorem inline_loop (input pre xs : List Char) (env : Env)
    (cursor : input = pre ++ xs) (zero : env.resultDepth = 0) :
    Derives (context false input) (.starLoop (.terminal 5)) xs.length env
      (.ok (xs.dropWhile PegVerification.isInlineSpace).length env) := by
  let ctx := context false input
  have term : ctx.terms 5 = some (.cls horizontal) := rfl
  have src : ctx.input = input := rfl
  induction xs generalizing pre with
  | nil =>
    have oracle := invariant1_oracle_at_cursor (term := .cls horizontal) (src.trans cursor) (remaining := 0) rfl
    have failure : runFuel ctx 1 (.terminal 5) 0 env = some .fail := by
      simp [runFuel, term, oracle, matchTerm]
    exact .loopStop (invariant1_runFuel_sound failure)
  | cons c cs ih =>
    have oracle := invariant1_oracle_at_cursor (term := .cls horizontal) (src.trans cursor)
      (remaining := cs.length + 1) rfl
    simp only [matchTerm, class_agrees] at oracle
    cases h : PegVerification.isInlineSpace c with
    | false =>
      have failure : runFuel ctx 1 (.terminal 5) (cs.length + 1) env = some .fail := by
        simp [runFuel, term, oracle, h]
      simpa [List.dropWhile, h] using Derives.loopStop (invariant1_runFuel_sound failure)
    | true =>
      have reset : {env with resultDepth := 0} = env := by cases env; simp_all
      have step : runFuel ctx 1 (.terminal 5) (cs.length + 1) env = some (.ok cs.length env) := by
        simp [runFuel, term, oracle, h, reset]
      simp only [List.dropWhile_cons_of_pos h]
      apply Derives.loopMore (invariant1_runFuel_sound step) (Nat.lt_succ_self _)
      simpa using ih (pre ++ [c]) (by simpa using cursor)

theorem invariant1_strict_inline_space (pre xs : List Char) (env : Env) :
    Derives (context false (pre ++ xs)) translatedStrictInlineSp xs.length env
      (.ok (xs.dropWhile PegVerification.isInlineSpace).length {env with resultDepth := 0}) :=
  .star (inline_loop _ pre xs _ rfl rfl)

theorem invariant1_inline_space_rule (input : List Char) :
    translatedStrictInlineSp = (context false input).rules 7 := rfl

theorem invariant1_inline_space_lexical_result (pre xs : List Char) (env : Env) :
    ∃ suffix, PegVerification.run PegVerification.inlineSp xs = .ok suffix ∧
      Derives (context false (pre ++ xs)) translatedStrictInlineSp xs.length env
        (.ok suffix.length {env with resultDepth := 0}) :=
  ⟨_, PegVerification.invariant1_inlineSp xs, invariant1_strict_inline_space pre xs env⟩

#print axioms invariant1_strict_inline_space
end PegHs.MetaExecution
