import EnvironmentDerivation
import TerminalCursor
import CaptureWindow

namespace PegHs.EnvironmentEval
open ConcreteTerminal

def Reply.shift (extra : Nat) : Reply → Reply
  | .ok n e => .ok (n + extra) e
  | .throwLabel pos name msg => .throwLabel (pos + extra) name msg
  | .fail => .fail

def appendInput (ctx : Inputs) (extra : List Char) :=
  { ctx with input := ctx.input ++ extra }

theorem shift_label (n : Nat) (label : String) (msg : Option String) (r : Reply) (k : Nat) :
    labelResult (n + k) label msg (r.shift k) = (labelResult n label msg r).shift k := by
  cases r <;> rfl

theorem shift_lookahead (n : Nat) (env : Env) (r : Reply) (k : Nat) :
    aheadResult (n + k) env (r.shift k) = (aheadResult n env r).shift k ∧
    notAheadResult (n + k) env (r.shift k) = (notAheadResult n env r).shift k := by
  cases r <;> exact ⟨rfl, rfl⟩

theorem shift_call (ctx : Inputs) (extra : List Char) (site : Nat) (env : Env) (r : Reply) :
    callResult (appendInput ctx extra) site env (r.shift extra.length) =
      (callResult ctx site env r).shift extra.length := by
  cases r <;> rfl

theorem shift_action (ctx : Inputs) (extra : List Char) (site : Nat) (r : Reply) :
    actionResult (appendInput ctx extra) site (r.shift extra.length) =
      (actionResult ctx site r).shift extra.length := by
  cases r with
  | ok rest env =>
    simp only [actionResult, Reply.shift, appendInput]
    split <;> rfl
  | fail | throwLabel => rfl

theorem shift_binding (ctx : Inputs) (extra : List Char) (site : Nat) (name : String)
    (n : Nat) (within : n ≤ ctx.input.length) (r : Reply) :
    bindResult (appendInput ctx extra) site name (n + extra.length) (r.shift extra.length) =
      (bindResult ctx site name n r).shift extra.length := by
  cases r with
  | ok rest env =>
    have h := invariant1_capture_window [] ctx.input extra n rest within
    simp only [List.nil_append] at h
    simp only [Reply.shift, bindResult, appendInput, h]
    split <;> rfl
  | fail | throwLabel => rfl

theorem shift_terminal_step (term : Terminal) (input extra : List Char) (n : Nat)
    (within : n ≤ input.length) (enough : readWidth term ≤ n) (fullRest : Nat) :
    TerminalStep term (input ++ extra) (n + extra.length) fullRest ↔
      ∃ rest, TerminalStep term input n rest ∧ fullRest = rest + extra.length := by
  simp only [← invariant1_terminalOracle_iff, invariant1_oracle_append_at term input extra n within enough]
  cases terminalOracle term input n <;> simp [eq_comm]

theorem shift_terminal_leaf {ctx : Inputs} {site n : Nat} {env : Env} {r : Reply}
    (extra : List Char) (within : n ≤ ctx.input.length)
    (enough : ∀ term, ctx.terms site = some term → readWidth term ≤ n)
    (localStep : Derives ctx (.terminal site) n env r) :
    Derives (appendInput ctx extra) (.terminal site) (n + extra.length) env
      (r.shift extra.length) := by
  cases localStep with
  | terminalOk found step progress =>
    exact .terminalOk found ((shift_terminal_step _ _ _ _ within (enough _ found) _).mpr
      ⟨_, step, rfl⟩) (by omega)
  | terminalFail bad =>
    apply Derives.terminalFail
    rcases bad with missing | ⟨term, found, failed⟩
    · exact Or.inl missing
    · refine Or.inr ⟨term, found, ?_⟩
      rintro ⟨rest, step, progress⟩
      obtain ⟨j, original, rfl⟩ := (shift_terminal_step _ _ _ _ within (enough _ found) _).mp step
      exact failed ⟨j, original, by omega⟩

end PegHs.EnvironmentEval
