import PrefixReplay
import FileTopItems

namespace PegHs.MetaExecution
open EnvironmentEval

set_option maxRecDepth 8192 in
theorem invariant1_top_item_at_end (mode : Bool) (input : List Char) (env : Env) :
    Derives (context mode input) (.call 1 1) 0 env .fail := by
  have emptyCall : runFuel (context mode []) 128 (.call 1 1) 0 env = some .fail := by
    cases mode <;> rfl
  have lifted := invariant1_prepend_derivation input (invariant1_runFuel_sound emptyCall)
    (Nat.zero_le _)
  have eq : {context mode [] with input := input ++ (context mode []).input} =
      context mode input := by
    have emptyInput : (context mode []).input = [] := by cases mode <;> rfl
    rw [emptyInput, List.append_nil]
    cases mode <;> rfl
  rw [eq] at lifted
  exact lifted

theorem invariant1_eof_terminal (ctx : Inputs) (env : Env) :
    Derives ctx (.terminal 0) 0 env .fail := by
  apply Derives.terminalFail
  cases found : ctx.terms 0 with
  | none => exact Or.inl rfl
  | some term => exact Or.inr ⟨term, rfl, by simp⟩

theorem invariant1_top_items_end (mode : Bool) (input : List Char) (env : Env) :
    TopItems (context mode input) 0 env 0 env :=
  .stop (invariant1_top_item_at_end mode input env)

end PegHs.MetaExecution
