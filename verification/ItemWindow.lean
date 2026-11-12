import WindowReads

namespace PegHs.MetaExecution
open EnvironmentEval

set_option maxRecDepth 8192

-- Each certificate evaluates the call itself, including its entry and exit hooks.
theorem invariant1_item_window (mode : Bool) (pre window extra : List Char)
    (fuel rest : Nat)
    (run : runFuel (context mode window) fuel (.call 1 1) window.length {} =
      some (.ok rest {}))
    (fits : readsFit (context mode window) fuel (.call 1 1) window.length {} = true) :
    Derives (context mode (pre ++ (window ++ extra))) (.call 1 1)
      (window.length + extra.length) {} (.ok (rest + extra.length) {}) := by
  let ctx := context mode window
  have input : ctx.input = window := by cases mode <;> rfl
  have h := invariant1_window_run run fits (by rw [show (context mode window).input = window from input]; exact Nat.le_refl _) extra
  have bound : window.length + extra.length ≤ (appendInput ctx extra).input.length := by
    simp [appendInput, input]
  have whole := invariant1_prepend_derivation pre h bound
  have same : {appendInput ctx extra with input := pre ++ (appendInput ctx extra).input} =
      context mode (pre ++ (window ++ extra)) := by cases mode <;> rfl
  rw [← same]
  exact whole

-- At the final item EOF may be observed. Only prefix replay is needed there.
theorem invariant1_final_item_window (mode : Bool) (pre window : List Char) (fuel : Nat)
    (run : runFuel (context mode window) fuel (.call 1 1) window.length {} =
      some (.ok 0 {})) :
    Derives (context mode (pre ++ window)) (.call 1 1) window.length {} (.ok 0 {}) := by
  let ctx := context mode window
  have input : ctx.input = window := by cases mode <;> rfl
  have whole := invariant1_prepend_derivation pre (invariant1_runFuel_sound run)
    (show window.length ≤ ctx.input.length by rw [input]; exact Nat.le_refl _)
  have same : {ctx with input := pre ++ ctx.input} = context mode (pre ++ window) := by
    cases mode <;> rfl
  rw [← same]
  exact whole

end PegHs.MetaExecution
