import InitialWhitespace

namespace PegHs.MetaExecution
open EnvironmentEval

set_option maxRecDepth 8192 in
theorem invariant1_initial_whitespace_call (mode : Bool) (extra : List Char) :
    Derives (context mode (wsWindow ++ extra)) (.call 0 4)
      (wsWindow ++ extra).length {} (.ok (1 + extra.length) {}) := by
  let ctx := context mode (wsWindow ++ extra)
  have body := invariant1_actual_rule_window mode [] wsWindow extra 4 512
    wsWindow.length {} (.ok 1 {}) (Nat.le_refl _) (invariant1_initial_whitespace_window mode)
    (invariant1_initial_whitespace_reads mode)
  have entered : ctx.hooks.enterCall 0 {} = some {} := by cases mode <;> rfl
  simp only [List.nil_append] at body
  have called := Derives.call (ctx := ctx) (site := 0) (rule := 4)
    (n := wsWindow.length + extra.length) (env := {}) (callee := {})
    (r := .ok (1 + extra.length) {}) entered body
  rw [List.length_append]
  cases mode <;> exact called

#print axioms invariant1_initial_whitespace_call
end PegHs.MetaExecution
