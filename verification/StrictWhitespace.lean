import StrictComment
import StrictSpaceChar

namespace PegHs.MetaExecution
open EnvironmentEval
set_option maxRecDepth 8192

-- Neither whitespace alternative consumes the first character of a directive
-- or rule. Ordered choice retries the comment at the unchanged position.
theorem invariant1_strict_ws_stop (pre : List Char) (c : Char) (tail : List Char) (env : Env)
    (ordinary : GhcPredicates.space c = false) (notHash : c ≠ '#') :
    let input := pre ++ c :: tail
    Derives (context false input) translatedStrictWs (c :: tail).length env
      (.ok (c :: tail).length {env with resultDepth := 0}) := by
  let ctx := context false (pre ++ c :: tail)
  let cleared := {env with resultDepth := 0}
  have space := invariant1_strict_space_char pre c tail cleared
  rw [ordinary] at space
  have rejected : Derives ctx (ctx.rules 5) (c :: tail).length cleared .fail :=
    invariant1_runFuel_sound space
  have comment : Derives ctx (ctx.rules 6) (c :: tail).length cleared .fail :=
    invariant1_strict_comment_missing_hash pre (c :: tail) cleared (by simpa using notHash)
  have entered7 : ctx.hooks.enterCall 7 cleared = some cleared := rfl
  have entered8 : ctx.hooks.enterCall 8 cleared = some cleared := rfl
  have left : Derives ctx (.call 7 5) (c :: tail).length cleared .fail :=
    .call entered7 rejected
  have right : Derives ctx (.call 8 6) (c :: tail).length cleared .fail :=
    .call entered8 comment
  exact .star (.loopStop (.altRetry left right))

theorem invariant1_strict_ws_eof (input : List Char) (env : Env) :
    Derives (context false input) translatedStrictWs 0 env (.ok 0 {env with resultDepth := 0}) := by
  let ctx := context false input
  let cleared := {env with resultDepth := 0}
  have rejected : Derives ctx (ctx.rules 5) 0 cleared .fail :=
    invariant1_runFuel_sound (invariant1_strict_space_char_eof input cleared)
  have comment := invariant1_strict_comment_missing_hash input [] cleared (by decide)
  simp only [List.append_nil, List.length_nil] at comment
  have entered7 : ctx.hooks.enterCall 7 cleared = some cleared := rfl
  have entered8 : ctx.hooks.enterCall 8 cleared = some cleared := rfl
  have left : Derives ctx (.call 7 5) 0 cleared .fail := .call entered7 rejected
  have right : Derives ctx (.call 8 6) 0 cleared .fail :=
    Derives.call (rule := 6) entered8 comment
  exact .star (.loopStop (.altRetry left right))

#print axioms invariant1_strict_ws_eof
#print axioms invariant1_strict_ws_stop
end PegHs.MetaExecution
