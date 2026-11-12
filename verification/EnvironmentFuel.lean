import EnvironmentEval

namespace PegHs.EnvironmentEval

theorem invariant1_fuel_step (ctx : Inputs) {fuel : Nat} {b : Body} {n : Nat} {env : Env}
    {r : Reply} (observed : runFuel ctx fuel b n env = some r) :
    runFuel ctx (fuel + 1) b n env = some r := by
  induction fuel generalizing b n env r with
  | zero => simp [runFuel] at observed
  | succ fuel ih =>
    unfold runFuel at observed ⊢
    cases b with
    | eps | terminal _ | predicate _ => exact observed
    | capture _ | star _ => exact ih observed
    | call site rule =>
      cases he : ctx.hooks.enterCall site env with
      | none => simpa only [he] using observed
      | some callee =>
        cases hr : runFuel ctx fuel (ctx.rules rule) n callee with
        | none => simp [he, hr] at observed
        | some rr => simpa only [he, hr, ih hr] using observed
    | ahead a | notAhead a | label _ _ a | bind _ _ a | action _ a =>
      cases hr : runFuel ctx fuel a n env with
      | none => simp [hr] at observed
      | some rr => simpa only [hr, ih hr] using observed
    | seq a b | alt a b | starLoop a =>
      cases hr : runFuel ctx fuel a n env with
      | none => simp [hr] at observed
      | some rr =>
        have larger := ih hr
        cases rr <;> simp only [hr, larger] at observed ⊢ <;>
          first | exact observed | exact ih observed | skip
        all_goals split at observed <;> rename_i h <;> simp only [h, ↓reduceIte] <;>
          first | exact observed | exact ih observed

theorem invariant1_fuel_stable (ctx : Inputs) {fuel limit : Nat} (budget : fuel ≤ limit)
    {b : Body} {n : Nat} {env : Env} {r : Reply}
    (observed : runFuel ctx fuel b n env = some r) :
    runFuel ctx limit b n env = some r := by
  induction budget with
  | refl => exact observed
  | step _ ih => exact invariant1_fuel_step ctx ih

theorem invariant1_result_unique (ctx : Inputs) {a b n : Nat} {body : Body} {env : Env}
    {x y : Reply} (left : runFuel ctx a body n env = some x)
    (right : runFuel ctx b body n env = some y) : x = y := by
  have hx := invariant1_fuel_stable ctx (Nat.le_max_left a b) left
  have hy := invariant1_fuel_stable ctx (Nat.le_max_right a b) right
  exact Option.some.inj (hx.symm.trans hy)

end PegHs.EnvironmentEval
