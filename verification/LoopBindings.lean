import ScopedEnv

/-!
The bindings of a repetition (premise R7 of verification/README.md, the
second difference).

The model passes one environment through a repetition: `runFuel` starts
each iteration of `.starLoop a` from the environment the previous iteration
left. The generated Haskell does not: `PegRt.many p` and `PegRt.skipMany p`
run the same action `p` for every iteration, so the variables that one
iteration of `p` binds are out of scope in the next one and after the loop.
`SelfHostedRuntime.exec` and `SelfHostedMemo.execM` follow the generated
code: every iteration starts from the environment the loop started with, and
only the result depth (the value depth of the list) is carried.

This module shows that the two meanings return the same replies when no
repetition body binds a name. Such a body leaves the environment it started
from, apart from the result depth (`invariant1_bindfree_frame`), so the
environment that the model hands to the next iteration is the one the loop
started with (`invariant1_loop_env_same`). Every rule of the strict
metagrammar is such a body (`invariant1_meta_loops_bind_nothing`, checked by
`decide` on the extracted rule table).

Theorems:
- `invariant1_bindfree_frame`: a body that binds no name returns, on
  success, its starting environment with only the result depth changed, when
  a call keeps the caller's environment apart from the result depth.
- `invariant1_loop_env_same`: under the same conditions, the environment the
  model passes to the next iteration of a repetition equals the one with the
  loop's starting environment and the carried result depth.
- `invariant1_meta_loops_bind_nothing`: the strict metagrammar meets the
  conditions (`Frame`).

Premises: none besides those of MetaExecution.lean.
-/

set_option linter.unusedSimpArgs false
namespace PegHs.LoopBindings
open PegHs.EnvironmentEval PegHs.MetaExecution PegHs.ScopedEnv

/-- Every repetition in a body has a body that binds no name. -/
def loopsBindNothing : Body → Bool
  | .star a | .starLoop a => (binders a).isEmpty && loopsBindNothing a
  | .seq a b | .alt a b => loopsBindNothing a && loopsBindNothing b
  | .ahead a | .notAhead a | .label _ _ a | .capture a | .bind _ _ a | .action _ a =>
    loopsBindNothing a
  | _ => true

/-- The conditions under which the two meanings of a repetition agree: a
call keeps the caller's environment apart from the result depth, and no
repetition body of a rule binds a name. -/
structure Frame (ctx : Inputs) : Prop where
  leave : ∀ site caller callee,
    ctx.hooks.leaveCall site caller callee = { caller with resultDepth := callee.resultDepth }
  rules : ∀ r, loopsBindNothing (ctx.rules r) = true

theorem env_eta (env : Env) : { env with resultDepth := env.resultDepth } = env := by
  cases env; rfl

/-- A body that binds no name returns its starting environment with only the
result depth changed. -/
theorem invariant1_bindfree_frame (ctx : Inputs)
    (leave : ∀ site caller callee,
      ctx.hooks.leaveCall site caller callee = { caller with resultDepth := callee.resultDepth }) :
    ∀ fuel body rem env rest next, binders body = [] →
      runFuel ctx fuel body rem env = some (.ok rest next) →
      next = { env with resultDepth := next.resultDepth } := by
  intro fuel
  induction fuel with
  | zero => intro body rem env rest next _ h; cases h
  | succ fuel ih =>
    intro body rem env rest next nb hr
    cases body with
    | eps =>
      simp only [runFuel, Option.some.injEq, Reply.ok.injEq] at hr
      obtain ⟨-, rfl⟩ := hr; rfl
    | terminal site =>
      simp only [runFuel] at hr
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · simp only [Option.some.injEq, Reply.ok.injEq] at hr
            obtain ⟨-, rfl⟩ := hr; rfl
          · cases hr
    | predicate site =>
      simp only [runFuel] at hr
      split at hr
      · cases hr
      · split at hr
        · simp only [Option.some.injEq, Reply.ok.injEq] at hr
          obtain ⟨-, rfl⟩ := hr; rfl
        · cases hr
    | call site rule =>
      simp only [runFuel] at hr
      split at hr
      · cases hr
      · split at hr <;> simp only [Option.some.injEq, Reply.ok.injEq, reduceCtorEq] at hr
        obtain ⟨-, rfl⟩ := hr
        rw [leave]
    | seq a b =>
      simp only [binders, List.append_eq_nil_iff] at nb
      simp only [runFuel] at hr
      cases ha : runFuel ctx fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        cases ra with
        | ok r1 n1 =>
          simp only at hr
          rw [ih b r1 n1 rest next nb.2 hr, ih a rem env r1 n1 nb.1 ha]
        | fail => cases hr
        | throwLabel _ _ _ => cases hr
    | alt a b =>
      simp only [binders, List.append_eq_nil_iff] at nb
      simp only [runFuel] at hr
      cases ha : runFuel ctx fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        cases ra with
        | ok r1 n1 =>
          simp only [Option.some.injEq, Reply.ok.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ih a rem env r1 n1 nb.1 ha
        | fail => exact ih b rem env rest next nb.2 hr
        | throwLabel _ _ _ => cases hr
    | ahead a =>
      simp only [runFuel] at hr
      split at hr <;> simp only [Option.some.injEq, Reply.ok.injEq, reduceCtorEq] at hr
      obtain ⟨-, rfl⟩ := hr; exact (env_eta _).symm
    | notAhead a =>
      simp only [runFuel] at hr
      split at hr <;> simp only [Option.some.injEq, Reply.ok.injEq, reduceCtorEq] at hr
      obtain ⟨-, rfl⟩ := hr; exact (env_eta _).symm
    | star a =>
      simp only [binders] at nb
      simp only [runFuel] at hr
      have h := ih (.starLoop a) rem _ rest next (by simpa [binders] using nb) hr
      rw [h]
    | starLoop a =>
      simp only [binders] at nb
      simp only [runFuel] at hr
      cases ha : runFuel ctx fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        cases ra with
        | ok r1 n1 =>
          simp only at hr
          split at hr
          · have h := ih (.starLoop a) r1 _ rest next (by simpa [binders] using nb) hr
            rw [h, ih a rem env r1 n1 nb ha]
          · simp only [Option.some.injEq, Reply.ok.injEq] at hr
            obtain ⟨-, rfl⟩ := hr; exact (env_eta _).symm
        | fail =>
          simp only [Option.some.injEq, Reply.ok.injEq] at hr
          obtain ⟨-, rfl⟩ := hr; exact (env_eta _).symm
        | throwLabel _ _ _ => cases hr
    | label name msg a =>
      simp only [binders] at nb
      simp only [runFuel] at hr
      split at hr
      · cases hr
      · exact ih a rem env rest next nb hr
    | capture a =>
      simp only [binders] at nb
      simp only [runFuel] at hr
      exact ih a rem env rest next nb hr
    | bind site name a => simp [binders] at nb
    | action site a =>
      simp only [binders] at nb
      simp only [runFuel] at hr
      cases ha : runFuel ctx fuel a rem env with
      | none => rw [ha] at hr; cases hr
      | some ra =>
        rw [ha] at hr
        cases ra with
        | ok r1 n1 =>
          simp only at hr
          split at hr
          · simp only [Option.some.injEq, Reply.ok.injEq] at hr
            obtain ⟨-, rfl⟩ := hr
            rw [ih a rem env r1 n1 nb ha]
          · cases hr
        | fail => cases hr
        | throwLabel _ _ _ => cases hr

/-- The environment that the model hands to the next iteration of a
repetition whose body binds no name is the loop's starting environment with
the carried result depth: the environment that `many` and `skipMany` of the
generated code start the next iteration from. -/
theorem invariant1_loop_env_same (ctx : Inputs)
    (leave : ∀ site caller callee,
      ctx.hooks.leaveCall site caller callee = { caller with resultDepth := callee.resultDepth })
    {fuel : Nat} {a : Body} {rem rest : Nat} {env next : Env} (nb : (binders a).isEmpty = true)
    (hr : runFuel ctx fuel a rem env = some (.ok rest next)) :
    { next with resultDepth := max env.resultDepth next.resultDepth } =
      { env with resultDepth := max env.resultDepth next.resultDepth } := by
  rw [invariant1_bindfree_frame ctx leave fuel a rem env rest next (List.isEmpty_iff.mp nb) hr]

section Bodies
theorem loops_seq {a b : Body} (h : loopsBindNothing (.seq a b) = true) :
    loopsBindNothing a = true ∧ loopsBindNothing b = true := by
  simpa [loopsBindNothing] using h
theorem loops_alt {a b : Body} (h : loopsBindNothing (.alt a b) = true) :
    loopsBindNothing a = true ∧ loopsBindNothing b = true := by
  simpa [loopsBindNothing] using h
theorem loops_star {a : Body} (h : loopsBindNothing (.star a) = true) :
    loopsBindNothing (.starLoop a) = true := h
theorem loops_starLoop {a : Body} (h : loopsBindNothing (.starLoop a) = true) :
    (binders a).isEmpty = true ∧ loopsBindNothing a = true := by
  simpa [loopsBindNothing] using h
theorem loops_one {a : Body} :
    (loopsBindNothing (.ahead a) = loopsBindNothing a) ∧
    (loopsBindNothing (.notAhead a) = loopsBindNothing a) ∧
    (∀ n m, loopsBindNothing (.label n m a) = loopsBindNothing a) ∧
    (loopsBindNothing (.capture a) = loopsBindNothing a) ∧
    (∀ s n, loopsBindNothing (.bind s n a) = loopsBindNothing a) ∧
    (∀ s, loopsBindNothing (.action s a) = loopsBindNothing a) :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
end Bodies

/-! ## The strict metagrammar -/

def metaLoopsBindNothing : Bool :=
  (List.range MetaTerminal1.environmentBodyTable.size).all fun r =>
    loopsBindNothing (MetaTerminal1.environmentBody r)

theorem metaLoopsBindNothing_eq : metaLoopsBindNothing = true := by decide +kernel

/-- The strict metagrammar meets the conditions: its calls keep the caller's
environment apart from the result depth, and no repetition body of its rules
binds a name. -/
theorem invariant1_meta_loops_bind_nothing (input : List Char) : Frame (context false input) := by
  refine ⟨fun _ _ _ => rfl, fun r => ?_⟩
  show loopsBindNothing (MetaTerminal1.environmentBody r) = true
  by_cases lt : r < MetaTerminal1.environmentBodyTable.size
  · have all := metaLoopsBindNothing_eq
    simp only [metaLoopsBindNothing, List.all_eq_true, List.mem_range] at all
    exact all r lt
  · have past : MetaTerminal1.environmentBody r = .terminal 0 := by
      simp [MetaTerminal1.environmentBody, Array.getElem?_eq_none (Nat.le_of_not_lt lt)]
    rw [past]; rfl

#print axioms invariant1_bindfree_frame
#print axioms invariant1_loop_env_same
#print axioms invariant1_meta_loops_bind_nothing

end PegHs.LoopBindings
