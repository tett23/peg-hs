import WindowReads

namespace PegHs.EnvironmentEval

open ConcreteTerminal

-- The first component records every terminal read, including abandoned
-- alternatives and lookahead. The second is the parser reply from that same
-- traversal. A child result is inspected once at each parent node.
def fastWindow (ctx : Inputs) : Nat → Body → Nat → Env → Bool × Option Reply
  | 0, _, _, _ => (false, none)
  | fuel + 1, body, remaining, env =>
    match body with
    | .eps => (true, some (.ok remaining {env with resultDepth := 0}))
    | .terminal site =>
      let term := ctx.terms site
      let fit := term.all (fun t => readWidth t ≤ remaining)
      let reply := match term with
        | none => some .fail
        | some t => match terminalOracle t ctx.input remaining with
          | none => some .fail
          | some rest => if rest < remaining then
              some (.ok rest {env with resultDepth := 0}) else some .fail
      (fit, reply)
    | .predicate site =>
      let reply := match ctx.sites site with
        | none => some .fail
        | some (kind, polarity) =>
          if PegHs.SemanticPredicates.eval ctx.classes kind (ctx.predicateEnv site env) == polarity
          then some (.ok remaining {env with resultDepth := 0}) else some .fail
      (true, reply)
    | .call site rule =>
      match ctx.hooks.enterCall site env with
      | none => (true, some .fail)
      | some callee =>
        let (fit, reply) := fastWindow ctx fuel (ctx.rules rule) remaining callee
        (fit, reply.map (callResult ctx site env))
    | .seq a b =>
      let (fitA, replyA) := fastWindow ctx fuel a remaining env
      match replyA with
      | some (.ok rest next) =>
        let (fitB, replyB) := fastWindow ctx fuel b rest next
        (fitA && fitB, replyB)
      | _ => (fitA, replyA)
    | .alt a b =>
      let (fitA, replyA) := fastWindow ctx fuel a remaining env
      match replyA with
      | some .fail =>
        let (fitB, replyB) := fastWindow ctx fuel b remaining env
        (fitA && fitB, replyB)
      | _ => (fitA, replyA)
    | .ahead a =>
      let (fit, reply) := fastWindow ctx fuel a remaining env
      (fit, reply.map (aheadResult remaining env))
    | .notAhead a =>
      let (fit, reply) := fastWindow ctx fuel a remaining env
      (fit, reply.map (notAheadResult remaining env))
    | .star a => fastWindow ctx fuel (.starLoop a) remaining {env with resultDepth := 0}
    | .starLoop a =>
      let (fitA, replyA) := fastWindow ctx fuel a remaining env
      match replyA with
      | some .fail => (fitA, some (.ok remaining env))
      | some (.throwLabel pos name msg) => (fitA, some (.throwLabel pos name msg))
      | some (.ok rest next) =>
        if rest < remaining then
          let (fitB, replyB) := fastWindow ctx fuel (.starLoop a) rest
            {next with resultDepth := max env.resultDepth next.resultDepth}
          (fitA && fitB, replyB)
        else (fitA, some (.ok remaining env))
      | none => (fitA, none)
    | .label name msg a =>
      let (fit, reply) := fastWindow ctx fuel a remaining env
      (fit, reply.map (labelResult remaining name msg))
    | .capture a => fastWindow ctx fuel a remaining env
    | .bind site name a =>
      let (fit, reply) := fastWindow ctx fuel a remaining env
      (fit, reply.map (bindResult ctx site name remaining))
    | .action site a =>
      let (fit, reply) := fastWindow ctx fuel a remaining env
      (fit, reply.map (actionResult ctx site))

theorem fastWindow_eq_pair (ctx : Inputs) :
    ∀ fuel body remaining env,
      fastWindow ctx fuel body remaining env =
        (readsFit ctx fuel body remaining env, runFuel ctx fuel body remaining env) := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro body remaining env
    cases body with
    | eps => rfl
    | terminal site =>
      cases ht : ctx.terms site with
      | none => simp [fastWindow, readsFit, runFuel, ht]
      | some term =>
        cases ho : terminalOracle term ctx.input remaining with
        | none => simp [fastWindow, readsFit, runFuel, ht, ho]
        | some rest => simp [fastWindow, readsFit, runFuel, ht, ho]
    | predicate site =>
      cases hs : ctx.sites site with
      | none => simp [fastWindow, readsFit, runFuel, hs]
      | some pair => cases pair with
        | mk kind polarity => simp [fastWindow, readsFit, runFuel, hs]
    | call site rule =>
      cases hc : ctx.hooks.enterCall site env with
      | none => simp [fastWindow, readsFit, runFuel, hc]
      | some callee =>
        cases hr : runFuel ctx fuel (ctx.rules rule) remaining callee with
        | none => simp [fastWindow, readsFit, runFuel, ih, hc, hr]
        | some reply =>
          cases reply <;> simp [fastWindow, readsFit, runFuel, ih, hc, hr, callResult]
    | seq a b =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply => cases reply <;> simp [fastWindow, readsFit, runFuel, ih, hr]
    | alt a b =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply => cases reply <;> simp [fastWindow, readsFit, runFuel, ih, hr]
    | ahead a =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply => cases reply <;> simp [fastWindow, readsFit, runFuel, ih, hr, aheadResult]
    | notAhead a =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply => cases reply <;> simp [fastWindow, readsFit, runFuel, ih, hr, notAheadResult]
    | star a => simp [fastWindow, readsFit, runFuel, ih]
    | starLoop a =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply =>
        cases reply with
        | fail => simp [fastWindow, readsFit, runFuel, ih, hr]
        | throwLabel pos name msg => simp [fastWindow, readsFit, runFuel, ih, hr]
        | ok rest next =>
          by_cases progress : rest < remaining
          · simp [fastWindow, readsFit, runFuel, ih, hr, progress]
          · simp [fastWindow, readsFit, runFuel, ih, hr, progress]
    | label name msg a =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply => cases reply <;> simp [fastWindow, readsFit, runFuel, ih, hr, labelResult]
    | capture a => simp [fastWindow, readsFit, runFuel, ih]
    | bind site name a =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply =>
        cases reply with
        | fail => simp [fastWindow, readsFit, runFuel, ih, hr, bindResult]
        | throwLabel pos label msg =>
          simp [fastWindow, readsFit, runFuel, ih, hr, bindResult]
        | ok rest inner =>
          cases hb : ctx.hooks.bindValue site name (matchedText ctx.input remaining rest) inner <;>
            simp [fastWindow, readsFit, runFuel, ih, hr, bindResult, hb]
    | action site a =>
      cases hr : runFuel ctx fuel a remaining env with
      | none => simp [fastWindow, readsFit, runFuel, ih, hr]
      | some reply =>
        cases reply with
        | fail => simp [fastWindow, readsFit, runFuel, ih, hr, actionResult]
        | throwLabel pos label msg =>
          simp [fastWindow, readsFit, runFuel, ih, hr, actionResult]
        | ok rest inner =>
          cases ha : ctx.actions site >>= DepthAction.eval inner <;>
            simp [fastWindow, readsFit, runFuel, ih, hr, actionResult, ha]

def windowCheck (ctx : Inputs) (fuel : Nat) (body : Body) (remaining : Nat)
    (env : Env) (expected : Reply) : Bool :=
  let (fits, reply) := fastWindow ctx fuel body remaining env
  fits && decide (reply = some expected)

theorem windowCheck_iff (ctx : Inputs) (fuel : Nat) (body : Body) (remaining : Nat)
    (env : Env) (expected : Reply) :
    windowCheck ctx fuel body remaining env expected = true ↔
      readsFit ctx fuel body remaining env = true ∧
      runFuel ctx fuel body remaining env = some expected := by
  simp [windowCheck, fastWindow_eq_pair]

#print axioms PegHs.EnvironmentEval.fastWindow_eq_pair
#print axioms PegHs.EnvironmentEval.windowCheck_iff

end PegHs.EnvironmentEval
