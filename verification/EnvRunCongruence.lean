import EnvProjection

namespace PegHs.EnvRunCongruence
open PegHs.EnvironmentEval PegHs.EnvProjection

def ReplyRel : Reply → Reply → Prop
  | .ok n left, .ok m right => n = m ∧ ObsEq left right
  | .fail, .fail => True
  | .throwLabel n name msg, .throwLabel m name' msg' =>
      n = m ∧ name = name' ∧ msg = msg'
  | _, _ => False

def OptionReplyRel : Option Reply → Option Reply → Prop
  | none, none => True
  | some left, some right => ReplyRel left right
  | _, _ => False

structure Compatible (ctx : Inputs) : Prop where
  predicate : ∀ site left right, ObsEq left right →
    (ctx.sites site).map (fun pair =>
      PegHs.SemanticPredicates.eval ctx.classes pair.1 (ctx.predicateEnv site left)) =
    (ctx.sites site).map (fun pair =>
      PegHs.SemanticPredicates.eval ctx.classes pair.1 (ctx.predicateEnv site right))
  enter : ∀ site left right, ObsEq left right →
    OptionObsEq (ctx.hooks.enterCall site left) (ctx.hooks.enterCall site right)
  bind : ∀ site name text left right, ObsEq left right →
    OptionObsEq (ctx.hooks.bindValue site name text left)
      (ctx.hooks.bindValue site name text right)
  leave : ∀ site callerLeft callerRight calleeLeft calleeRight,
    ObsEq callerLeft callerRight → ObsEq calleeLeft calleeRight →
    ObsEq (ctx.hooks.leaveCall site callerLeft calleeLeft)
      (ctx.hooks.leaveCall site callerRight calleeRight)

private theorem loop_env_congr {callerLeft callerRight nextLeft nextRight : Env}
    (callers : ObsEq callerLeft callerRight)
    (nexts : ObsEq nextLeft nextRight) :
    ObsEq {nextLeft with resultDepth := max callerLeft.resultDepth nextLeft.resultDepth}
      {nextRight with resultDepth := max callerRight.resultDepth nextRight.resultDepth} := by
  refine ⟨nexts.depth, ?_, nexts.capture, nexts.valueDepth, nexts.presence⟩
  simp [callers.resultDepth, nexts.resultDepth]

theorem runFuel_congr (ctx : Inputs) (compat : Compatible ctx)
    (fuel : Nat) (body : Body) (remaining : Nat)
    (left right : Env) (same : ObsEq left right) :
    OptionReplyRel (runFuel ctx fuel body remaining left)
      (runFuel ctx fuel body remaining right) := by
  induction fuel generalizing body remaining left right with
  | zero => simp [runFuel, OptionReplyRel]
  | succ fuel ih =>
      cases body with
      | eps => simp [runFuel, OptionReplyRel, ReplyRel,
          resultDepth_congr same 0]
      | terminal site =>
          cases ht : ctx.terms site with
          | none => simp [runFuel, ht, OptionReplyRel, ReplyRel]
          | some term =>
              cases hm : PegHs.ConcreteTerminal.terminalOracle term ctx.input remaining with
              | none => simp [runFuel, ht, hm, OptionReplyRel, ReplyRel]
              | some rest =>
                  by_cases progress : rest < remaining
                  · simp [runFuel, ht, hm, progress, OptionReplyRel, ReplyRel,
                      resultDepth_congr same 0]
                  · simp [runFuel, ht, hm, progress, OptionReplyRel, ReplyRel]
      | predicate site =>
          cases hs : ctx.sites site with
          | none => simp [runFuel, hs, OptionReplyRel, ReplyRel]
          | some pair =>
              rcases pair with ⟨kind, polarity⟩
              have hp := compat.predicate site left right same
              simp only [hs, Option.map_some] at hp
              have equalEval := Option.some.inj hp
              simp only [runFuel, hs, equalEval]
              split
              · exact ⟨rfl, resultDepth_congr same 0⟩
              · trivial
      | call site rule =>
          have entrance := compat.enter site left right same
          cases heLeft : ctx.hooks.enterCall site left with
          | none =>
              cases heRight : ctx.hooks.enterCall site right with
              | none => simp [runFuel, heLeft, heRight, OptionReplyRel, ReplyRel]
              | some callee =>
                  simp [OptionObsEq, heLeft, heRight] at entrance
          | some calleeLeft =>
              cases heRight : ctx.hooks.enterCall site right with
              | none => simp [OptionObsEq, heLeft, heRight] at entrance
              | some calleeRight =>
                  have calleeSame : ObsEq calleeLeft calleeRight := by
                    simpa [OptionObsEq, heLeft, heRight] using entrance
                  have child := ih (ctx.rules rule) remaining
                    calleeLeft calleeRight calleeSame
                  cases hLeft : runFuel ctx fuel (ctx.rules rule) remaining calleeLeft with
                  | none =>
                      cases hRight : runFuel ctx fuel (ctx.rules rule) remaining calleeRight with
                      | none => simp [runFuel, heLeft, heRight, hLeft, hRight, OptionReplyRel]
                      | some reply => simp [OptionReplyRel, hLeft, hRight] at child
                  | some replyLeft =>
                      cases hRight : runFuel ctx fuel (ctx.rules rule) remaining calleeRight with
                      | none => simp [OptionReplyRel, hLeft, hRight] at child
                      | some replyRight =>
                          have related : ReplyRel replyLeft replyRight := by
                            simpa [OptionReplyRel, hLeft, hRight] using child
                          cases replyLeft <;> cases replyRight <;>
                            simp [ReplyRel] at related ⊢
                          all_goals simp [runFuel, heLeft, heRight, hLeft, hRight,
                            OptionReplyRel, ReplyRel] at *
                          all_goals first
                            | exact related
                            | exact ⟨related.1,
                                compat.leave site left right _ _ same related.2⟩
      | seq a b =>
          have first := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at first
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at first
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using first
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  all_goals first
                    | simpa [runFuel, hLeft, hRight, related.1] using
                        ih b _ _ _ related.2
                    | simp [runFuel, hLeft, hRight, OptionReplyRel,
                        ReplyRel, related]
      | alt a b =>
          have first := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at first
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at first
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using first
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  all_goals first
                    | simpa [runFuel, hLeft, hRight] using
                        ih b remaining left right same
                    | simpa [runFuel, hLeft, hRight, OptionReplyRel,
                        ReplyRel] using related
      | ahead a =>
          have child := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at child
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at child
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using child
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  all_goals simp [runFuel, hLeft, hRight, OptionReplyRel,
                    ReplyRel, same]
      | notAhead a =>
          have child := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at child
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at child
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using child
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  all_goals simp [runFuel, hLeft, hRight, OptionReplyRel,
                    ReplyRel, same]
      | star a =>
          simpa [runFuel] using ih (.starLoop a) remaining
            {left with resultDepth := 0} {right with resultDepth := 0}
            (resultDepth_congr same 0)
      | starLoop a =>
          have first := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at first
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at first
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using first
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  all_goals first
                    | (simp only [runFuel, hLeft, hRight, related.1]
                       split
                       · exact ih (.starLoop a) _ _ _
                           (loop_env_congr same related.2)
                       · exact ⟨rfl, same⟩)
                    | simp [runFuel, hLeft, hRight, OptionReplyRel,
                        ReplyRel, related, same]
      | label name msg a =>
          have child := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at child
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at child
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using child
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  all_goals simp [runFuel, hLeft, hRight, OptionReplyRel,
                    ReplyRel, related]
      | capture a => simpa [runFuel] using ih a remaining left right same
      | bind site name a =>
          have first := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at first
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at first
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using first
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  case ok.ok restLeft envLeft restRight envRight =>
                    rcases related with ⟨rfl, envSame⟩
                    have bound := compat.bind site name
                      (matchedText ctx.input remaining restLeft)
                      envLeft envRight envSame
                    cases hbLeft : ctx.hooks.bindValue site name
                        (matchedText ctx.input remaining restLeft) envLeft with
                    | none =>
                        cases hbRight : ctx.hooks.bindValue site name
                            (matchedText ctx.input remaining restLeft) envRight with
                        | none => simp [runFuel, hLeft, hRight, hbLeft, hbRight,
                            OptionReplyRel, ReplyRel]
                        | some env => simp [OptionObsEq, hbLeft, hbRight] at bound
                    | some boundLeft =>
                        cases hbRight : ctx.hooks.bindValue site name
                            (matchedText ctx.input remaining restLeft) envRight with
                        | none => simp [OptionObsEq, hbLeft, hbRight] at bound
                        | some boundRight =>
                            have boundSame : ObsEq boundLeft boundRight := by
                              simpa [OptionObsEq, hbLeft, hbRight] using bound
                            simp [runFuel, hLeft, hRight, hbLeft, hbRight,
                              OptionReplyRel, ReplyRel, boundSame]
                  all_goals simp [runFuel, hLeft, hRight, OptionReplyRel,
                    ReplyRel, related]
      | action site a =>
          have first := ih a remaining left right same
          cases hLeft : runFuel ctx fuel a remaining left with
          | none =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [runFuel, hLeft, hRight, OptionReplyRel]
              | some reply => simp [OptionReplyRel, hLeft, hRight] at first
          | some replyLeft =>
              cases hRight : runFuel ctx fuel a remaining right with
              | none => simp [OptionReplyRel, hLeft, hRight] at first
              | some replyRight =>
                  have related : ReplyRel replyLeft replyRight := by
                    simpa [OptionReplyRel, hLeft, hRight] using first
                  cases replyLeft <;> cases replyRight <;>
                    simp [ReplyRel] at related ⊢
                  case ok.ok restLeft envLeft restRight envRight =>
                    rcases related with ⟨rfl, envSame⟩
                    have actionSame :
                        (ctx.actions site >>= DepthAction.eval envLeft) =
                          (ctx.actions site >>= DepthAction.eval envRight) := by
                      cases ha : ctx.actions site with
                      | none => rfl
                      | some action =>
                          simpa [ha] using depthAction_congr envSame action
                    cases haLeft : ctx.actions site >>= DepthAction.eval envLeft with
                    | none =>
                        simp [runFuel, hLeft, hRight, haLeft, ← actionSame,
                          OptionReplyRel, ReplyRel]
                    | some depth =>
                        simp [runFuel, hLeft, hRight, haLeft, ← actionSame,
                          OptionReplyRel, ReplyRel,
                          resultDepth_congr envSame depth]
                  all_goals simp [runFuel, hLeft, hRight, OptionReplyRel,
                    ReplyRel, related]

#print axioms runFuel_congr

end PegHs.EnvRunCongruence
