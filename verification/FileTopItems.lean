import MetaExecution

namespace PegHs.MetaExecution
open EnvironmentEval

-- A certificate is a finite list of successful TopItem calls followed by the
-- failing call that stops the star. The environments retain semantic depth.
inductive TopItems (ctx : Inputs) : Nat → Env → Nat → Env → Prop where
  | stop {n env} : Derives ctx (.call 1 1) n env .fail → TopItems ctx n env n env
  | next {n env mid inner rest final} :
      Derives ctx (.call 1 1) n env (.ok mid inner) → mid < n →
      TopItems ctx mid
        { inner with resultDepth := max env.resultDepth inner.resultDepth } rest final →
      TopItems ctx n env rest final

theorem invariant1_top_items_to_loop {ctx : Inputs} {n rest : Nat} {env final : Env}
    (items : TopItems ctx n env rest final) :
    Derives ctx (.starLoop (.call 1 1)) n env (.ok rest final) := by
  induction items with
  | stop failed => exact .loopStop failed
  | next succeeded progress _ ih => exact .loopMore succeeded progress ih

theorem invariant1_file_from_top_items (mode : Bool) (input : List Char)
    {afterWs : Nat} {wsEnv finalEnv : Env}
    (ws : Derives (context mode input) (.call 0 4) input.length {}
      (.ok afterWs wsEnv))
    (items : TopItems (context mode input) afterWs
      { wsEnv with resultDepth := 0 } 0 finalEnv)
    (endOfFile : Derives (context mode input) (.terminal 0) 0 finalEnv .fail) :
    FileResult mode input (.ok 0 finalEnv) := by
  let ctx := context mode input
  have shape : ctx.rules (startRule mode) =
      .seq (.call 0 4) (.seq (.star (.call 1 1))
        (.label "top" (some "expected a rule, a directive or %{ ... }%")
          (.notAhead (.terminal 0)))) := by
    cases mode <;> rfl
  change Derives ctx (ctx.rules (startRule mode)) input.length {} (.ok 0 finalEnv)
  rw [shape]
  exact .seqOk ws (.seqOk (.star (invariant1_top_items_to_loop items))
    (.label (.notAhead endOfFile)))

#print axioms invariant1_file_from_top_items

end PegHs.MetaExecution
