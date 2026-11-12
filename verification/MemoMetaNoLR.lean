import CallTables

namespace PegHs.MemoMetaNoLR
open PegHs.CallOrder

-- A left-recursion seed requires a cycle of calls at the same input offset.
-- The extracted call tables prove a stronger property: every nested call,
-- including calls after consumption, follows a well-founded relation.
private theorem no_cycle (rules : Nat → Body)
    (wf : WellFounded (Nested rules)) (state : Nat × Nat) :
    ¬ Relation.TransGen (Nested rules) state state := by
  let relation := Relation.TransGen (Nested rules)
  apply (wf.transGen).induction state
  intro current ih cycle
  exact ih current cycle cycle

theorem peg_no_left_recursion_seed (remaining rule : Nat) :
    ¬ Relation.TransGen (Nested Meta1.rules) (remaining, rule) (remaining, rule) :=
  no_cycle Meta1.rules Meta1.invariant1_recursive_calls_terminate (remaining, rule)

theorem syntax_no_left_recursion_seed (remaining rule : Nat) :
    ¬ Relation.TransGen (Nested Meta2.rules) (remaining, rule) (remaining, rule) :=
  no_cycle Meta2.rules Meta2.invariant1_recursive_calls_terminate (remaining, rule)

#print axioms peg_no_left_recursion_seed
#print axioms syntax_no_left_recursion_seed

end PegHs.MemoMetaNoLR
