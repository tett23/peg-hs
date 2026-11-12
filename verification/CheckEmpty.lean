import FileTrees

-- Each certificate is specialized to the operator tree extracted from that file.
#check Grammar1.invariant1_topItem_empty
#check Grammar2.invariant1_topItem_empty
#check Grammar1.invariant1_ws_empty
#check Grammar2.invariant1_ws_empty
#check Grammar1.invariant1_file_empty
#check Grammar2.invariant1_file_empty
#check Grammar1.invariant1_file
#check Grammar2.invariant1_file

open PegVerification

-- Even if every unexpanded expression throws, recognizing an empty file
-- never reaches one of those expressions.
private def throwing (_ : Nat) : Expr := .label "unexpected" (.predicate false)

example : run (Grammar1.start (Grammar1.ruleWs throwing) (Grammar1.ruleTopItem throwing)) [] = .ok [] :=
  Grammar1.invariant1_file_empty throwing
example : run (Grammar2.start (Grammar2.ruleWs throwing) (Grammar2.ruleTopItem throwing)) [] = .ok [] :=
  Grammar2.invariant1_file_empty throwing

#check Grammar1.invariant1_file_whitespace
#check Grammar2.invariant1_file_whitespace
