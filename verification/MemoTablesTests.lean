import MemoTables

open PegHs.MemoRecognition PegHs.MemoTables

private def entry (n : Nat) : Entry Nat :=
  { result := .ok n n, failure := n, deps := fun _ => false, errors := [] }

-- Invariant 1: ordinary memo insertion replaces only its own offset.
example : lookupMemo (insertMemo emptyMemo 3 (entry 1)) 3 = some (entry 1) := by rfl
example : lookupMemo (insertMemo (insertMemo emptyMemo 3 (entry 1)) 3 (entry 2)) 3 =
    some (entry 2) := by rfl
example : lookupMemo (insertMemo (insertMemo emptyMemo 4 (entry 1)) 3 (entry 2)) 4 =
    some (entry 1) := by rfl

-- Invariant 1: argument memo insertion distinguishes both parts of the key.
example : lookupArg (insertArg emptyArg 3 1 (entry 1)) 3 1 = some (entry 1) := by rfl
example : lookupArg (insertArg (insertArg emptyArg 3 1 (entry 1)) 3 2 (entry 2)) 3 1 =
    some (entry 1) := by rfl
example : lookupArg (insertArg (insertArg emptyArg 3 1 (entry 1)) 4 1 (entry 2)) 3 1 =
    some (entry 1) := by rfl
