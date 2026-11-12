import MemoTrace

open PegHs.MemoRecognition PegHs.MemoTrace

private def body : Nat → Entry Nat := fun k =>
  { result := .ok (k + 1) k, failure := k,
    deps := fun n => n == k, errors := [] }

-- Invariant 1: a miss followed by a hit uses one evaluation.
example : (runMemo true body [3, 3] initial).evaluations = 1 := by decide
example : (runMemo true body [3, 3] initial).results = [.ok 4 3, .ok 4 3] := by decide

-- Invariant 1: equal offsets with distinct arguments require distinct entries.
private def argBody : Nat × Nat → Entry Nat := fun key => body (key.1 + key.2)
example : (runMemo true argBody [(3, 1), (3, 2), (3, 1)] initial).evaluations = 2 := by decide

-- Invariant 1: recognition and replayed failure positions agree with no memo.
example : (runMemo true body [3, 4, 3] initial).results =
    (runMemo false body [3, 4, 3] initial).results := by decide
example : (runMemo true body [3, 4, 3] initial).state.failure =
    (runMemo false body [3, 4, 3] initial).state.failure := by decide

-- A body that changes between insertion and lookup does not satisfy the
-- cache invariant; the trace theorem deliberately does not claim that case.
private def changed : Nat → Entry Nat := fun k =>
  { result := .fail, failure := k,
    deps := fun n => n == k, errors := [] }
example : ¬ CacheInvariant changed [(3, body 3)] := by
  intro inv
  have same := inv 3 (body 3) (by rfl)
  have results := congrArg Entry.result same
  cases results
